//! `--shell`: after the report, commands on stdin drill into the same
//! analysis. Only the strings a view prints are read from the file again.

use std::io::{self, BufRead, Write};

use super::Session;
use super::options::{Section, Sections, Sort};
use super::pattern::Pattern;
use super::report::View;
use crate::error::{Error, Result};

const HELP: &str = "\
  sections   heap suspects biggest classes packages collections threads locals loaders
             strings arrays boxed references garbage system direct baseline
  focus      class PATTERN | object ID|suspect:N|top:N|Class.FIELD[.f][N] | find TEXT | where C.F=V
  settings   top N | depth N | paths N | min PCT | suspect PCT | sort retained|shallow|instances|name
             json on|off | full-paths on|off
  quit
";

pub fn run(session: &mut Session) -> Result<()> {
    let stdin = io::stdin();
    let mut out = io::stdout();
    println!("\n  shell: `help` lists the commands, `quit` leaves");
    loop {
        print!("heap> ");
        let _ = out.flush();
        let mut line = String::new();
        if stdin.lock().read_line(&mut line)? == 0 {
            break;
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        match session.command(line) {
            Ok(Some(text)) => {
                print!("{text}");
                let _ = out.flush();
            }
            Ok(None) => break,
            Err(e) => eprintln!("  {e}"),
        }
    }
    Ok(())
}

impl Session<'_> {
    /// Run one shell command; None means leave.
    pub fn command(&mut self, line: &str) -> Result<Option<String>> {
        let (word, rest) = line.split_once(char::is_whitespace).unwrap_or((line, ""));
        let rest = rest.trim();
        let number =
            |what: &str| rest.parse::<usize>().map_err(|_| Error::Usage(format!("{what} takes a number")));
        let percent =
            |what: &str| rest.parse::<f64>().map_err(|_| Error::Usage(format!("{what} takes a percentage")));
        let on_off = || match rest {
            "on" | "yes" | "true" => Ok(true),
            "off" | "no" | "false" => Ok(false),
            _ => Err(Error::Usage(format!("{word} takes on or off"))),
        };
        match word {
            "help" | "?" => return Ok(Some(HELP.to_string())),
            "quit" | "exit" | "q" => return Ok(None),
            "top" => self.view.top = number("top")?,
            "depth" => self.view.depth = number("depth")?,
            "paths" => self.view.paths = number("paths")?.max(1),
            "min" => self.view.min = percent("min")?,
            "suspect" => self.view.suspect = percent("suspect")?,
            "sort" => {
                self.view.sort = match rest {
                    "retained" => Sort::Retained,
                    "shallow" => Sort::Shallow,
                    "instances" => Sort::Instances,
                    "name" => Sort::Name,
                    _ => return Err(Error::Usage("sort takes retained, shallow, instances or name".into())),
                }
            }
            "json" => self.json = on_off()?,
            "full-paths" => self.view.full_paths = on_off()?,
            _ => return self.view_command(word, rest).map(Some),
        }
        Ok(Some(String::new()))
    }

    /// Show a section or a focused view with the current settings.
    fn view_command(&mut self, word: &str, rest: &str) -> Result<String> {
        let mut view = View { class: None, object: None, find: None, filter: None, ..self.view.clone() };
        match word {
            "class" if !rest.is_empty() => view.class = Some(Pattern::parse(rest)),
            "object" if !rest.is_empty() => view.object = Some(rest.to_string()),
            "find" if !rest.is_empty() => view.find = Some(rest.to_string()),
            "where" if !rest.is_empty() => view.filter = Some(rest.to_string()),
            "class" | "object" | "find" | "where" => {
                return Err(Error::Usage(format!("{word} needs an argument")));
            }
            "packages" => {
                view.by_package = true;
                view.sections = Sections::none().with(Section::Classes);
            }
            _ => {
                let section = Section::parse(word)?;
                view.sections = Sections::none().with(section);
                view.by_package = false;
            }
        }
        if view.find.is_some() || view.filter.is_some() {
            self.search(view.find.as_deref(), view.filter.as_deref())?;
        }
        self.show(&view)
    }
}
