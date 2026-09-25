//! Report options parsed from the command line: which sections to build and
//! how to sort the class table.

use clap::ValueEnum;

use crate::error::{Error, Result};

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum Section {
    Heap,
    Suspects,
    Biggest,
    Classes,
    Collections,
    Threads,
    Locals,
    Loaders,
    Strings,
    Arrays,
    Boxed,
    References,
    Garbage,
    System,
    Direct,
    Baseline,
}

impl Section {
    pub fn parse(name: &str) -> Result<Section> {
        let name = name.trim().to_lowercase();
        Section::from_str(&name, false).map_err(|_| {
            let values = Section::value_variants().iter().filter_map(ValueEnum::to_possible_value);
            let names: Vec<String> = values.map(|value| value.get_name().to_string()).collect();
            Error::Usage(format!("`{name}` is not a section; the sections are {}", names.join(", ")))
        })
    }
}

/// The set of sections a run prints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sections(u32);

impl Sections {
    pub fn all() -> Sections {
        Sections((1 << Section::value_variants().len()) - 1)
    }

    pub fn none() -> Sections {
        Sections(0)
    }

    /// `--only` picks a list; `--skip` removes one; both are comma-separated.
    pub fn from_args(only: Option<&str>, skip: Option<&str>) -> Result<Sections> {
        let list = |text: &str| -> Result<Sections> {
            let mut sections = Sections::none();
            for part in text.split(',').filter(|part| !part.trim().is_empty()) {
                sections = sections.with(Section::parse(part)?);
            }
            Ok(sections)
        };
        let mut out = only.map_or(Ok(Sections::all()), list)?;
        if let Some(text) = skip {
            out.0 &= !list(text)?.0;
        }
        Ok(out)
    }

    pub fn with(self, section: Section) -> Sections {
        Sections(self.0 | 1 << section as u32)
    }

    pub fn has(self, section: Section) -> bool {
        self.0 & 1 << section as u32 != 0
    }

    /// Whether the run needs the array-hashing read.
    pub fn needs_hashes(self) -> bool {
        self.has(Section::Strings) || self.has(Section::Arrays)
    }
}

/// Order of the class table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum Sort {
    Retained,
    Shallow,
    Instances,
    Name,
}
