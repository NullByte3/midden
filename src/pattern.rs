//! Class-name patterns for `--class`, `--exclude` and `--where`: a substring
//! by default, a glob when it has `*` or `?`, an exact name with a leading
//! `=`. All case-insensitive.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern {
    kind: Kind,
    text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Substring,
    Glob,
    Exact,
}

impl Pattern {
    pub fn parse(text: &str) -> Pattern {
        let (kind, text) = match text.strip_prefix('=') {
            Some(rest) => (Kind::Exact, rest),
            None if text.contains(['*', '?']) => (Kind::Glob, text),
            None => (Kind::Substring, text),
        };
        Pattern { kind, text: text.to_lowercase() }
    }

    pub fn matches(&self, name: &str) -> bool {
        let name = name.to_lowercase();
        match self.kind {
            Kind::Substring => name.contains(&self.text),
            Kind::Exact => name == self.text || short(&name) == self.text,
            Kind::Glob => glob(self.text.as_bytes(), name.as_bytes()),
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }
}

/// `java.util.HashMap$Node` → `HashMap$Node`, keeping array brackets.
pub fn short(name: &str) -> &str {
    let base = name.trim_end_matches("[]");
    let cut = base.rfind('.').map_or(0, |i| i + 1);
    &name[cut..]
}

/// Anchored glob match with `*` and `?`, iterative with one backtrack point.
pub fn glob(pattern: &[u8], text: &[u8]) -> bool {
    let (mut pattern_pos, mut text_pos) = (0, 0);
    let mut star: Option<(usize, usize)> = None;
    while text_pos < text.len() {
        match pattern.get(pattern_pos) {
            Some(b'*') => {
                star = Some((pattern_pos, text_pos));
                pattern_pos += 1;
            }
            Some(&c) if c == b'?' || c == text[text_pos] => {
                pattern_pos += 1;
                text_pos += 1;
            }
            _ => match star {
                Some((star_pos, star_text_pos)) => {
                    pattern_pos = star_pos + 1;
                    text_pos = star_text_pos + 1;
                    star = Some((star_pos, star_text_pos + 1));
                }
                None => return false,
            },
        }
    }
    pattern[pattern_pos..].iter().all(|&c| c == b'*')
}
