//! Source positions as TLC reports them: a per-file line index and the
//! `line L, col C to line L2, col C2 of module M` ranges built on it.
//!
//! The end of a range is the last byte of a span, optionally moved back over
//! trailing blanks and comments (`EndTrim`); a trimmed end is always a
//! character boundary. The callers disagree on that rule and on the module
//! name; both are explicit parameters here.

use std::fmt;

use tlx_front::ast::Span;

use crate::resolve::SourceFile;

/// Where a source file was loaded from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleOrigin {
    /// A user file (root module, `-I` search path, or `TLX_CLASSPATH`).
    User,
    /// A bundled TLA+ standard module (`<stdlib>/...`).
    Stdlib,
    /// A bundled CommunityModules module (`<community>/...`).
    Community,
}

/// Byte offsets of the line starts of one file.
#[derive(Clone, Debug)]
pub struct LineIndex {
    starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(src: &str) -> LineIndex {
        let mut starts = vec![0u32];
        starts.extend(src.bytes().enumerate().filter(|&(_, b)| b == b'\n').map(|(i, _)| i as u32 + 1));
        LineIndex { starts }
    }

    /// The 1-based line and column of the byte at offset `at` (an offset
    /// equal to the length of the file counts as one past the last byte).
    pub fn line_col(&self, at: usize) -> (usize, usize) {
        let line = self.starts.partition_point(|&s| s as usize <= at);
        (line, at - self.starts[line - 1] as usize + 1)
    }
}

/// Where the end of a range is taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EndTrim {
    /// The last byte of the span.
    Raw,
    /// The last byte that is not blank.
    Blank,
    /// The last byte that is neither blank nor in a comment (a junction
    /// list's span may extend over the comments after it; TLC's location
    /// ends at its last token).
    BlankAndComments,
}

/// A source range as TLC reports it (1-based lines and columns; the end is
/// the last character of the range, see `EndTrim`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRange {
    pub begin: (usize, usize),
    pub end: (usize, usize),
    pub module: String,
}

impl SourceRange {
    /// The range of `sp` in `file`, named after `module`.
    pub fn of(file: &SourceFile, sp: Span, trim: EndTrim, module: String) -> SourceRange {
        let src = &*file.src;
        let start = sp.start as usize;
        let last = (sp.end as usize).saturating_sub(1).max(start);
        let last = match trim {
            EndTrim::Raw => last.min(src.len()),
            // The end is a position in the source and so must be a character
            // boundary: `α` is two bytes and either of them can be the last
            // byte of a span (or of the trailing comment it is trimmed to).
            EndTrim::Blank => char_start(src, trim_blank(src, start, last.min(src.len().saturating_sub(1)))),
            EndTrim::BlankAndComments => char_start(src, last_code_byte(src, start, last.min(src.len().saturating_sub(1)))),
        };
        SourceRange { begin: (sp.line as usize, sp.col as usize), end: file.lines().line_col(last), module }
    }

    /// The location of the unknown action (TLC's `Action.UNKNOWN`).
    pub fn builtins() -> SourceRange {
        SourceRange { begin: (0, 0), end: (0, 0), module: "--TLA+ BUILTINS--".into() }
    }

    /// The fields of TLC's location record, in the order TLC lists them.
    pub fn fields(&self) -> [(&'static str, Field<'_>); 5] {
        [
            ("beginLine", Field::Int(self.begin.0 as i64)),
            ("beginColumn", Field::Int(self.begin.1 as i64)),
            ("endLine", Field::Int(self.end.0 as i64)),
            ("endColumn", Field::Int(self.end.1 as i64)),
            ("module", Field::Str(&self.module)),
        ]
    }
}

/// A field of a location record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Field<'a> {
    Int(i64),
    Str(&'a str),
}

impl fmt::Display for SourceRange {
    /// `line L, col C to line L2, col C2 of module M`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, col {} to line {}, col {} of module {}", self.begin.0, self.begin.1, self.end.0, self.end.1, self.module)
    }
}

/// `line L, col C of module M`: the start of `sp` only.
pub fn begin_text(sp: Span, module: &str) -> String {
    format!("line {}, col {} of module {module}", sp.line, sp.col)
}

/// The largest character boundary at or before `at` (never past the end).
fn char_start(src: &str, at: usize) -> usize {
    let mut at = at.min(src.len());
    while !src.is_char_boundary(at) {
        at -= 1;
    }
    at
}

/// The last byte of `src[start..=last]` that is not blank.
fn trim_blank(src: &str, start: usize, mut last: usize) -> usize {
    while last > start && src.as_bytes()[last].is_ascii_whitespace() {
        last -= 1;
    }
    last
}

/// The last byte of `src[start..=last]` that is neither blank nor in a
/// comment.
fn last_code_byte(src: &str, start: usize, mut last: usize) -> usize {
    let b = src.as_bytes();
    loop {
        last = trim_blank(src, start, last);
        // A block comment `(* ... *)` (nested) ending here.
        if last > start + 1 && b[last] == b')' && b[last - 1] == b'*' {
            let (mut depth, mut i) = (0usize, last + 1);
            while i >= start + 2 {
                if b[i - 2] == b'*' && b[i - 1] == b')' {
                    depth += 1;
                    i -= 2;
                } else if b[i - 2] == b'(' && b[i - 1] == b'*' {
                    depth -= 1;
                    i -= 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i -= 1;
                }
            }
            if depth != 0 || i <= start {
                return last;
            }
            last = i - 1;
            continue;
        }
        // A line comment `\* ...` this line ends with (outside strings).
        let line_start = b[..last].iter().rposition(|&c| c == b'\n').map_or(0, |i| i + 1).max(start);
        let (mut in_str, mut i, mut comment) = (false, line_start, None);
        while i < last {
            match b[i] {
                b'\\' if in_str => i += 1,
                b'"' => in_str = !in_str,
                b'\\' if b[i + 1] == b'*' => {
                    comment = Some(i);
                    break;
                }
                _ => {}
            }
            i += 1;
        }
        match comment {
            Some(c) if c > start => last = c - 1,
            _ => return last,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::sync::Arc;
    use tlx_front::ast::FileId;

    fn file(src: &str) -> SourceFile {
        SourceFile::new(PathBuf::from("M.tla"), Arc::from(src))
    }

    /// The span of `needle` in `src`, with its begin line and column.
    fn span(src: &str, needle: &str) -> Span {
        let start = src.find(needle).unwrap();
        let line_col = LineIndex::new(src).line_col(start);
        Span { file: FileId(0), start: start as u32, end: (start + needle.len()) as u32, line: line_col.0 as u32, col: line_col.1 as u32 }
    }

    /// The counting the index replaced: newlines before `at`.
    fn scan(src: &str, at: usize) -> (usize, usize) {
        let before = &src[..at];
        (before.matches('\n').count() + 1, at - before.rfind('\n').map_or(0, |i| i + 1) + 1)
    }

    #[test]
    fn line_index_agrees_with_scanning() {
        for src in ["", "a", "a\n", "\n\nab\ncd", "x\r\ny\n\nz\n"] {
            let idx = LineIndex::new(src);
            for at in 0..=src.len() {
                assert_eq!(idx.line_col(at), scan(src, at), "{src:?} at {at}");
            }
        }
    }

    #[test]
    fn end_trim_rules() {
        let src = "A ==\n  /\\ x = 1  \n  /\\ y = 2 (* c *) \\* tail\n\nB == 3";
        let f = file(src);
        // A span that covers the whole junction list and what follows it.
        let sp = span(src, "A ==\n  /\\ x = 1  \n  /\\ y = 2 (* c *) \\* tail\n\n");
        let range = |t| SourceRange::of(&f, sp, t, "M".into());
        assert_eq!(range(EndTrim::Raw).end, (4, 1));
        assert_eq!(range(EndTrim::Blank).end, (3, 26));
        assert_eq!(range(EndTrim::BlankAndComments).end, (3, 10));
        assert_eq!(range(EndTrim::Raw).to_string(), "line 1, col 1 to line 4, col 1 of module M");
    }

    #[test]
    fn empty_span_at_end_of_file() {
        let src = "ab\n";
        let f = file(src);
        let sp = Span { file: FileId(0), start: 3, end: 3, line: 2, col: 1 };
        assert_eq!(SourceRange::of(&f, sp, EndTrim::Raw, "M".into()).end, (2, 1));
        assert_eq!(SourceRange::of(&f, sp, EndTrim::Blank, "M".into()).end, (1, 3));
    }

    #[test]
    fn end_trim_at_a_multibyte_final_character() {
        // A span's last byte can be the second byte of a multibyte character
        // (`α`), and a trailing comment can end in one: the trimmed end must
        // still be a character boundary, on the same convention as ASCII (the
        // end is the last character of the range). `Blank` only trims blanks,
        // `BlankAndComments` also drops a trailing comment.
        let cases = [
            ("", (1, 1), (1, 1)),
            ("x", (1, 1), (1, 1)),
            ("x \\* ascii", (1, 10), (1, 1)),
            ("α", (1, 1), (1, 1)),
            ("x \\* α", (1, 6), (1, 1)),
            ("x\nα", (2, 1), (2, 1)),
            ("α\nx \\* ä", (2, 6), (2, 1)),
        ];
        for (src, blank, comments) in cases {
            let f = file(src);
            let end = |t| SourceRange::of(&f, span(src, src), t, "M".into()).end;
            assert_eq!(end(EndTrim::Blank), blank, "{src:?} Blank");
            assert_eq!(end(EndTrim::BlankAndComments), comments, "{src:?} BlankAndComments");
        }
    }

    #[test]
    fn builtins_record_fields() {
        let r = SourceRange::builtins();
        let f = r.fields();
        assert_eq!(f[0], ("beginLine", Field::Int(0)));
        assert_eq!(f[4], ("module", Field::Str("--TLA+ BUILTINS--")));
    }
}
