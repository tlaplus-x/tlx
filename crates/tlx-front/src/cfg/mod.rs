//! TLC model configuration (`.cfg`) parser.
//!
//! Mirrors the semantics of TLC's `tlc2.tool.impl.ModelConfig`:
//!
//! - The file is a sequence of sections, each introduced by a keyword and
//!   continuing until the next keyword (or end of file).
//! - `INIT`, `NEXT`, `SPECIFICATION`, `SYMMETRY`, `VIEW`, `ALIAS` take exactly
//!   one name and may appear at most once. `CHECK_DEADLOCK` takes `TRUE` or
//!   `FALSE` and may appear at most once.
//! - `INVARIANT(S)`, `PROPERTY`/`PROPERTIES`, `CONSTRAINT(S)`,
//!   `ACTION_CONSTRAINT(S)`, `POSTCONDITION(S)`, `_POSSIBLE` take a
//!   whitespace-separated list of names and may be repeated (lists are
//!   concatenated). Like TLC, commas are *not* accepted as separators.
//! - `CONSTANT(S)` takes a list of bindings: `c = value`, `c = [M] value`,
//!   `F <- G`, `F <- [M] G`. Values are integers, strings, `TRUE`/`FALSE`,
//!   model values (bare identifiers) and finite sets `{v1, ..., vn}`. The
//!   names of a substitution may be operator symbols (`++ <- PlusPlus`,
//!   `Plus <- +`), recorded by their canonical names (`\circ` as `\o`).
//! - A `.tla` file as configuration: its `---- CONFIG Name ----` section
//!   (`config_section`).
//! - Comments are TLA+ comments: `\*` to end of line and nestable `(* ... *)`.
//!
//! Extensions beyond TLC (all strictly additive; TLC rejects these inputs):
//! negative integers (`N = -1`), tuples (`<<1, 2>>`), and the operator
//! override form `F(_, _) <- G` (recorded as a substitution for `F`).
//!
//! Deviations from TLC:
//! - String escapes (`\"`, `\\`, `\n`, `\t`, `\r`, `\f`) are decoded; TLC keeps
//!   the raw text between the quotes.
//! - Integers are parsed as `i64`; TLC rejects literals outside the `i32` range.
//! - TLC's internal keywords `_PERIODIC`, `_RL_REWARD` are parsed and ignored.
//! - Names after a keyword must be identifiers (TLC accepts any token there and
//!   fails later when looking the name up).

mod lex;

use crate::ast::Span;
use crate::Diagnostic;
use lex::{lex, Tok, Token};

/// A constant value as written in a `.cfg` file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgValue {
    Int(i64),
    Str(String),
    Bool(bool),
    /// A bare identifier on the right-hand side denotes a model value.
    ModelValue(String),
    Set(Vec<CfgValue>),
    Tuple(Vec<CfgValue>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstBinding {
    /// `N = 3`, `Procs = {p1, p2}`, `a = a` (model value).
    /// `module` is set for the module-scoped form `c = [M] v`.
    Value { name: String, value: CfgValue, module: Option<String> },
    /// `F <- G` (replace constant/operator F by the definition G).
    /// `module` is set for the module-scoped form `F <- [M] G`.
    Subst { name: String, op: String, module: Option<String> },
    /// `F(a1, ..., an) = v`: the value of operator constant F at the given
    /// arguments (TLC's OpRcdValue; F is undefined at any others).
    OpValue { name: String, args: Vec<CfgValue>, value: CfgValue },
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Config {
    pub constants: Vec<ConstBinding>,
    pub init: Option<String>,
    pub next: Option<String>,
    pub specification: Option<String>,
    pub invariants: Vec<String>,
    pub properties: Vec<String>,
    pub constraints: Vec<String>,
    pub action_constraints: Vec<String>,
    pub symmetry: Option<String>,
    pub view: Option<String>,
    pub alias: Option<String>,
    pub postconditions: Vec<String>,
    /// `_POSSIBLE`: predicates that must hold in some state (state level) or
    /// step (action level) of the model.
    pub possible: Vec<String>,
    pub check_deadlock: Option<bool>,
}

/// Effective unqualified (`module: None`) binding for a `.cfg` `CONSTANT` entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectiveConst<'a> {
    Value(&'a CfgValue),
    Subst(&'a str),
}

impl Config {
    /// Resolve the effective unqualified (`module: None`) binding for `name`,
    /// matching TLC / runtime `bind_cfg` precedence: `<-` substitutions apply
    /// after `=` values, and within each kind the last entry in `.cfg` wins.
    ///
    /// Returns `None` if `name` has no unqualified binding or is bound by an
    /// operator table (`F(a) = v`) without a later substitution.
    pub fn effective_constant(&self, name: &str) -> Option<EffectiveConst<'_>> {
        let mut effective = None;
        for b in &self.constants {
            match b {
                ConstBinding::Value { name: n, value, module: None } if n == name => {
                    effective = Some(EffectiveConst::Value(value));
                }
                ConstBinding::OpValue { name: n, .. } if n == name => {
                    effective = None;
                }
                _ => {}
            }
        }
        for b in &self.constants {
            if let ConstBinding::Subst { name: n, op, module: None } = b {
                if n == name {
                    effective = Some(EffectiveConst::Subst(op.as_str()));
                }
            }
        }
        effective
    }

    /// The effective unqualified `name = value` binding (last wins), returning
    /// `None` if overridden by an unqualified `<-` substitution or `OpValue`.
    pub fn last_constant_value(&self, name: &str) -> Option<&CfgValue> {
        match self.effective_constant(name) {
            Some(EffectiveConst::Value(v)) => Some(v),
            _ => None,
        }
    }

    /// The effective unqualified `name <- op` substitution (last wins).
    pub fn last_constant_subst(&self, name: &str) -> Option<&str> {
        match self.effective_constant(name) {
            Some(EffectiveConst::Subst(op)) => Some(op),
            _ => None,
        }
    }
}

/// The configuration embedded in a `.tla` file as TLC reads it
/// (`util.MonolithSpecExtractor.config`): the lines after the first line
/// `---- CONFIG name ----` (four or more dashes on each side) up to the next
/// line starting with `====`; empty if there is no such section.
pub fn config_section(src: &str, name: &str) -> String {
    let is_start = |line: &str| {
        let Some(rest) = line.strip_prefix("----") else { return false };
        let rest = rest.trim_start_matches('-').trim_start();
        let Some(rest) = rest.strip_prefix("CONFIG") else { return false };
        if !rest.starts_with(char::is_whitespace) {
            return false;
        }
        let Some(rest) = rest.trim_start().strip_prefix(name) else { return false };
        let dashes = rest.trim_start();
        dashes.len() >= 4 && dashes.bytes().all(|b| b == b'-')
    };
    let mut lines = src.lines();
    if !lines.any(is_start) {
        return String::new();
    }
    let body: Vec<&str> = lines.take_while(|l| !l.starts_with("====")).collect();
    body.join("\n").trim().to_string()
}

pub fn parse_cfg(src: &str) -> Result<Config, Vec<Diagnostic>> {
    let (tokens, mut diags) = lex(src);
    let mut parser = Parser { tokens, pos: 0, diags: Vec::new(), cfg: Config::default(), seen: Vec::new() };
    parser.parse_file();
    diags.append(&mut parser.diags);
    if diags.is_empty() {
        Ok(parser.cfg)
    } else {
        diags.sort_by_key(|d| d.span.start);
        Err(diags)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Keyword {
    Constant,
    Init,
    Next,
    Specification,
    Invariant,
    Property,
    Constraint,
    ActionConstraint,
    Symmetry,
    View,
    Alias,
    PostCondition,
    CheckDeadlock,
    /// TLC-internal `_PERIODIC`, `_RL_REWARD` (single name) - ignored.
    InternalSingle,
    /// TLC's `_POSSIBLE` (list of names).
    Possible,
}

impl Keyword {
    fn from_str(s: &str) -> Option<Keyword> {
        Some(match s {
            "CONSTANT" | "CONSTANTS" => Keyword::Constant,
            "INIT" => Keyword::Init,
            "NEXT" => Keyword::Next,
            "SPECIFICATION" => Keyword::Specification,
            "INVARIANT" | "INVARIANTS" => Keyword::Invariant,
            "PROPERTY" | "PROPERTIES" => Keyword::Property,
            "CONSTRAINT" | "CONSTRAINTS" => Keyword::Constraint,
            "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => Keyword::ActionConstraint,
            "SYMMETRY" => Keyword::Symmetry,
            "VIEW" => Keyword::View,
            "ALIAS" => Keyword::Alias,
            "POSTCONDITION" | "POSTCONDITIONS" => Keyword::PostCondition,
            "CHECK_DEADLOCK" => Keyword::CheckDeadlock,
            "_PERIODIC" | "_RL_REWARD" => Keyword::InternalSingle,
            "_POSSIBLE" => Keyword::Possible,
            _ => return None,
        })
    }
}

/// Marker for a syntax error that has already been reported; the caller
/// recovers by skipping to the next keyword.
struct Reported;

type PResult<T> = Result<T, Reported>;

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    diags: Vec<Diagnostic>,
    cfg: Config,
    /// First occurrence of each single-valued keyword, for duplicate errors.
    seen: Vec<(String, Span)>,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn bump(&mut self) -> Token {
        let t = self.tokens[self.pos].clone();
        if t.tok != Tok::Eof {
            self.pos += 1;
        }
        t
    }

    fn error<T>(&mut self, span: Span, message: impl Into<String>) -> PResult<T> {
        // An invalid character at the cursor was already reported by the
        // lexer; don't pile a parse error on top of it.
        if self.peek().tok != Tok::Error {
            self.diags.push(Diagnostic { span, message: message.into() });
        }
        Err(Reported)
    }

    /// The keyword at the cursor, if any.
    fn at_keyword(&self) -> Option<Keyword> {
        match &self.peek().tok {
            Tok::Ident(s) => Keyword::from_str(s),
            _ => None,
        }
    }

    /// True at a keyword or end of file, i.e. at the end of a section.
    fn at_section_end(&self) -> bool {
        self.peek().tok == Tok::Eof || self.at_keyword().is_some()
    }

    fn skip_to_section_end(&mut self) {
        while !self.at_section_end() {
            self.bump();
        }
    }

    fn eat_sym(&mut self, sym: &'static str) -> bool {
        if self.peek().tok == Tok::Sym(sym) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect_sym(&mut self, sym: &'static str, context: &str) -> PResult<Span> {
        let t = self.peek().clone();
        if t.tok == Tok::Sym(sym) {
            self.bump();
            Ok(t.span)
        } else {
            self.error(t.span, format!("expected `{sym}` {context}, found {}", t.describe()))
        }
    }

    /// Expects a non-keyword identifier.
    fn expect_ident(&mut self, what: &str) -> PResult<(String, Span)> {
        let t = self.peek().clone();
        match &t.tok {
            Tok::Ident(s) if Keyword::from_str(s).is_none() => {
                self.bump();
                Ok((s.clone(), t.span))
            }
            _ => self.error(t.span, format!("expected {what}, found {}", t.describe())),
        }
    }

    /// An identifier or an operator symbol (by its canonical name).
    fn expect_name(&mut self, what: &str) -> PResult<(String, Span)> {
        let t = self.peek().clone();
        let sym = match &t.tok {
            Tok::Op(sym) => Some(sym.as_str()),
            Tok::Sym("-") => Some("-"),
            _ => None,
        };
        if let Some(sym) = sym {
            if let Some(name) = crate::parse::canonical_symbol(sym) {
                self.bump();
                return Ok((name.to_string(), t.span));
            }
        }
        self.expect_ident(what)
    }

    fn parse_file(&mut self) {
        while self.peek().tok != Tok::Eof {
            let t = self.peek().clone();
            let kw_name = match &t.tok {
                Tok::Ident(s) => s.clone(),
                _ => String::new(),
            };
            let Some(kw) = Keyword::from_str(&kw_name) else {
                // Report before consuming so `error` can see an `Error` token.
                let _: PResult<()> = self.error(
                    t.span,
                    format!(
                        "expected a keyword (CONSTANT(S), INIT, NEXT, SPECIFICATION, INVARIANT(S), \
                         PROPERTY/PROPERTIES, CONSTRAINT(S), ACTION_CONSTRAINT(S), SYMMETRY, VIEW, \
                         ALIAS, POSTCONDITION, CHECK_DEADLOCK), found {}",
                        t.describe()
                    ),
                );
                self.bump();
                self.skip_to_section_end();
                continue;
            };
            self.bump();
            if self.section(kw, &kw_name, t.span).is_err() {
                self.skip_to_section_end();
            }
        }
    }

    fn section(&mut self, kw: Keyword, kw_name: &str, kw_span: Span) -> PResult<()> {
        match kw {
            Keyword::Constant => self.constants(),
            Keyword::Init => self.single(kw_name, kw_span, |c| &mut c.init),
            Keyword::Next => self.single(kw_name, kw_span, |c| &mut c.next),
            Keyword::Specification => self.single(kw_name, kw_span, |c| &mut c.specification),
            Keyword::Symmetry => self.single(kw_name, kw_span, |c| &mut c.symmetry),
            Keyword::View => self.single(kw_name, kw_span, |c| &mut c.view),
            Keyword::Alias => self.single(kw_name, kw_span, |c| &mut c.alias),
            Keyword::InternalSingle => self.expect_ident(&format!("a name after {kw_name}")).map(|_| ()),
            Keyword::Invariant => self.list(kw_name, |c| &mut c.invariants),
            Keyword::Property => self.list(kw_name, |c| &mut c.properties),
            Keyword::Constraint => self.list(kw_name, |c| &mut c.constraints),
            Keyword::ActionConstraint => self.list(kw_name, |c| &mut c.action_constraints),
            Keyword::Possible => self.list(kw_name, |c| &mut c.possible),
            Keyword::PostCondition => self.list(kw_name, |c| &mut c.postconditions),
            Keyword::CheckDeadlock => {
                let t = self.peek().clone();
                let value = match &t.tok {
                    Tok::Ident(s) if s == "TRUE" => true,
                    Tok::Ident(s) if s == "FALSE" => false,
                    _ => return self.error(t.span, format!("expected TRUE or FALSE after CHECK_DEADLOCK, found {}", t.describe())),
                };
                self.bump();
                self.check_twice("CHECK_DEADLOCK", kw_span)?;
                self.cfg.check_deadlock = Some(value);
                Ok(())
            }
        }
    }

    /// Reports an error if the single-valued keyword `name` was already given.
    fn check_twice(&mut self, name: &str, span: Span) -> PResult<()> {
        if let Some((_, first)) = self.seen.iter().find(|(n, _)| n == name) {
            let first = *first;
            return self.error(span, format!("{name} specified twice (first at {}:{})", first.line, first.col));
        }
        self.seen.push((name.to_string(), span));
        Ok(())
    }

    /// A keyword taking exactly one name, e.g. `INIT Init`.
    fn single(&mut self, kw_name: &str, kw_span: Span, field: fn(&mut Config) -> &mut Option<String>) -> PResult<()> {
        let (name, _) = self.expect_ident(&format!("a name after {kw_name}"))?;
        self.check_twice(kw_name, kw_span)?;
        *field(&mut self.cfg) = Some(name);
        // TLC requires the next token to start a new section.
        let t = self.peek().clone();
        if !self.at_section_end() {
            return self.error(t.span, format!("{kw_name} takes a single name; unexpected {} (expected a keyword)", t.describe()));
        }
        Ok(())
    }

    /// A keyword taking a whitespace-separated list of names.
    fn list(&mut self, kw_name: &str, field: fn(&mut Config) -> &mut Vec<String>) -> PResult<()> {
        let mut names = Vec::new();
        let res = self.names(kw_name, &mut names);
        field(&mut self.cfg).extend(names.into_iter().map(|(n, _)| n));
        res
    }

    fn names(&mut self, kw_name: &str, out: &mut Vec<(String, Span)>) -> PResult<()> {
        while !self.at_section_end() {
            let t = self.peek().clone();
            if t.tok == Tok::Sym(",") {
                return self.error(t.span, format!("unexpected `,` in {kw_name} list: names are separated by whitespace"));
            }
            out.push(self.expect_ident(&format!("a name in {kw_name} list"))?);
        }
        Ok(())
    }

    fn constants(&mut self) -> PResult<()> {
        while !self.at_section_end() {
            self.binding()?;
        }
        Ok(())
    }

    /// One constant binding: `c = v`, `c = [M] v`, `F <- G`, `F <- [M] G`,
    /// `F(_, _) <- G`.
    fn binding(&mut self) -> PResult<()> {
        let (mut name, _) = self.expect_name("a constant name")?;
        // TLC accepts `A!B!C` on the left-hand side.
        while self.eat_sym("!") {
            let (part, _) = self.expect_ident("a name after `!`")?;
            name.push('!');
            name.push_str(&part);
        }

        // `F(_, _) <- G` or `F(1, 2) = v` (`_` reads as a model value).
        let mut args = None;
        if self.peek().tok == Tok::Sym("(") {
            self.bump();
            if self.at_section_end() {
                let t = self.peek().clone();
                return self.error(t.span, format!("unclosed `(` in binding of `{name}`"));
            }
            args = Some(self.value_list(")", "argument list")?);
        }

        let t = self.peek().clone();
        match t.tok {
            Tok::Sym("<-") => {
                self.bump();
                let module = self.module_scope()?;
                let (op, _) = self.expect_name(&format!("an operator name after `{name} <-`"))?;
                self.cfg.constants.push(ConstBinding::Subst { name, op, module });
                Ok(())
            }
            Tok::Sym("=") if args.is_some() => {
                self.bump();
                let value = self.value()?;
                self.cfg.constants.push(ConstBinding::OpValue { name, args: args.unwrap_or_default(), value });
                Ok(())
            }
            Tok::Sym("=") => {
                self.bump();
                let module = self.module_scope()?;
                let value = self.value()?;
                self.cfg.constants.push(ConstBinding::Value { name, value, module });
                Ok(())
            }
            _ => self.error(t.span, format!("expected `=` or `<-` after `{name}`, found {}", t.describe())),
        }
    }

    /// Optional `[M]` module scope.
    fn module_scope(&mut self) -> PResult<Option<String>> {
        if !self.eat_sym("[") {
            return Ok(None);
        }
        let (module, _) = self.expect_ident("a module name after `[`")?;
        self.expect_sym("]", "to close the module scope")?;
        Ok(Some(module))
    }

    fn value(&mut self) -> PResult<CfgValue> {
        let t = self.peek().clone();
        match &t.tok {
            Tok::Num(digits) => {
                self.bump();
                self.int(digits, false, t.span)
            }
            Tok::Sym("-") => {
                self.bump();
                let n = self.peek().clone();
                match &n.tok {
                    Tok::Num(digits) => {
                        self.bump();
                        self.int(digits, true, t.span)
                    }
                    _ => self.error(n.span, format!("expected a number after `-`, found {}", n.describe())),
                }
            }
            Tok::Str(s) => {
                self.bump();
                Ok(CfgValue::Str(s.clone()))
            }
            Tok::Ident(s) if s == "TRUE" => {
                self.bump();
                Ok(CfgValue::Bool(true))
            }
            Tok::Ident(s) if s == "FALSE" => {
                self.bump();
                Ok(CfgValue::Bool(false))
            }
            Tok::Ident(s) if Keyword::from_str(s).is_none() => {
                self.bump();
                Ok(CfgValue::ModelValue(s.clone()))
            }
            Tok::Sym("{") => {
                self.bump();
                Ok(CfgValue::Set(self.value_list("}", "set")?))
            }
            Tok::Sym("<<") => {
                self.bump();
                Ok(CfgValue::Tuple(self.value_list(">>", "tuple")?))
            }
            _ => self.error(t.span, format!("expected a value, found {}", t.describe())),
        }
    }

    /// Comma-separated values up to the closing delimiter (already past the
    /// opening one). Empty lists are allowed; trailing commas are not.
    fn value_list(&mut self, close: &'static str, what: &str) -> PResult<Vec<CfgValue>> {
        let mut elems = Vec::new();
        if self.eat_sym(close) {
            return Ok(elems);
        }
        loop {
            elems.push(self.value()?);
            if self.eat_sym(",") {
                continue;
            }
            self.expect_sym(close, &format!("or `,` in {what}"))?;
            return Ok(elems);
        }
    }

    fn int(&mut self, digits: &str, negative: bool, span: Span) -> PResult<CfgValue> {
        let text = if negative { format!("-{digits}") } else { digits.to_string() };
        match text.parse::<i64>() {
            Ok(n) => Ok(CfgValue::Int(n)),
            Err(_) => self.error(span, format!("integer literal `{text}` is out of range")),
        }
    }
}
