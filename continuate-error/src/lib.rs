use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::io;
use std::io::Write;
use std::iter;
use std::mem;
use std::num::NonZeroUsize;
use std::ops::Range;
use std::path::Path;
use std::path::PathBuf;
use std::result;
use std::sync::Arc;

use ariadne::Label;
use ariadne::Report;
use ariadne::ReportKind;

use chumsky::error::RichPattern;
use chumsky::input::Input;
use chumsky::label;
use chumsky::span;
use chumsky::util::MaybeRef;

use strum::EnumDiscriminants;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceId(NonZeroUsize);

impl SourceId {
    const DUMMY: SourceId = if let Some(id) = NonZeroUsize::new(1) {
        SourceId(id)
    } else {
        unreachable!()
    };

    const START: SourceId = if let Some(id) = NonZeroUsize::new(2) {
        SourceId(id)
    } else {
        unreachable!()
    };

    fn next(&mut self) -> SourceId {
        let id = *self;
        self.0 = id.0.checked_add(1).unwrap();
        id
    }

    const fn as_usize(self) -> usize {
        NonZeroUsize::get(self.0)
    }
}

pub struct Source {
    source: ariadne::Source<Arc<str>>,
    path: PathBuf,
}

impl Source {
    fn new(source: Arc<str>, path: PathBuf) -> Source {
        Source {
            source: source.into(),
            path,
        }
    }

    pub fn contents(&self) -> &str {
        self.source.text()
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

pub struct SourceCache {
    sources: HashMap<SourceId, Source>,
    next_id: SourceId,
}

impl SourceCache {
    pub fn new() -> SourceCache {
        SourceCache {
            sources: HashMap::new(),
            next_id: SourceId::START,
        }
    }

    /// ## Panics
    ///
    /// Panics if the total number of source files exceeds `u32::MAX - 3`.
    pub fn insert_source<T: Into<Arc<str>>>(&mut self, source: T, path: PathBuf) -> SourceId {
        let id = self.next_id.next();
        let source = Source::new(source.into(), path);
        self.sources.insert(id, source);
        id
    }

    pub fn eof(&self, source_id: SourceId) -> Option<Span> {
        let source = self.sources.get(&source_id)?;
        let len = source.source.len();
        Some(Span::new(len, len, source_id))
    }

    pub fn get(&self, id: SourceId) -> Option<&Source> {
        self.sources.get(&id)
    }

    fn fetch(
        &self,
        id: SourceId,
    ) -> result::Result<&ariadne::Source<Arc<str>>, Box<dyn fmt::Debug + '_>> {
        self.sources.get(&id).map_or_else(
            || Err(Box::new(format!("source for {id:?} not found")) as _),
            |source| Ok(&source.source),
        )
    }
}

impl Default for SourceCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ariadne::Cache<SourceId> for SourceCache {
    type Storage = Arc<str>;

    #[inline]
    fn fetch(
        &mut self,
        id: &SourceId,
    ) -> result::Result<&ariadne::Source<Self::Storage>, Box<dyn fmt::Debug + '_>> {
        (*self).fetch(*id)
    }

    #[inline]
    fn display<'a>(&self, id: &'a SourceId) -> Option<Box<dyn fmt::Display + 'a>> {
        Some(Box::new(
            self.sources.get(id)?.path.to_string_lossy().into_owned(),
        ))
    }
}

impl ariadne::Cache<SourceId> for &SourceCache {
    type Storage = Arc<str>;

    #[inline]
    fn fetch(
        &mut self,
        id: &SourceId,
    ) -> result::Result<&ariadne::Source<Self::Storage>, Box<dyn fmt::Debug + '_>> {
        (**self).fetch(*id)
    }

    #[inline]
    fn display<'a>(&self, id: &'a SourceId) -> Option<Box<dyn fmt::Display + 'a>> {
        (**self).display(id)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    start: usize,
    len: u32,
    source: SourceId,
}

impl Span {
    /// An empty span in a non-existent source file.
    pub const fn dummy() -> Span {
        Span {
            start: 0,
            len: 0,
            source: SourceId::DUMMY,
        }
    }

    /// ## Panics
    ///
    /// Panics if `end > start` or if `end - start > u32::MAX`.
    pub const fn new(start: usize, end: usize, source: SourceId) -> Span {
        let len = end.checked_sub(start).unwrap();
        assert!(len <= u32::MAX as usize, "span length too long");

        Span {
            start,
            len: len as u32,
            source,
        }
    }

    const fn is_dummy(&self) -> bool {
        self.source.as_usize() == SourceId::DUMMY.as_usize()
    }

    pub fn contains_span(&self, other: &Span) -> bool {
        let self_end = self.start + self.len as usize;
        let other_end = other.start + other.len as usize;
        self.source == other.source && self.start <= other.start && self_end >= other_end
    }

    #[must_use = "This method returns a new span without modifying the original one"]
    pub const fn first_n(&self, n: usize) -> Span {
        Span {
            start: self.start,
            len: n as u32,
            source: self.source,
        }
    }

    #[must_use = "This method returns a new span without modifying the original one"]
    pub const fn last_n(&self, n: usize) -> Span {
        Span {
            start: self.start + self.len as usize - n,
            len: n as u32,
            source: self.source,
        }
    }

    #[inline]
    pub const fn range(&self) -> Range<usize> {
        Range {
            start: self.start,
            end: self.start + self.len as usize,
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn union(self, other: Span) -> Option<Span> {
        if self.is_dummy() {
            Some(other)
        } else if other.is_dummy() {
            Some(self)
        } else if self.source == other.source {
            let self_end = self.start + self.len as usize;
            let other_end = other.start + other.len as usize;
            let end = self_end.max(other_end);
            let start = self.start.min(other.start);
            Some(Span {
                start,
                len: (end - start) as u32,
                source: self.source,
            })
        } else {
            None
        }
    }
}

impl span::Span for Span {
    type Offset = usize;
    type Context = SourceId;

    fn new(context: SourceId, range: Range<usize>) -> Self {
        Span {
            start: range.start,
            len: (range.end - range.start) as u32,
            source: context,
        }
    }

    fn context(&self) -> Self::Context {
        self.source
    }

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.start + self.len as usize
    }

    fn union(&self, other: Self) -> Self {
        (*self).union(other).unwrap()
    }
}

impl ariadne::Span for Span {
    type SourceId = SourceId;

    fn source(&self) -> &Self::SourceId {
        &self.source
    }

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.start + self.len as usize
    }

    fn len(&self) -> usize {
        self.len as usize
    }
}

#[derive(EnumDiscriminants)]
#[strum_discriminants(name(ErrorCode))]
#[strum_discriminants(repr(u8))]
#[derive(Debug, Clone, PartialEq)]
enum ErrorInner {
    UnexpectedToken {
        expected: HashSet<Option<String>>,
        found: Option<String>,
        span: Span,
    },
    UnclosedDelimiter {
        unclosed: String,
        unclosed_span: Span,
        expected: String,
        found: String,
        found_span: Span,
    },
    UnopenedDelimiter {
        unopened: String,
        unopened_span: Span,
    },
    Simple(String),
}

impl ErrorInner {
    fn take_found(&mut self) -> Option<String> {
        match self {
            ErrorInner::UnexpectedToken { found, .. } => found.take(),
            ErrorInner::UnclosedDelimiter { found, .. } => Some(mem::take(found)),
            ErrorInner::UnopenedDelimiter { unopened, .. } => Some(mem::take(unopened)),
            ErrorInner::Simple(_) => None,
        }
    }

    const fn span(&self) -> Option<Span> {
        match *self {
            ErrorInner::UnexpectedToken { span, .. } => Some(span),
            ErrorInner::UnclosedDelimiter { found_span, .. } => Some(found_span),
            ErrorInner::UnopenedDelimiter { unopened_span, .. } => Some(unopened_span),
            ErrorInner::Simple(_) => None,
        }
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&(*self as u8), f)
    }
}

fn format_token(token: Option<&String>) -> String {
    if let Some(token) = token {
        token.to_owned()
    } else {
        "EOF".to_owned()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct SingleError {
    inner: ErrorInner,
    note: Option<String>,
    span: Span,
}

impl SingleError {
    fn report(&self) -> Report<'static, Span> {
        let mut builder =
            Report::build(ReportKind::Error, self.span).with_code(ErrorCode::from(&self.inner));

        if let Some(note) = &self.note {
            builder.set_note(note);
        }

        match self.inner {
            ErrorInner::UnexpectedToken {
                ref expected,
                ref found,
                span,
            } => {
                builder.set_message("Unexpected token");
                let mut iter = expected.iter();
                let mut expected_message = if expected.len() == 1 {
                    let expected = format_token(iter.next().unwrap().as_ref());
                    format!("Expected '{expected}', ")
                } else if expected.len() == 2 {
                    let expected_1 = format_token(iter.next().unwrap().as_ref());
                    let expected_2 = format_token(iter.next().unwrap().as_ref());
                    format!("Expected '{expected_1}' or '{expected_2}', ")
                } else {
                    let mut buf = "Expected one of ".to_string();
                    for token in iter {
                        buf.push_str(&format_token(token.as_ref()));
                        buf.push_str(", ");
                    }
                    buf
                };
                expected_message.push_str(&format!("found {}", format_token(found.as_ref())));
                builder.add_label(Label::new(span).with_message(expected_message));
            }
            ErrorInner::UnclosedDelimiter {
                ref unclosed,
                unclosed_span,
                ref expected,
                found: _,
                found_span,
            } => {
                let unclosed_message = format!("Unclosed '{unclosed}'");
                builder.set_message(unclosed_message.clone());
                builder.add_label(Label::new(unclosed_span).with_message(unclosed_message));
                builder.add_label(
                    Label::new(found_span).with_message(format!("Expected '{expected}' here")),
                );
            }
            ErrorInner::UnopenedDelimiter {
                ref unopened,
                unopened_span,
            } => {
                let message = format!("Unmatched '{unopened}'");
                builder.set_message(message.clone());
                builder.add_label(Label::new(unopened_span).with_message(message));
            }
            ErrorInner::Simple(ref message) => {
                builder.set_message(message);
            }
        }

        builder.finish()
    }
}

#[allow(clippy::fallible_impl_from)]
impl From<ErrorInner> for SingleError {
    fn from(value: ErrorInner) -> Self {
        let span = match value {
            ErrorInner::UnexpectedToken { span, .. } => span,
            ErrorInner::UnclosedDelimiter {
                unclosed_span,
                found_span,
                ..
            } => unclosed_span.union(found_span).unwrap(),
            ErrorInner::UnopenedDelimiter { unopened_span, .. } => unopened_span,
            ErrorInner::Simple(_) => Span::dummy(),
        };

        SingleError {
            inner: value,
            note: None,
            span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    errors: Vec<SingleError>,
}

impl Error {
    pub fn unexpected_token<I: IntoIterator<Item = Option<String>>>(
        expected: I,
        found: Option<String>,
        span: Span,
    ) -> Error {
        ErrorInner::UnexpectedToken {
            expected: expected.into_iter().collect(),
            found,
            span,
        }
        .into()
    }

    pub fn unclosed_delimiter(
        unclosed: String,
        unclosed_span: Span,
        expected: String,
        found: String,
        found_span: Span,
    ) -> Error {
        ErrorInner::UnclosedDelimiter {
            unclosed,
            unclosed_span,
            expected,
            found,
            found_span,
        }
        .into()
    }

    pub fn unopened_delimiter(unopened: String, unopened_span: Span) -> Error {
        ErrorInner::UnopenedDelimiter {
            unopened,
            unopened_span,
        }
        .into()
    }

    fn simple(message: String) -> Error {
        ErrorInner::Simple(message).into()
    }

    pub fn report(&self) -> Vec<Report<'static, Span>> {
        self.errors.iter().map(SingleError::report).collect()
    }

    /// Write this error to an implementor of [`Write`].
    ///
    /// This method assumes that the output is going to be printed to `stderr`.
    ///
    /// ## Errors
    ///
    /// Returns an error if writing to `w` fails.
    pub fn write(&self, cache: &SourceCache, mut w: impl Write) -> io::Result<()> {
        self.report()
            .into_iter()
            .try_for_each(|report| report.write(cache, &mut w))
    }

    /// Write this error to an implementor of [`Write`].
    ///
    /// This method assumes that the output is going to be printed to `stderr`.
    ///
    /// ## Errors
    ///
    /// Returns an error if writing to `w` fails.
    pub fn write_for_stdout(&self, cache: &SourceCache, mut w: impl Write) -> io::Result<()> {
        self.report()
            .into_iter()
            .try_for_each(|report| report.write_for_stdout(cache, &mut w))
    }

    /// Write this error to `stderr`.
    ///
    /// ## Errors
    ///
    /// Returns an error if writing to `stderr` fails.
    pub fn eprint(&self, cache: &SourceCache) -> io::Result<()> {
        self.report()
            .into_iter()
            .try_for_each(|report| report.eprint(cache))
    }

    /// Write this error to `stdout`.
    ///
    /// In most cases, [`Error::eprint`] is the "more correct" method to use.
    ///
    /// ## Errors
    ///
    /// Returns an error if writing to `stdout` fails.
    pub fn print(&self, cache: &SourceCache) -> io::Result<()> {
        self.report()
            .into_iter()
            .try_for_each(|report| report.print(cache))
    }

    #[must_use]
    pub fn combine(mut self, other: Error) -> Error {
        self.errors.extend(other.errors);
        self
    }
}

impl From<ErrorInner> for Error {
    fn from(value: ErrorInner) -> Self {
        Error {
            errors: vec![value.into()],
        }
    }
}

impl From<&str> for Error {
    fn from(value: &str) -> Self {
        Error::simple(value.to_string())
    }
}

impl From<String> for Error {
    fn from(value: String) -> Self {
        Error::simple(value)
    }
}

impl Default for Error {
    fn default() -> Self {
        Error::simple("unrecognised token".to_string())
    }
}

impl<'a, I> chumsky::error::Error<'a, I> for Error
where
    I: Input<'a, Span = Span>,
    I::Token: fmt::Display,
{
    fn merge(mut self, mut other: Self) -> Self {
        self.errors.append(&mut other.errors);
        self
    }
}

fn to_string_as_pattern<'a, T: fmt::Display + 'a, L: Into<RichPattern<'a, T>>>(token: L) -> String {
    Into::<RichPattern<'a, T>>::into(token).to_string()
}

impl<'a, 'b, I, L> label::LabelError<'a, I, L> for Error
where
    I: Input<'a, Span = Span>,
    I::Token: fmt::Display + 'b,
    L: Into<RichPattern<'b, I::Token>>,
{
    fn expected_found<E: IntoIterator<Item = L>>(
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self::unexpected_token(
            expected
                .into_iter()
                .map(|token| Some(to_string_as_pattern(token))),
            found.map(|token| (*token).to_string()),
            span,
        )
    }

    fn label_with(&mut self, label: L) {
        let label = to_string_as_pattern(label);
        for error in &mut self.errors {
            if let ErrorInner::UnexpectedToken {
                ref mut expected,
                found: _,
                span: _,
            } = error.inner
            {
                expected.clear();
                expected.insert(Some(label.clone()));
            } else {
                error.inner = ErrorInner::UnexpectedToken {
                    expected: iter::once(Some(label.clone())).collect(),
                    found: error.inner.take_found(),
                    span: error.inner.span().unwrap_or_else(Span::dummy),
                }
            }
        }
    }

    fn in_context(&mut self, label: L, _: Span) {
        <Self as label::LabelError<'a, I, L>>::label_with(self, label);
    }
}

pub type Result<T> = result::Result<T, Error>;
