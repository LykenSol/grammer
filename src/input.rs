use std::fmt;
use std::ops::{self, Deref, Range, RangeInclusive};
use std::str;

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineColumn {
    pub line: usize,
    pub column: usize,
}

impl fmt::Debug for LineColumn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", 1 + self.line, 1 + self.column)
    }
}

impl LineColumn {
    fn count(prefix: &str) -> Self {
        let (line, column) = prefix
            .split('\n')
            .enumerate()
            .last()
            .map_or((0, 0), |(i, s)| (i, s.chars().count()));
        LineColumn { line, column }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineColumnRange {
    pub start: LineColumn,
    pub end: LineColumn,
}

impl fmt::Debug for LineColumnRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}-{:?}", self.start, self.end)
    }
}

pub trait Input: Sized {
    type Container: Deref<Target = Self::Slice>;
    type Slice: std::ops::Index<Range<usize>, Output = Self::Slice> + ?Sized;
    type SourceInfo: fmt::Debug;
    // FIXME(eddyb) remove - replace with `SourceInfo` for the affected range
    type SourceInfoPoint: fmt::Debug;
    fn to_container(self) -> Self::Container;
    fn slice<'a>(input: &'a Self::Container, range: Range<usize>) -> &'a Self::Slice;
    fn source_info(input: &Self::Container, range: Range<usize>) -> Self::SourceInfo;
    fn source_info_point(input: &Self::Container, index: usize) -> Self::SourceInfoPoint;
    fn len(input: &Self::Container) -> usize;
}

impl<T> Input for &[T] {
    type Container = Self;
    type Slice = [T];
    type SourceInfo = ops::Range<usize>;
    type SourceInfoPoint = usize;
    fn to_container(self) -> Self::Container {
        self
    }
    fn slice<'b>(input: &'b Self::Container, range: Range<usize>) -> &'b Self::Slice {
        &input[range]
    }
    fn source_info(_: &Self::Container, range: Range<usize>) -> Self::SourceInfo {
        range
    }
    fn source_info_point(_: &Self::Container, index: usize) -> Self::SourceInfoPoint {
        index
    }
    fn len(input: &Self::Container) -> usize {
        input.len()
    }
}

impl<'a> Input for &'a str {
    type Container = &'a str;
    type Slice = str;
    type SourceInfo = LineColumnRange;
    type SourceInfoPoint = LineColumn;
    fn to_container(self) -> Self::Container {
        self.into()
    }
    fn slice<'b>(input: &'b Self::Container, range: Range<usize>) -> &'b Self::Slice {
        &input[range]
    }
    fn source_info(input: &Self::Container, range: Range<usize>) -> Self::SourceInfo {
        let start = Self::source_info_point(input, range.start);
        // HACK(eddyb) add up `LineColumn`s to avoid counting twice.
        // Ideally we'd cache around a line map, like rustc's `SourceMap`.
        let mut end = LineColumn::count(Self::slice(input, range));
        end.line += start.line;
        if end.line == start.line {
            end.column += start.column;
        }
        LineColumnRange { start, end }
    }
    fn source_info_point<'i>(input: &Self::Container, index: usize) -> Self::SourceInfoPoint {
        LineColumn::count(&input[..index])
    }
    fn len(input: &Self::Container) -> usize {
        input.len()
    }
}

pub trait InputMatch<Pat: ?Sized> {
    fn match_left(&self, pat: &Pat) -> Option<usize>;
    fn match_right(&self, pat: &Pat) -> Option<usize>;
}

impl<I: ?Sized + InputMatch<Pat>, Pat: ?Sized> InputMatch<&'_ Pat> for I {
    fn match_left(&self, &pat: &&Pat) -> Option<usize> {
        self.match_left(pat)
    }
    fn match_right(&self, &pat: &&Pat) -> Option<usize> {
        self.match_right(pat)
    }
}

impl<T: PartialEq> InputMatch<[T]> for [T] {
    fn match_left(&self, pat: &[T]) -> Option<usize> {
        if self.starts_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &[T]) -> Option<usize> {
        if self.ends_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
}

impl<T: PartialOrd> InputMatch<RangeInclusive<T>> for [T] {
    fn match_left(&self, pat: &RangeInclusive<T>) -> Option<usize> {
        let x = self.first()?;
        if pat.start() <= x && x <= pat.end() {
            Some(1)
        } else {
            None
        }
    }
    fn match_right(&self, pat: &RangeInclusive<T>) -> Option<usize> {
        let x = self.last()?;
        if pat.start() <= x && x <= pat.end() {
            Some(1)
        } else {
            None
        }
    }
}

impl InputMatch<str> for str {
    fn match_left(&self, pat: &str) -> Option<usize> {
        if self.starts_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &str) -> Option<usize> {
        if self.ends_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
}

impl InputMatch<RangeInclusive<char>> for str {
    fn match_left(&self, pat: &RangeInclusive<char>) -> Option<usize> {
        let c = self.chars().next()?;
        if *pat.start() <= c && c <= *pat.end() {
            Some(c.len_utf8())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &RangeInclusive<char>) -> Option<usize> {
        let c = self.chars().rev().next()?;
        if *pat.start() <= c && c <= *pat.end() {
            Some(c.len_utf8())
        } else {
            None
        }
    }
}
