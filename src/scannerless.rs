use crate::input::InputMatch;
use crate::rule::{MatchesEmpty, MaybeKnown};
use std::char;
use std::fmt;
use std::ops::{self, Bound, RangeBounds};

pub type Context<S = String> = crate::context::Context<Pat<S>>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Pat<S = String, C = char> {
    String(S),
    Range(C, C),
}

impl<S: fmt::Debug> fmt::Debug for Pat<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pat::String(s) => s.fmt(f),
            &Pat::Range(start, end) => {
                if start != '\0' {
                    start.fmt(f)?;
                }
                f.write_str("..")?;
                if end != char::MAX {
                    f.write_str("=")?;
                    end.fmt(f)?;
                }
                Ok(())
            }
        }
    }
}

impl<'a, C> From<&'a str> for Pat<&'a str, C> {
    fn from(s: &'a str) -> Self {
        Pat::String(s)
    }
}

impl<C> From<&str> for Pat<String, C> {
    fn from(s: &str) -> Self {
        Pat::String(s.to_string())
    }
}

impl<C> From<String> for Pat<String, C> {
    fn from(s: String) -> Self {
        Pat::String(s)
    }
}

// HACK(eddyb) this should be generic over `RangeBounds<char>`,
// but that errors with: "upstream crates may add new impl of trait
// `std::ops::RangeBounds<char>` for type `&str` in future versions"
impl<'a, S> From<(Bound<&'a char>, Bound<&'a char>)> for Pat<S> {
    fn from(range: (Bound<&char>, Bound<&char>)) -> Self {
        let start = match range.start_bound() {
            Bound::Included(&c) => c,
            Bound::Excluded(&c) => {
                char::from_u32(c as u32 + 1).expect("excluded lower char bound too high")
            }
            Bound::Unbounded => '\0',
        };
        let end = match range.end_bound() {
            Bound::Included(&c) => c,
            Bound::Excluded(&c) => {
                char::from_u32(c as u32 - 1).expect("excluded upper char bound too low")
            }
            Bound::Unbounded => char::MAX,
        };
        Pat::Range(start, end)
    }
}

macro_rules! range_impls {
    ($($ty:ty),*) => {
        $(impl<S> From<$ty> for Pat<S> {
            fn from(range: $ty) -> Self {
                Self::from((range.start_bound(), range.end_bound()))
            }
        })*
    }
}
range_impls! {
    (Bound<char>, Bound<char>),
    ops::RangeTo<char>,
    ops::Range<char>,
    ops::RangeInclusive<char>,
    ops::RangeFull,
    ops::RangeFrom<char>,
    ops::RangeToInclusive<char>
}

impl<S: AsRef<str>> MatchesEmpty for Pat<S> {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        MaybeKnown::Known(match self {
            Pat::String(s) => s.as_ref().is_empty(),
            Pat::Range(..) => false,
        })
    }
}

impl<S, C: Copy> InputMatch<Pat<S, C>> for str
where
    str: InputMatch<S> + InputMatch<ops::RangeInclusive<C>>,
{
    fn match_left(&self, pat: &Pat<S, C>) -> Option<usize> {
        match pat {
            Pat::String(s) => self.match_left(s),
            &Pat::Range(start, end) => self.match_left(&(start..=end)),
        }
    }
    fn match_right(&self, pat: &Pat<S, C>) -> Option<usize> {
        match pat {
            Pat::String(s) => self.match_right(s),
            &Pat::Range(start, end) => self.match_right(&(start..=end)),
        }
    }
}

impl InputMatch<String> for str {
    fn match_left(&self, pat: &String) -> Option<usize> {
        self.match_left(&pat[..])
    }
    fn match_right(&self, pat: &String) -> Option<usize> {
        self.match_right(&pat[..])
    }
}
