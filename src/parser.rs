use super::RangeExt;
use crate::forest::{GrammarReflector, Node, ParseForest};
use crate::input::{Input, InputMatch};
use std::collections::HashMap;
use std::ops::Range;

pub struct Parser<'a, G: GrammarReflector, I: Input, Pat> {
    state: &'a mut ParserState<G, I, Pat>,
    result: Range<usize>,
    remaining: Range<usize>,
}

struct ParserState<G: GrammarReflector, I: Input, Pat> {
    forest: ParseForest<G, I>,
    last_input_pos: usize,
    expected_pats: Vec<Pat>,
}

#[derive(Debug)]
pub struct ParseError<A, Pat> {
    pub at: A,
    pub expected: Vec<Pat>,
}

pub type ParseResult<A, Pat, T> = Result<T, ParseError<A, Pat>>;

impl<G: GrammarReflector, I: Input, Pat: Ord> Parser<'_, G, I, Pat> {
    pub fn parse_with(
        grammar: G,
        input: I,
        f: impl for<'i2> FnOnce(Parser<'_, G, I, Pat>) -> Option<Node<G>>,
    ) -> ParseResult<I::SourceInfoPoint, Pat, (ParseForest<G, I>, Node<G>)> {
        let container: I::Container = input.to_container();
        let range = 0..Input::len(&container);
        let mut state = ParserState {
            forest: ParseForest {
                grammar,
                input: container,
                possibilities: HashMap::new(),
            },
            last_input_pos: 0,
            expected_pats: vec![],
        };

        let result = f(Parser {
            state: &mut state,
            result: 0..0,
            remaining: range,
        });

        let mut error = ParseError {
            at: I::source_info_point(&state.forest.input, state.last_input_pos),
            expected: state.expected_pats,
        };
        error.expected.sort();
        error.expected.dedup();

        match result {
            None => Err(error),
            Some(node) => {
                // The result is only a successful parse if it's as long as the input.
                if node.range == range {
                    Ok((state.forest, node))
                } else {
                    Err(error)
                }
            }
        }
    }

    // FIXME(eddyb) find an nicer way for algorithms to manipulate these ranges.
    pub fn result(&self) -> Range<usize> {
        self.result
    }

    pub fn remaining(&self) -> Range<usize> {
        self.remaining
    }

    /// Get the current result range, and leave behind an empty range
    /// (at the end of the current result / start of the remaining input).
    pub fn take_result(&mut self) -> Range<usize> {
        let result = self.result;
        self.result = result.end..result.end;
        result
    }

    pub fn with_result_and_remaining<'a>(
        &'a mut self,
        result: Range<usize>,
        remaining: Range<usize>,
    ) -> Parser<'a, G, I, Pat> {
        // HACK(eddyb) enforce that `result` and `remaining` are inside `self`.
        assert_eq!(self.result, self.remaining.start..self.remaining.start);
        let full_new_range = result.join(remaining).unwrap();
        assert!(self.remaining.start <= full_new_range.start);
        assert_eq!(self.remaining.end, full_new_range.end);

        Parser {
            state: self.state,
            result,
            remaining,
        }
    }

    pub fn input_consume_left<'a, SpecificPat: Into<Pat>>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Parser<'a, G, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        let start = self.remaining.start;
        if start > self.state.last_input_pos {
            self.state.last_input_pos = start;
            self.state.expected_pats.clear();
        }
        match self.state.forest.input(self.remaining).match_left(&pat) {
            Some(n) => {
                let (matching, after) = self.remaining.split_at(n);
                if after.start > self.state.last_input_pos {
                    self.state.last_input_pos = after.start;
                    self.state.expected_pats.clear();
                }
                Some(Parser {
                    state: self.state,
                    result: (self.result.join(matching).unwrap()),
                    remaining: (after),
                })
            }
            None => {
                if start == self.state.last_input_pos {
                    self.state.expected_pats.push(pat.into());
                }
                None
            }
        }
    }

    pub fn input_consume_right<'a, SpecificPat>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Parser<'a, G, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        // FIXME(eddyb) implement error reporting support like in `input_consume_left`
        match self.state.forest.input(self.remaining).match_right(&pat) {
            Some(n) => {
                let (before, matching) = self.remaining.split_at(self.remaining.len() - n);
                Some(Parser {
                    state: self.state,
                    result: matching.join(self.result).unwrap(),
                    remaining: before,
                })
            }
            None => None,
        }
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_choice(&mut self, kind: G::NodeKind, choice: usize) {
        self.state
            .forest
            .possibilities
            .entry(Node {
                kind,
                range: self.result,
            })
            .or_default()
            .insert(choice);
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_split(&mut self, kind: G::NodeKind, left: Node<G>) {
        self.result = left.range.join(self.result).unwrap();
        self.state
            .forest
            .possibilities
            .entry(Node {
                kind,
                range: self.result,
            })
            .or_default()
            .insert(left.range.len());
    }
}
