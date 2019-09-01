use crate::forest::{GrammarReflector, Node, OwnedParseForestAndNode, ParseForest};
use crate::high::ErasableL;
use crate::input::{Input, InputMatch, Range};
use indexing::{self, Index, Unknown};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

pub struct Parser<'a, 'i, G: GrammarReflector, I: Input, Pat> {
    state: &'a mut ParserState<'i, G, I, Pat>,
    result: Range<'i>,
    remaining: Range<'i>,
}

struct ParserState<'i, G: GrammarReflector, I: Input, Pat> {
    forest: ParseForest<'i, G, I>,
    last_input_pos: Index<'i, Unknown>,
    expected_pats: Vec<Pat>,
}

#[derive(Debug)]
pub struct ParseError<A, Pat> {
    pub at: A,
    pub expected: Vec<Pat>,
}

pub type ParseResult<A, Pat, T> = Result<T, ParseError<A, Pat>>;

impl<'i, P, G, I: Input, Pat: Ord> Parser<'_, 'i, G, I, Pat>
where
    // FIXME(eddyb) these shouldn't be needed, as they are bounds on
    // `GrammarReflector::NodeKind`, but that's ignored currently.
    P: fmt::Debug + Eq + Hash + Copy,
    G: GrammarReflector<NodeKind = P>,
{
    pub fn parse_with(
        grammar: G,
        input: I,
        f: impl for<'i2> FnOnce(Parser<'_, 'i2, G, I, Pat>) -> Option<Node<'i2, P>>,
    ) -> ParseResult<I::SourceInfoPoint, Pat, OwnedParseForestAndNode<G, P, I>> {
        ErasableL::indexing_scope(input.to_container(), |lifetime, input| {
            let range = Range(input.range());
            let mut state = ParserState {
                forest: ParseForest {
                    grammar,
                    input,
                    possibilities: HashMap::new(),
                },
                last_input_pos: range.first(),
                expected_pats: vec![],
            };

            let result = f(Parser {
                state: &mut state,
                result: Range(range.frontiers().0),
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
                        Ok(OwnedParseForestAndNode::pack(
                            lifetime,
                            (state.forest, node),
                        ))
                    } else {
                        Err(error)
                    }
                }
            }
        })
    }

    // FIXME(eddyb) find an nicer way for algorithms to manipulate these ranges.
    pub fn result(&self) -> Range<'i> {
        self.result
    }

    pub fn remaining(&self) -> Range<'i> {
        self.remaining
    }

    /// Get the current result range, and leave behind an empty range
    /// (at the end of the current result / start of the remaining input).
    pub fn take_result(&mut self) -> Range<'i> {
        let result = self.result;
        self.result = Range(result.frontiers().1);
        result
    }

    pub fn with_result_and_remaining<'a>(
        &'a mut self,
        result: Range<'i>,
        remaining: Range<'i>,
    ) -> Parser<'a, 'i, G, I, Pat> {
        // HACK(eddyb) enforce that `result` and `remaining` are inside `self`.
        assert_eq!(self.result, Range(self.remaining.frontiers().0));
        let full_new_range = result.join(remaining.0).unwrap();
        assert!(self.remaining.start() <= full_new_range.start());
        assert_eq!(self.remaining.end(), full_new_range.end());

        Parser {
            state: self.state,
            result,
            remaining,
        }
    }

    pub fn input_consume_left<'a, SpecificPat: Into<Pat>>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Parser<'a, 'i, G, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        let start = self.remaining.first();
        if start > self.state.last_input_pos {
            self.state.last_input_pos = start;
            self.state.expected_pats.clear();
        }
        match self.state.forest.input(self.remaining).match_left(&pat) {
            Some(n) => {
                let (matching, after, _) = self.remaining.split_at(n);
                if after.first() > self.state.last_input_pos {
                    self.state.last_input_pos = after.first();
                    self.state.expected_pats.clear();
                }
                Some(Parser {
                    state: self.state,
                    result: Range(self.result.join(matching).unwrap()),
                    remaining: Range(after),
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
    ) -> Option<Parser<'a, 'i, G, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        // FIXME(eddyb) implement error reporting support like in `input_consume_left`
        match self.state.forest.input(self.remaining).match_right(&pat) {
            Some(n) => {
                let (before, matching, _) = self.remaining.split_at(self.remaining.len() - n);
                Some(Parser {
                    state: self.state,
                    result: Range(matching.join(self.result.0).unwrap()),
                    remaining: Range(before),
                })
            }
            None => None,
        }
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_choice(&mut self, kind: P, choice: usize) {
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
    pub fn forest_add_split(&mut self, kind: P, left: Node<'i, P>) {
        self.result = Range(left.range.join(self.result.0).unwrap());
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
