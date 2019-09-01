use crate::high::{type_lambda, ExistsL, PairL};
use crate::input::{Input, Range};
use indexing::{self, Container};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::str;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NodeShape<T> {
    Opaque,
    Alias(T),
    Choice(usize),
    Opt(T),
    Split(T, T),
}

impl<T: fmt::Display> fmt::Display for NodeShape<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeShape::Opaque => write!(f, "Opaque"),
            NodeShape::Alias(inner) => write!(f, "Alias({})", inner),
            NodeShape::Choice(count) => write!(f, "Choice({})", count),
            NodeShape::Opt(inner) => write!(f, "Opt({})", inner),
            NodeShape::Split(left, right) => write!(f, "Split({}, {})", left, right),
        }
    }
}

impl<T> NodeShape<T> {
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> NodeShape<U> {
        match self {
            NodeShape::Opaque => NodeShape::Opaque,
            NodeShape::Alias(inner) => NodeShape::Alias(f(inner)),
            NodeShape::Choice(count) => NodeShape::Choice(count),
            NodeShape::Opt(inner) => NodeShape::Opt(f(inner)),
            NodeShape::Split(left, right) => NodeShape::Split(f(left), f(right)),
        }
    }
}

/// Objects capable of providing information about various parts of the grammar
/// (mostly parse nodes and their substructure).
///
/// For code generation, this doesn't need to be more than an unit struct, as
/// all the information can be hardcoded, but in more dynamic settings, this
/// might contain e.g. a reference to a context.
pub trait GrammarReflector {
    type NodeKind: fmt::Debug + Eq + Hash + Copy;

    fn node_shape(&self, kind: Self::NodeKind) -> NodeShape<Self::NodeKind>;
    fn node_shape_choice_get(&self, kind: Self::NodeKind, i: usize) -> Self::NodeKind;
    fn node_desc(&self, kind: Self::NodeKind) -> String;
}

pub struct Node<'i, G: GrammarReflector> {
    pub kind: G::NodeKind,
    pub range: Range<'i>,
}

// FIXME(eddyb) can't derive these on `Node<G>` because that puts bounds on `G`.
impl<G: GrammarReflector> Copy for Node<'_, G> {}
impl<G: GrammarReflector> Clone for Node<'_, G> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<G: GrammarReflector> PartialEq for Node<'_, G> {
    fn eq(&self, other: &Self) -> bool {
        (self.kind, self.range) == (other.kind, other.range)
    }
}
impl<G: GrammarReflector> Eq for Node<'_, G> {}
impl<G: GrammarReflector> PartialOrd for Node<'_, G>
where
    G::NodeKind: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.kind, self.range).partial_cmp(&(other.kind, other.range))
    }
}
impl<G: GrammarReflector> Ord for Node<'_, G>
where
    G::NodeKind: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.kind, self.range).cmp(&(other.kind, other.range))
    }
}
impl<G: GrammarReflector> Hash for Node<'_, G> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.kind, self.range).hash(state);
    }
}

impl<G: GrammarReflector> fmt::Debug for Node<'_, G> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} @ {}..{}",
            self.kind,
            self.range.start(),
            self.range.end()
        )
    }
}

/// A parse forest, in SPPF (Shared Packed Parse Forest) representation.
pub struct ParseForest<'i, G: GrammarReflector, I: Input> {
    pub grammar: G,
    // HACK(eddyb) `pub(crate)` only for `parser`.
    pub(crate) input: Container<'i, I::Container>,
    pub(crate) possibilities: HashMap<Node<'i, G>, BTreeSet<usize>>,
}

type_lambda! {
    pub type<'i> ParseForestL<G: GrammarReflector, I: Input> = ParseForest<'i, G, I>;
    pub type<'i> NodeL<G: GrammarReflector> = Node<'i, G>;
}

pub type OwnedParseForestAndNode<G, I> = ExistsL<PairL<ParseForestL<G, I>, NodeL<G>>>;

#[derive(Debug)]
pub struct MoreThanOne;

impl<'i, G: GrammarReflector, I: Input> ParseForest<'i, G, I> {
    pub fn input(&self, range: Range<'i>) -> &I::Slice {
        I::slice(&self.input, range)
    }

    pub fn source_info(&self, range: Range<'i>) -> I::SourceInfo {
        I::source_info(&self.input, range)
    }

    // NOTE(eddyb) this is a private helper and should never be exported.
    fn choice_child(&self, node: Node<'i, G>, choice: usize) -> Node<'i, G> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Choice(_) => Node {
                kind: self.grammar.node_shape_choice_get(node.kind, choice),
                range: node.range,
            },
            shape => unreachable!(
                "choice_child({:?}, {}): non-choice shape {:?}",
                node, choice, shape
            ),
        }
    }

    pub fn one_choice(&self, node: Node<'i, G>) -> Result<Node<'i, G>, MoreThanOne> {
        let choices = &self.possibilities[&node];
        if choices.len() > 1 {
            return Err(MoreThanOne);
        }
        let &choice = choices.iter().next().unwrap();
        Ok(self.choice_child(node, choice))
    }

    pub fn all_choices<'a>(
        &'a self,
        node: Node<'i, G>,
    ) -> impl Iterator<Item = Node<'i, G>> + Clone + 'a
    where
        G::NodeKind: 'a,
    {
        self.possibilities[&node]
            .iter()
            .cloned()
            .map(move |choice| self.choice_child(node, choice))
    }

    // NOTE(eddyb) this is a private helper and should never be exported.
    fn split_children(&self, node: Node<'i, G>, split: usize) -> (Node<'i, G>, Node<'i, G>) {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Split(left_kind, right_kind) => {
                let (left, right, _) = node.range.split_at(split);
                (
                    Node {
                        kind: left_kind,
                        range: Range(left),
                    },
                    Node {
                        kind: right_kind,
                        range: Range(right),
                    },
                )
            }
            shape => unreachable!(
                "split_children({:?}, {}): non-split shape {:?}",
                node, split, shape
            ),
        }
    }

    pub fn one_split(&self, node: Node<'i, G>) -> Result<(Node<'i, G>, Node<'i, G>), MoreThanOne> {
        let splits = &self.possibilities[&node];
        if splits.len() > 1 {
            return Err(MoreThanOne);
        }
        let &split = splits.iter().next().unwrap();
        Ok(self.split_children(node, split))
    }

    pub fn all_splits<'a>(
        &'a self,
        node: Node<'i, G>,
    ) -> impl Iterator<Item = (Node<'i, G>, Node<'i, G>)> + Clone + 'a
    where
        G::NodeKind: 'a,
    {
        self.possibilities[&node]
            .iter()
            .cloned()
            .map(move |split| self.split_children(node, split))
    }

    pub fn unpack_alias(&self, node: Node<'i, G>) -> Node<'i, G> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Alias(inner) => Node {
                kind: inner,
                range: node.range,
            },
            shape => unreachable!("unpack_alias({:?}): non-alias shape {:?}", node, shape),
        }
    }

    pub fn unpack_opt(&self, node: Node<'i, G>) -> Option<Node<'i, G>> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Opt(inner) => {
                if node.range.is_empty() {
                    None
                } else {
                    Some(Node {
                        kind: inner,
                        range: node.range,
                    })
                }
            }
            shape => unreachable!("unpack_opt({:?}): non-opt shape {:?}", node, shape),
        }
    }

    pub fn dump_graphviz(&self, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "digraph forest {{")?;
        let mut queue: VecDeque<_> = self.possibilities.keys().cloned().collect();
        let mut seen: HashSet<_> = queue.iter().cloned().collect();
        let mut p = 0;
        let node_name = |Node { kind, range }| {
            format!(
                "{} @ {:?}",
                self.grammar.node_desc(kind),
                self.source_info(range)
            )
        };
        while let Some(source) = queue.pop_front() {
            let source_name = node_name(source);
            writeln!(out, "    {:?} [shape=box]", source_name)?;
            let mut add_children = |children: &[(&str, Node<'i, G>)]| -> io::Result<()> {
                writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                writeln!(out, "    {:?} -> p{}:n", source_name, p)?;
                for &(port, child) in children {
                    writeln!(
                        out,
                        "    p{}:{} -> {:?}:n [dir=none]",
                        p,
                        port,
                        node_name(child)
                    )?;
                    if seen.insert(child) {
                        queue.push_back(child);
                    }
                }
                p += 1;
                Ok(())
            };
            match self.grammar.node_shape(source.kind) {
                NodeShape::Opaque => {}

                NodeShape::Alias(_) => {
                    add_children(&[("s", self.unpack_alias(source))])?;
                }

                NodeShape::Opt(_) => {
                    if let Some(child) = self.unpack_opt(source) {
                        add_children(&[("s", child)])?;
                    }
                }

                NodeShape::Choice(_) => {
                    for child in self.all_choices(source) {
                        add_children(&[("s", child)])?;
                    }
                }

                NodeShape::Split(..) => {
                    for (left, right) in self.all_splits(source) {
                        add_children(&[("sw", left), ("se", right)])?;
                    }
                }
            }
        }
        writeln!(out, "}}")
    }
}

pub mod typed {
    use super::{GrammarReflector, MoreThanOne, Node, ParseForest};
    use crate::input::Input;

    #[derive(Clone)]
    enum Void {}

    // HACK(eddyb) this type uses `T` but is also uninhabited.
    type PhantomVoid<T> = (Void, std::marker::PhantomData<T>);

    pub trait Shaped {
        type Shape: ShapeStateLen;

        // FIXME(eddyb) this is always `[usize; Self::Shape::STATE_LEN]`.
        // (but that doesn't work yet)
        type State: Default + AsMut<[usize]>;
    }

    pub trait FromShapeFields<'a, Forest, Node>: Sized {
        type Output;

        // FIXME(eddyb) use an array length const here instead when that works.
        type Fields: Default + AsMut<[Option<Node>]>;

        fn from_shape_fields(forest: &'a Forest, fields: Self::Fields) -> Self::Output;

        fn one(forest: &'a Forest, node: Node) -> Result<Self::Output, MoreThanOne>
        where
            Self: Shaped,
            Self::Shape: Shape<Forest, Node>,
            Node: Copy,
        {
            let mut state = Self::State::default();
            let state = state.as_mut();
            assert_eq!(state.len(), Self::Shape::STATE_LEN);

            Self::Shape::init(forest, node, state);

            let mut fields = Self::Fields::default();
            Self::Shape::read(forest, node, state, fields.as_mut());

            if Self::Shape::step(forest, node, state) {
                Err(MoreThanOne)
            } else {
                Ok(Self::from_shape_fields(forest, fields))
            }
        }

        fn all(forest: &'a Forest, node: Node) -> ShapedAllIter<'a, Self, Forest, Node>
        where
            Self: Shaped,
            Self::Shape: Shape<Forest, Node>,
            Node: Copy,
        {
            let mut state = Self::State::default();
            assert_eq!(state.as_mut().len(), Self::Shape::STATE_LEN);

            Self::Shape::init(forest, node, state.as_mut());

            ShapedAllIter {
                forest,
                node,
                state: Some(state),
            }
        }
    }

    pub struct ShapedAllIter<'a, T: Shaped, Forest, Node> {
        forest: &'a Forest,
        node: Node,
        state: Option<T::State>,
    }

    impl<'a, T, Forest, Node: Copy> Iterator for ShapedAllIter<'a, T, Forest, Node>
    where
        T: Shaped + FromShapeFields<'a, Forest, Node>,
        T::Shape: Shape<Forest, Node>,
    {
        type Item = T::Output;

        fn next(&mut self) -> Option<T::Output> {
            let state = self.state.as_mut()?.as_mut();
            let mut fields = T::Fields::default();
            T::Shape::read(self.forest, self.node, state, fields.as_mut());
            if !T::Shape::step(self.forest, self.node, state) {
                self.state.take();
            }
            Some(T::from_shape_fields(self.forest, fields))
        }
    }

    impl Shaped for () {
        type Shape = shape!(_);
        type State = [usize; <shape!(_)>::STATE_LEN];
    }

    impl<Forest, Node> FromShapeFields<'_, Forest, Node> for () {
        type Output = ();
        type Fields = [Option<Node>; 0];

        fn from_shape_fields(_: &Forest, []: Self::Fields) {}
    }

    impl<'a, Forest, Node, T> FromShapeFields<'a, Forest, Node> for Option<T>
    where
        T: FromShapeFields<'a, Forest, Node, Fields = [Option<Node>; 1]>,
    {
        type Output = Option<T::Output>;
        type Fields = [Option<Node>; 1];

        fn from_shape_fields(forest: &'a Forest, [node]: Self::Fields) -> Option<T::Output> {
            Some(T::from_shape_fields(forest, [Some(node?)]))
        }
    }

    pub struct WithShape<T, Shape, State>(PhantomVoid<(T, Shape, State)>);

    impl<T, Shape, State> Shaped for WithShape<T, Shape, State>
    where
        Shape: ShapeStateLen,
        State: Default + AsMut<[usize]>,
    {
        type Shape = Shape;
        type State = State;
    }

    impl<'a, Forest, Node, T, Shape, State> FromShapeFields<'a, Forest, Node>
        for WithShape<T, Shape, State>
    where
        T: FromShapeFields<'a, Forest, Node>,
    {
        type Output = T::Output;
        type Fields = T::Fields;

        fn from_shape_fields(forest: &'a Forest, fields: T::Fields) -> T::Output {
            T::from_shape_fields(forest, fields)
        }
    }

    pub trait ShapeStateLen {
        const STATE_LEN: usize;
    }

    pub trait Shape<Forest, Node>: ShapeStateLen {
        fn init(forest: &Forest, node: Node, state: &mut [usize]);
        fn read(forest: &Forest, node: Node, state: &[usize], fields: &mut [Option<Node>]);
        fn step(forest: &Forest, node: Node, state: &mut [usize]) -> bool;
    }

    pub struct Leaf(PhantomVoid<()>);

    impl ShapeStateLen for Leaf {
        const STATE_LEN: usize = 0;
    }

    impl<Forest, Node> Shape<Forest, Node> for Leaf {
        fn init(_: &Forest, _: Node, _: &mut [usize]) {}
        fn read(_: &Forest, _: Node, _: &[usize], _: &mut [Option<Node>]) {}
        fn step(_: &Forest, _: Node, _: &mut [usize]) -> bool {
            false
        }
    }

    // FIXME(eddyb) this should be using const generics.
    pub struct Field<X>(PhantomVoid<X>);

    impl<X> ShapeStateLen for Field<X> {
        const STATE_LEN: usize = 0;
    }

    impl<X, Forest, Node> Shape<Forest, Node> for Field<X>
    where
        X: Default + AsRef<[()]>,
    {
        fn init(_: &Forest, _: Node, _: &mut [usize]) {}
        fn read(_: &Forest, node: Node, _: &[usize], fields: &mut [Option<Node>]) {
            fields[X::default().as_ref().len()] = Some(node);
        }
        fn step(_: &Forest, _: Node, _: &mut [usize]) -> bool {
            false
        }
    }

    pub struct Split<Left, Right>(PhantomVoid<(Left, Right)>);

    impl<Left, Right> ShapeStateLen for Split<Left, Right>
    where
        Left: ShapeStateLen,
        Right: ShapeStateLen,
    {
        const STATE_LEN: usize = 1 + Left::STATE_LEN + Right::STATE_LEN;
    }

    impl<'i, G: GrammarReflector, I: Input, Left, Right> Shape<ParseForest<'i, G, I>, Node<'i, G>>
        for Split<Left, Right>
    where
        Left: Shape<ParseForest<'i, G, I>, Node<'i, G>>,
        Right: Shape<ParseForest<'i, G, I>, Node<'i, G>>,
    {
        fn init(forest: &ParseForest<'i, G, I>, node: Node<'i, G>, state: &mut [usize]) {
            let (state_split, state) = state.split_at_mut(1);
            let state_split = &mut state_split[0];
            let (state_left, state_right) = state.split_at_mut(Left::STATE_LEN);

            let &split = forest.possibilities[&node].iter().next().unwrap();

            let (left, right) = forest.split_children(node, split);

            *state_split = split;
            Left::init(forest, left, state_left);
            Right::init(forest, right, state_right);
        }
        fn read(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        ) {
            let (state_split, state) = state.split_at(1);
            let state_split = state_split[0];
            let (state_left, state_right) = state.split_at(Left::STATE_LEN);

            let (left, right) = forest.split_children(node, state_split);
            Left::read(forest, left, state_left, fields);
            Right::read(forest, right, state_right, fields);
        }
        fn step(forest: &ParseForest<'i, G, I>, node: Node<'i, G>, state: &mut [usize]) -> bool {
            let (state_split, state) = state.split_at_mut(1);
            let state_split = &mut state_split[0];
            let (state_left, state_right) = state.split_at_mut(Left::STATE_LEN);

            let (left, right) = forest.split_children(node, *state_split);

            Right::step(forest, right, state_right)
                || Left::step(forest, left, state_left) && {
                    Right::init(forest, right, state_right);
                    true
                }
                || ({
                    use std::ops::Bound::*;
                    forest.possibilities[&node]
                        .range((Excluded(*state_split), Unbounded))
                        .next()
                        .cloned()
                })
                .map(|split| {
                    *state_split = split;

                    let (left, right) = forest.split_children(node, split);

                    Left::init(forest, left, state_left);
                    Right::init(forest, right, state_right);
                })
                .is_some()
        }
    }

    pub struct Choice<At, Cases>(PhantomVoid<(At, Cases)>);

    impl<At, Cases> ShapeStateLen for Choice<At, Cases>
    where
        At: ShapeStateLen,
        Cases: ShapeStateLen,
    {
        const STATE_LEN: usize = At::STATE_LEN + Cases::STATE_LEN;
    }

    impl<'i, G: GrammarReflector, I: Input, At, Cases> Shape<ParseForest<'i, G, I>, Node<'i, G>>
        for Choice<At, Cases>
    where
        At: Shape<ParseForest<'i, G, I>, Node<'i, G>>,
        Cases: Shape<ParseForest<'i, G, I>, Node<'i, G>>,
    {
        fn init(forest: &ParseForest<'i, G, I>, node: Node<'i, G>, state: &mut [usize]) {
            let (state_at, state_cases) = state.split_at_mut(At::STATE_LEN);

            let &choice = forest.possibilities[&node].iter().next().unwrap();

            let child = forest.choice_child(node, choice);

            state_cases[0] = choice;
            At::init(forest, child, state_at);
            Cases::init(forest, child, state_cases);
        }
        fn read(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        ) {
            let (state_at, state_cases) = state.split_at(At::STATE_LEN);

            let child = forest.choice_child(node, state_cases[0]);

            At::read(forest, child, state_at, fields);
            Cases::read(forest, child, state_cases, fields);
        }
        fn step(forest: &ParseForest<'i, G, I>, node: Node<'i, G>, state: &mut [usize]) -> bool {
            let (state_at, state_cases) = state.split_at_mut(At::STATE_LEN);

            let child = forest.choice_child(node, state_cases[0]);

            At::step(forest, child, state_at)
                || Cases::step(forest, child, state_cases) && {
                    At::init(forest, child, state_at);
                    true
                }
                || ({
                    use std::ops::Bound::*;
                    forest.possibilities[&node]
                        .range((Excluded(state_cases[0]), Unbounded))
                        .next()
                        .cloned()
                })
                .map(|choice| {
                    state_cases[0] = choice;

                    let child = forest.choice_child(node, choice);

                    At::init(forest, child, state_at);
                    Cases::init(forest, child, state_cases);
                })
                .is_some()
        }
    }

    pub trait CaseList {
        const LEN: usize;
    }

    pub struct CaseAppend<Prefix, Last>(PhantomVoid<(Prefix, Last)>);

    impl<Prefix: CaseList, Last> CaseList for CaseAppend<Prefix, Last> {
        const LEN: usize = Prefix::LEN + 1;
    }

    impl<Prefix, Last> ShapeStateLen for CaseAppend<Prefix, Last>
    where
        Prefix: ShapeStateLen,
        Last: ShapeStateLen,
    {
        const STATE_LEN: usize = {
            // HACK(eddyb) this is just `max(1 + Last::STATE_LEN, Prefix::STATE_LEN)`.
            let a = 1 + Last::STATE_LEN;
            let b = Prefix::STATE_LEN;

            let a_gt_b_mask = -((a > b) as isize) as usize;
            (a_gt_b_mask & a) | (!a_gt_b_mask & b)
        };
    }

    impl<Forest, Node, Prefix, Last> Shape<Forest, Node> for CaseAppend<Prefix, Last>
    where
        Prefix: Shape<Forest, Node> + CaseList,
        Last: Shape<Forest, Node>,
    {
        fn init(forest: &Forest, node: Node, state: &mut [usize]) {
            let (state_choice, state_last) = state.split_at_mut(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::init(forest, node, state);
            } else {
                Last::init(forest, node, state_last);
            }
        }
        fn read(forest: &Forest, node: Node, state: &[usize], fields: &mut [Option<Node>]) {
            let (state_choice, state_last) = state.split_at(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::read(forest, node, state, fields);
            } else {
                Last::read(forest, node, state_last, fields);
            }
        }
        fn step(forest: &Forest, node: Node, state: &mut [usize]) -> bool {
            let (state_choice, state_last) = state.split_at_mut(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::step(forest, node, state)
            } else {
                Last::step(forest, node, state_last)
            }
        }
    }

    pub struct CaseEmpty(PhantomVoid<()>);

    impl CaseList for CaseEmpty {
        const LEN: usize = 0;
    }

    impl ShapeStateLen for CaseEmpty {
        const STATE_LEN: usize = 0;
    }

    impl<Forest, Node> Shape<Forest, Node> for CaseEmpty {
        fn init(_: &Forest, _: Node, _: &mut [usize]) {
            unreachable!()
        }
        fn read(_: &Forest, _: Node, _: &[usize], _: &mut [Option<Node>]) {
            unreachable!()
        }
        fn step(_: &Forest, _: Node, _: &mut [usize]) -> bool {
            unreachable!()
        }
    }

    pub struct Opt<A>(PhantomVoid<A>);

    impl<A> ShapeStateLen for Opt<A>
    where
        A: ShapeStateLen,
    {
        const STATE_LEN: usize = A::STATE_LEN;
    }

    impl<'i, G: GrammarReflector, I: Input, A> Shape<ParseForest<'i, G, I>, Node<'i, G>> for Opt<A>
    where
        A: Shape<ParseForest<'i, G, I>, Node<'i, G>>,
    {
        fn init(forest: &ParseForest<'i, G, I>, node: Node<'i, G>, state: &mut [usize]) {
            if let Some(child) = forest.unpack_opt(node) {
                A::init(forest, child, state);
            }
        }
        fn read(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        ) {
            if let Some(child) = forest.unpack_opt(node) {
                A::read(forest, child, state, fields);
            }
        }
        fn step(forest: &ParseForest<'i, G, I>, node: Node<'i, G>, state: &mut [usize]) -> bool {
            match forest.unpack_opt(node) {
                Some(child) => A::step(forest, child, state),
                None => false,
            }
        }
    }

    // HACK(eddyb) work around `macro_rules` not being `use`-able.
    pub use crate::__forest_typed_shape as shape;

    #[macro_export]
    macro_rules! __forest_typed_shape {
        (_) => {
            $crate::forest::typed::Leaf
        };
        ($i:literal) => {
            $crate::forest::typed::Field<[(); $i]>
        };
        (($l_shape:tt $r_shape:tt)) => {
            $crate::forest::typed::Split<
                $crate::forest::typed::shape!($l_shape),
                $crate::forest::typed::shape!($r_shape),
            >
        };
        ({ $at_shape:tt @ $($shape:tt)* }) => {
            $crate::forest::typed::Choice<
                $crate::forest::typed::shape!($at_shape),
                $crate::forest::typed::shape!(cases { $($shape)* } rev {}),
            >
        };
        // HACK(eddyb) have to reverse the tt list to produce a "snoc-list"
        // instead of "cons-list".
        (cases { $shape0:tt $($shape:tt)* } rev { $($shape_rev:tt)* }) => {
            $crate::forest::typed::shape!(cases { $($shape)* } rev { $shape0 $($shape_rev)* })
        };
        (cases {} rev { $shape_last:tt $($shape:tt)* }) => {
            $crate::forest::typed::CaseAppend<
                $crate::forest::typed::shape!(cases {} rev { $($shape)* }),
                $crate::forest::typed::shape!($shape_last),
            >
        };
        (cases {} rev {}) => { $crate::forest::typed::CaseEmpty };
        ([$shape:tt]) => {
            $crate::forest::typed::Opt<
                $crate::forest::typed::shape!($shape),
            >
        }
    }
}
