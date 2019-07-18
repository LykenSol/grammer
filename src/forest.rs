use crate::high::{type_lambda, ExistsL, PairL};
use crate::input::{Input, Range};
use indexing::{self, Container};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::iter;
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

    pub fn dump_graphviz(&self, root: Option<Node<'i, G>>, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "digraph forest {{")?;
        let mut queue: VecDeque<_> = match root {
            Some(root) => iter::once(root).collect(),
            None => self.possibilities.keys().cloned().collect(),
        };
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

pub mod dynamic {
    use super::{
        GrammarReflector, MoreThanOne, Node, NodeShape, OwnedParseForestAndNode, ParseForest,
    };
    use crate::context::{Context, IFields, IRule, IStr};
    use crate::input::{Input, Range};
    use crate::rule::{Fields, Rule};
    use std::fmt;
    use std::hash::Hash;
    use std::rc::Rc;

    pub struct CxAndGrammar<'a, Pat> {
        pub cx: &'a Context<Pat>,
        pub grammar: &'a crate::Grammar,
    }

    impl<Pat: Eq + Hash + fmt::Debug> GrammarReflector for CxAndGrammar<'_, Pat> {
        type NodeKind = IRule;

        fn node_shape(&self, rule: IRule) -> NodeShape<IRule> {
            rule.node_shape(self.cx, Some(&self.grammar.rules))
        }
        fn node_shape_choice_get(&self, rule: IRule, i: usize) -> IRule {
            match &self.cx[rule] {
                Rule::Or(cases) => cases[i],
                _ => unreachable!(),
            }
        }
        fn node_desc(&self, rule: IRule) -> String {
            rule.node_desc(self.cx)
        }
    }

    // TODO(eddyb) remove this entirely, only user of it left is `ListHandle`.
    #[derive(Clone)]
    struct ExpandedTree<'i, G: GrammarReflector> {
        node: Node<'i, G>,
        kind: ExpandedTreeKind<'i, G>,
    }

    #[derive(Clone)]
    enum ExpandedTreeKind<'i, G: GrammarReflector> {
        Leaf,
        Or(G::NodeKind, Rc<ExpandedTree<'i, G>>),
        Opt(Option<Rc<ExpandedTree<'i, G>>>),
        Concat([Rc<ExpandedTree<'i, G>>; 2]),
    }

    impl<'i, G: GrammarReflector> ExpandedTree<'i, G> {
        fn one_from_node<I>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
        ) -> Result<Rc<Self>, MoreThanOne>
        where
            I: Input,
        {
            let kind = match forest.grammar.node_shape(node.kind) {
                NodeShape::Opaque | NodeShape::Alias(_) => ExpandedTreeKind::Leaf,
                NodeShape::Choice(_) => {
                    let child = forest.one_choice(node)?;
                    ExpandedTreeKind::Or(child.kind, Self::one_from_node(forest, child)?)
                }
                NodeShape::Opt(_) => ExpandedTreeKind::Opt(match forest.unpack_opt(node) {
                    Some(child) => Some(Self::one_from_node(forest, child)?),
                    None => None,
                }),
                NodeShape::Split(..) => {
                    let (left, right) = forest.one_split(node)?;
                    ExpandedTreeKind::Concat([
                        Self::one_from_node(forest, left)?,
                        Self::one_from_node(forest, right)?,
                    ])
                }
            };
            Ok(Rc::new(ExpandedTree { node, kind }))
        }

        fn all_from_node<I>(forest: &ParseForest<'i, G, I>, node: Node<'i, G>) -> Vec<Rc<Self>>
        where
            I: Input,
        {
            let new = |kind| Rc::new(ExpandedTree { node, kind });
            match forest.grammar.node_shape(node.kind) {
                NodeShape::Opaque | NodeShape::Alias(_) => vec![new(ExpandedTreeKind::Leaf)],
                NodeShape::Choice(_) => forest
                    .all_choices(node)
                    .flat_map(|child| {
                        Self::all_from_node(forest, child)
                            .into_iter()
                            .map(move |child_tree| {
                                new(ExpandedTreeKind::Or(child.kind, child_tree))
                            })
                    })
                    .collect(),
                NodeShape::Opt(_) => match forest.unpack_opt(node) {
                    Some(child) => Self::all_from_node(forest, child)
                        .into_iter()
                        .map(|child_tree| new(ExpandedTreeKind::Opt(Some(child_tree))))
                        .collect(),
                    None => vec![new(ExpandedTreeKind::Opt(None))],
                },
                NodeShape::Split(..) => forest
                    .all_splits(node)
                    .flat_map(|(left, right)| {
                        Self::all_from_node(forest, left)
                            .into_iter()
                            .flat_map(move |left_tree| {
                                Self::all_from_node(forest, right).into_iter().map(
                                    move |right_tree| {
                                        new(ExpandedTreeKind::Concat([
                                            left_tree.clone(),
                                            right_tree,
                                        ]))
                                    },
                                )
                            })
                    })
                    .collect(),
            }
        }
    }

    #[derive(Debug)]
    pub struct Ambiguity<T>(T);

    pub struct OwnedHandle<'a, Pat: Eq + Hash + fmt::Debug, I: Input> {
        pub forest_and_node: OwnedParseForestAndNode<CxAndGrammar<'a, Pat>, I>,
    }

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> OwnedHandle<'_, Pat, I> {
        pub fn source_info(&self) -> I::SourceInfo {
            self.forest_and_node.unpack_ref(|_, forest_and_node| {
                let (ref forest, node) = *forest_and_node;
                forest.source_info(node.range)
            })
        }

        pub fn with<R>(&self, f: impl FnOnce(Handle<'_, '_, '_, Pat, I>) -> R) -> R {
            self.forest_and_node.unpack_ref(|_, forest_and_node| {
                let (ref forest, node) = *forest_and_node;
                f(Handle {
                    forest,
                    node,
                    fields: None,
                    disambiguator: None,
                })
            })
        }
    }

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> fmt::Debug for OwnedHandle<'_, Pat, I> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.with(|handle| handle.fmt(f))
        }
    }

    // FIXME(eddyb) figure out how to maybe get rid of the 'a/'b split.
    pub struct Handle<'a, 'b, 'i, Pat: Eq + Hash + fmt::Debug, I: Input> {
        pub forest: &'a ParseForest<'i, CxAndGrammar<'b, Pat>, I>,
        pub node: Node<'i, CxAndGrammar<'b, Pat>>,
        pub fields: Option<IFields>,
        // FIXME(eddyb) support an arbitrary number of disambiguations here
        disambiguator: Option<(Node<'i, CxAndGrammar<'b, Pat>>, usize)>,
    }

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> Copy for Handle<'_, '_, '_, Pat, I> {}

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> Clone for Handle<'_, '_, '_, Pat, I> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> fmt::Debug for Handle<'_, '_, '_, Pat, I> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            struct FieldName<'a>(&'a str);
            impl fmt::Debug for FieldName<'_> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.write_str(self.0)
                }
            }

            self.source_info().fmt(f)?;

            let cx = self.forest.grammar.cx;
            let mut first = true;

            let name = match cx[self.node.kind] {
                Rule::RepeatMany(..) | Rule::RepeatMore(..) => {
                    f.write_str(" => ")?;
                    for x in self.all_lists() {
                        if !first {
                            f.write_str(" | ")?;
                        }
                        first = false;
                        x.fmt(f)?;
                    }
                    return Ok(());
                }
                Rule::Call(name) => Some(name),
                _ => None,
            };

            if self.fields.is_some() || name.is_some() {
                f.write_str(" => ")?;
                for x in self.all_records() {
                    if !first {
                        f.write_str(" | ")?;
                    }
                    first = false;

                    if let Some(name) = name {
                        f.write_str(&cx[name])?;
                        f.write_str(" ")?;
                    }

                    let mut f = f.debug_map();
                    x.visit_fields(&mut |r| match r {
                        Ok((name, field)) => {
                            f.entry(&FieldName(&cx[name]), &field);
                        }
                        Err(Ambiguity(handle)) => {
                            // FIXME(eddyb) print this properly, similar to lists.
                            // (will require reimplementing the `debug_map` adapter)
                            f.entry(&FieldName(".."), &handle);
                        }
                    });
                    f.finish()?;
                }
            }
            Ok(())
        }
    }

    impl<'a, 'b, 'i, Pat: Eq + Hash + fmt::Debug, I: Input> Handle<'a, 'b, 'i, Pat, I> {
        pub fn source(self) -> &'a I::Slice {
            self.forest.input(self.node.range)
        }

        pub fn source_info(self) -> I::SourceInfo {
            self.forest.source_info(self.node.range)
        }

        // FIXME(eddyb) make this return an iterator or get rid of somehow.
        fn all_records(self) -> Vec<Self> {
            let forest = self.forest;
            let cx = forest.grammar.cx;

            let mut node = self.node;
            let fields = self.fields.unwrap_or_else(|| match cx[node.kind] {
                Rule::Call(name) => {
                    if let NodeShape::Alias(inner) = forest.grammar.node_shape(node.kind) {
                        node.kind = inner;
                    }
                    forest.grammar.grammar.rules[&name].fields
                }
                _ => unreachable!("not a record"),
            });

            let rec = |disambiguator: Option<usize>| Handle {
                disambiguator: disambiguator.map(|i| (node, i)),
                ..self
            };

            if let Fields::Aggregate(_) = cx[fields] {
                match &cx[node.kind] {
                    Rule::Concat(_) => {
                        return forest
                            .all_splits(node)
                            .map(|(left, _)| rec(Some(left.range.len())))
                            .collect()
                    }
                    Rule::Or(rules) => {
                        return forest
                            .all_choices(node)
                            .map(|child| {
                                // FIXME(eddyb) expose the index from the forest,
                                // or integrate fielded traversal through the forest.
                                let i = rules.iter().position(|&rule| child.kind == rule).unwrap();
                                rec(Some(i))
                            })
                            .collect();
                    }
                    _ => {}
                }
            }
            vec![rec(None)]
        }

        pub fn visit_fields(
            &self,
            f: &mut impl FnMut(
                // FIXME(eddyb) maybe make the error case, or Ambiguity itself, an iterator?
                // Maybe `Ambiguities<Self>` would be better? Same for list tails?
                Result<(IStr, Self), Ambiguity<Self>>,
            ),
        ) {
            let forest = self.forest;
            let cx = forest.grammar.cx;

            let mut node = self.node;
            // FIXME(eddyb) remember the name here.
            let fields = self.fields.unwrap_or_else(|| match cx[node.kind] {
                Rule::Call(name) => {
                    if let NodeShape::Alias(inner) = forest.grammar.node_shape(node.kind) {
                        node.kind = inner;
                    }
                    forest.grammar.grammar.rules[&name].fields
                }
                _ => unreachable!("not a record"),
            });

            let children = match &cx[fields] {
                Fields::Leaf(field) => {
                    if let Some(field) = field {
                        f(Ok((
                            field.name,
                            Handle {
                                forest,
                                node,
                                fields: if cx[field.sub] == Fields::Leaf(None) {
                                    // HACK(eddyb) figure out a nicer way to communicate leaves.
                                    None
                                } else {
                                    Some(field.sub)
                                },
                                disambiguator: None,
                            },
                        )))
                    }
                    return;
                }
                Fields::Aggregate(children) => children,
            };
            let mut visit_child = |child, i| {
                Handle {
                    forest,
                    node: child,
                    fields: Some(children[i]),
                    disambiguator: None,
                }
                .visit_fields(f);
            };

            match cx[node.kind] {
                Rule::Concat([left_rule, right_rule]) => {
                    let split = match self.disambiguator {
                        Some((dis_node, dis_split)) if dis_node == node => {
                            let (left, right, _) = node.range.split_at(dis_split);
                            Ok((
                                Node {
                                    kind: left_rule,
                                    range: Range(left),
                                },
                                Node {
                                    kind: right_rule,
                                    range: Range(right),
                                },
                            ))
                        }
                        _ => forest.one_split(node),
                    };
                    match split {
                        Ok((left, right)) => {
                            visit_child(left, 0);
                            visit_child(right, 1);
                        }
                        Err(_) => return f(Err(Ambiguity(*self))),
                    }
                }
                Rule::Or(ref rules) => {
                    let choice = match self.disambiguator {
                        Some((dis_node, dis_choice)) if dis_node == node => Ok(Node {
                            kind: rules[dis_choice],
                            range: node.range,
                        }),
                        _ => forest.one_choice(node),
                    };
                    match choice {
                        Ok(child) => {
                            // FIXME(eddyb) use `IndexSet<IRule>` in `Rule::Or`.
                            let i = rules.iter().position(|&rule| child.kind == rule).unwrap();
                            visit_child(child, i);
                        }
                        Err(_) => return f(Err(Ambiguity(*self))),
                    }
                }
                Rule::Opt(_) => {
                    if let Some(child) = forest.unpack_opt(node) {
                        visit_child(child, 0);
                    }
                }
                _ => unreachable!("not an aggregate"),
            }
        }

        pub fn field(&self, name: IStr) -> Result<Option<Self>, Ambiguity<Self>> {
            // FIXME(eddyb) speed this up somehow.
            let mut found = None;
            let mut ambiguity = None;
            self.visit_fields(&mut |r| match r {
                Ok((field_name, field)) => {
                    if field_name == name {
                        found = Some(field);
                    }
                }
                Err(a) => {
                    if ambiguity.is_none() {
                        ambiguity = Some(a);
                    }
                }
            });
            match (found, ambiguity) {
                (Some(field), _) => Ok(Some(field)),
                (_, Some(ambiguity)) => Err(ambiguity),
                _ => Ok(None),
            }
        }

        pub fn field_by_str(&self, name: &str) -> Result<Option<Self>, Ambiguity<Self>> {
            self.field(self.forest.grammar.cx.intern(name))
        }

        // FIXME(eddyb) maybe these should be deep?! then `ExpandedTree` shouldn't
        // be controlled using `Alias` but something else (and maybe stop using `Alias`
        // for `Repeat{Many,More}`?). This is all kinda tricky.
        pub fn as_list(mut self) -> ListHandle<'a, 'b, 'i, Pat, I> {
            assert_eq!(self.fields, None);
            let tree = match self.forest.grammar.cx[self.node.kind] {
                Rule::RepeatMany(..) => {
                    // Can't be ambiguous, due to being `Opt`.
                    self.node = self.forest.unpack_alias(self.node);
                    ExpandedTree::one_from_node(self.forest, self.node).unwrap()
                }
                Rule::RepeatMore(..) => {
                    // Might be ambiguous, fake it being a `Many`.
                    // NOTE(eddyb) the unwrap is fine because we haven't done `unpack_alias`.
                    let many = ExpandedTree::one_from_node(self.forest, self.node).unwrap();
                    Rc::new(ExpandedTree {
                        node: self.node,
                        kind: ExpandedTreeKind::Opt(Some(many)),
                    })
                }
                _ => unreachable!("not a list"),
            };
            ListHandle {
                forest: self.forest,
                tree,
            }
        }

        // FIXME(eddyb) move to `ListHandle` *or* make deep.
        fn all_lists(mut self) -> impl Iterator<Item = ListHandle<'a, 'b, 'i, Pat, I>> {
            assert_eq!(self.fields, None);
            match self.forest.grammar.cx[self.node.kind] {
                Rule::RepeatMany(..) | Rule::RepeatMore(..) => {}
                _ => unreachable!("not a list"),
            }
            self.node = self.forest.unpack_alias(self.node);
            ExpandedTree::all_from_node(self.forest, self.node)
                .into_iter()
                .map(move |tree| ListHandle {
                    forest: self.forest,
                    tree,
                })
        }
    }

    pub struct ListHandle<'a, 'b, 'i, Pat: Eq + Hash + fmt::Debug, I: Input> {
        pub forest: &'a ParseForest<'i, CxAndGrammar<'b, Pat>, I>,
        tree: Rc<ExpandedTree<'i, CxAndGrammar<'b, Pat>>>,
    }

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> Clone for ListHandle<'_, '_, '_, Pat, I> {
        fn clone(&self) -> Self {
            ListHandle {
                forest: self.forest,
                tree: self.tree.clone(),
            }
        }
    }

    impl<'a, 'b, 'i, Pat: Eq + Hash + fmt::Debug, I: Input> Iterator
        for ListHandle<'a, 'b, 'i, Pat, I>
    {
        type Item = Result<Handle<'a, 'b, 'i, Pat, I>, Ambiguity<Handle<'a, 'b, 'i, Pat, I>>>;

        fn next(&mut self) -> Option<Self::Item> {
            match &self.tree.kind {
                ExpandedTreeKind::Opt(Some(more)) => {
                    let more = self.forest.unpack_alias(more.node);
                    match ExpandedTree::one_from_node(self.forest, more) {
                        Ok(more) => self.tree = more,
                        Err(_) => {
                            return Some(Err(Ambiguity(Handle {
                                forest: self.forest,
                                node: more,
                                fields: None,
                                disambiguator: None,
                            })))
                        }
                    }
                }
                ExpandedTreeKind::Opt(None) => return None,
                _ => {}
            }
            match &self.tree.kind {
                ExpandedTreeKind::Concat([elem, tail]) => {
                    let elem = Handle {
                        forest: self.forest,
                        node: elem.node,
                        fields: None,
                        disambiguator: None,
                    };

                    self.tree = tail.clone();
                    loop {
                        match &self.tree.kind {
                            // HACK(eddyb) this only works because it's handled first
                            // in the next `<Self as Iterator>::next` call, even if
                            // it might be otherwise not the right rule.
                            ExpandedTreeKind::Opt(None) => return Some(Ok(elem)),
                            ExpandedTreeKind::Opt(Some(tail))
                            | ExpandedTreeKind::Concat([_, tail]) => {
                                self.tree = tail.clone();
                            }
                            ExpandedTreeKind::Leaf => {
                                *self = Handle {
                                    forest: self.forest,
                                    node: self.tree.node,
                                    fields: None,
                                    disambiguator: None,
                                }
                                .as_list();
                                return Some(Ok(elem));
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    impl<Pat: Eq + Hash + fmt::Debug, I: Input> fmt::Debug for ListHandle<'_, '_, '_, Pat, I> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            struct Spread<T>(T);
            impl<T: fmt::Debug> fmt::Debug for Spread<T> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.write_str("...(")?;
                    self.0.fmt(f)?;
                    f.write_str(")")
                }
            }

            let mut f = f.debug_list();
            for x in self.clone() {
                match x {
                    Ok(elem) => {
                        f.entry(&elem);
                    }
                    Err(Ambiguity(tail)) => {
                        f.entry(&Spread(tail));
                        break;
                    }
                }
            }
            f.finish()
        }
    }

    // HACK(eddyb) work around `macro_rules` not being `use`-able.
    pub use crate::__forest_dynamic_handle as handle;

    #[macro_export]
    macro_rules! __forest_dynamic_handle {
        (let _ = $handle:expr) => {
            let _ = $handle;
        };
        (let $x:ident = $handle:expr) => {
            let $x = $handle;
        };
        (let { $($field:ident),* $(,)? } = $handle:expr) => {
            let handle = &$handle;
            $(handle!(let $field = handle.field_by_str(stringify!($field)).unwrap().unwrap());)*
        };

        (if let _ = $handle:ident $body:block) => {
            match $handle { _ => $body }
        };
        (if let $x:ident = $handle:ident $body:block) => {
            match $handle { $x => $body }
        };
        (if let {} = $handle:ident $body:block) => {
            match $handle { _ => $body }
        };
        (if let { $field:ident: $pat:tt $(, $($rest:tt)*)? } = $handle:ident $body:block) => {
            if let Some(x) = $handle.field_by_str(stringify!($field)).unwrap() {
                handle!(if let $pat = x {
                    handle!(if let { $($($rest)*)? } = $handle $body)
                })
            }
        };
        (if let { $field:ident $(,)? $(, $($rest:tt)*)? } = $handle:ident $body:block) => {
            handle!(if let { $field: $field $(, $($rest)*)? } = $handle $body)
        };

        (match $handle:ident { $($pat:tt => $e:expr),* $(,)? }) => {
            loop {
                $(handle!(if let $pat = $handle {
                    break $e;
                });)*
                #[allow(unreachable_code)] {
                    unreachable!();
                }
            }
        };
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
        type Shape: Shape;

        // FIXME(eddyb) this is always `[usize; Self::Shape::STATE_LEN]`.
        // (but that doesn't work yet)
        type State: Default + AsMut<[usize]>;
    }

    pub trait FromShapeFields<'a, 'i, G: GrammarReflector, I: Input>: Sized {
        type Output;

        // FIXME(eddyb) use an array length const here instead when that works.
        type Fields: Default + AsMut<[Option<Node<'i, G>>]>;

        fn from_shape_fields(
            forest: &'a ParseForest<'i, G, I>,
            fields: Self::Fields,
        ) -> Self::Output;

        fn one(
            forest: &'a ParseForest<'i, G, I>,
            node: Node<'i, G>,
        ) -> Result<Self::Output, MoreThanOne>
        where
            Self: Shaped,
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

        fn all(
            forest: &'a ParseForest<'i, G, I>,
            node: Node<'i, G>,
        ) -> ShapedAllIter<'a, 'i, G, I, Self>
        where
            Self: Shaped,
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

    pub struct ShapedAllIter<'a, 'i, G: GrammarReflector, I: Input, T: Shaped> {
        forest: &'a ParseForest<'i, G, I>,
        node: Node<'i, G>,
        state: Option<T::State>,
    }

    impl<'a, 'i, G: GrammarReflector, I: Input, T: Shaped> Iterator for ShapedAllIter<'a, 'i, G, I, T>
    where
        T: FromShapeFields<'a, 'i, G, I>,
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

    impl<'i, G: GrammarReflector, I: Input> FromShapeFields<'_, 'i, G, I> for () {
        type Output = ();
        type Fields = [Option<Node<'i, G>>; 0];

        fn from_shape_fields(_: &ParseForest<'i, G, I>, []: Self::Fields) {}
    }

    impl<'a, 'i, G: GrammarReflector, I: Input, T> FromShapeFields<'a, 'i, G, I> for Option<T>
    where
        T: FromShapeFields<'a, 'i, G, I, Fields = [Option<Node<'i, G>>; 1]>,
    {
        type Output = Option<T::Output>;
        type Fields = [Option<Node<'i, G>>; 1];

        fn from_shape_fields(
            forest: &'a ParseForest<'i, G, I>,
            [node]: Self::Fields,
        ) -> Option<T::Output> {
            Some(T::from_shape_fields(forest, [Some(node?)]))
        }
    }

    pub struct WithShape<T, A: Shape, S: Default + AsMut<[usize]>>(PhantomVoid<(T, A, S)>);

    impl<T, A: Shape, S: Default + AsMut<[usize]>> Shaped for WithShape<T, A, S> {
        type Shape = A;
        type State = S;
    }

    impl<'a, 'i, G: GrammarReflector, I: Input, T, A, S> FromShapeFields<'a, 'i, G, I>
        for WithShape<T, A, S>
    where
        T: FromShapeFields<'a, 'i, G, I>,
        A: Shape,
        S: Default + AsMut<[usize]>,
    {
        type Output = T::Output;
        type Fields = T::Fields;

        fn from_shape_fields(forest: &'a ParseForest<'i, G, I>, fields: T::Fields) -> T::Output {
            T::from_shape_fields(forest, fields)
        }
    }

    pub trait Shape {
        const STATE_LEN: usize;

        fn init<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        );
        fn read<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        );
        fn step<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) -> bool;
    }

    pub struct Leaf(PhantomVoid<()>);

    impl Shape for Leaf {
        const STATE_LEN: usize = 0;

        fn init<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &mut [usize],
        ) {
        }
        fn read<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &[usize],
            _: &mut [Option<Node<'i, G>>],
        ) {
        }
        fn step<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &mut [usize],
        ) -> bool {
            false
        }
    }

    // FIXME(eddyb) this should be using const generics.
    pub struct Field<X: Default + AsRef<[()]>>(PhantomVoid<X>);

    impl<X: Default + AsRef<[()]>> Shape for Field<X> {
        const STATE_LEN: usize = 0;

        fn init<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &mut [usize],
        ) {
        }
        fn read<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            _: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        ) {
            fields[X::default().as_ref().len()] = Some(node);
        }
        fn step<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &mut [usize],
        ) -> bool {
            false
        }
    }

    pub struct Split<Left: Shape, Right: Shape>(PhantomVoid<(Left, Right)>);

    impl<Left: Shape, Right: Shape> Shape for Split<Left, Right> {
        const STATE_LEN: usize = 1 + Left::STATE_LEN + Right::STATE_LEN;

        fn init<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) {
            let (state_split, state) = state.split_at_mut(1);
            let state_split = &mut state_split[0];
            let (state_left, state_right) = state.split_at_mut(Left::STATE_LEN);

            let &split = forest.possibilities[&node].iter().next().unwrap();

            let (left, right) = forest.split_children(node, split);

            *state_split = split;
            Left::init(forest, left, state_left);
            Right::init(forest, right, state_right);
        }
        fn read<'i, G: GrammarReflector, I: Input>(
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
        fn step<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) -> bool {
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

    pub struct Choice<At: Shape, Cases: Shape>(PhantomVoid<(At, Cases)>);

    impl<At: Shape, Cases: Shape> Shape for Choice<At, Cases> {
        const STATE_LEN: usize = At::STATE_LEN + Cases::STATE_LEN;

        fn init<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) {
            let (state_at, state_cases) = state.split_at_mut(At::STATE_LEN);

            let &choice = forest.possibilities[&node].iter().next().unwrap();

            let child = forest.choice_child(node, choice);

            state_cases[0] = choice;
            At::init(forest, child, state_at);
            Cases::init(forest, child, state_cases);
        }
        fn read<'i, G: GrammarReflector, I: Input>(
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
        fn step<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) -> bool {
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

    pub trait CaseList: Shape {
        const LEN: usize;
    }

    pub struct CaseAppend<Prefix: CaseList, Last: Shape>(PhantomVoid<(Prefix, Last)>);

    impl<Prefix: CaseList, Last: Shape> CaseList for CaseAppend<Prefix, Last> {
        const LEN: usize = Prefix::LEN + 1;
    }

    impl<Prefix: CaseList, Last: Shape> Shape for CaseAppend<Prefix, Last> {
        const STATE_LEN: usize = {
            // HACK(eddyb) this is just `max(1 + Last::STATE_LEN, Prefix::STATE_LEN)`.
            let a = 1 + Last::STATE_LEN;
            let b = Prefix::STATE_LEN;

            let a_gt_b_mask = -((a > b) as isize) as usize;
            (a_gt_b_mask & a) | (!a_gt_b_mask & b)
        };

        fn init<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) {
            let (state_choice, state_last) = state.split_at_mut(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::init(forest, node, state);
            } else {
                Last::init(forest, node, state_last);
            }
        }
        fn read<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        ) {
            let (state_choice, state_last) = state.split_at(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::read(forest, node, state, fields);
            } else {
                Last::read(forest, node, state_last, fields);
            }
        }
        fn step<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) -> bool {
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

    impl Shape for CaseEmpty {
        const STATE_LEN: usize = 0;

        fn init<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &mut [usize],
        ) {
            unreachable!()
        }
        fn read<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &[usize],
            _: &mut [Option<Node<'i, G>>],
        ) {
            unreachable!()
        }
        fn step<'i, G: GrammarReflector, I: Input>(
            _: &ParseForest<'i, G, I>,
            _: Node<'i, G>,
            _: &mut [usize],
        ) -> bool {
            unreachable!()
        }
    }

    pub struct Opt<A: Shape>(PhantomVoid<A>);

    impl<A: Shape> Shape for Opt<A> {
        const STATE_LEN: usize = A::STATE_LEN;

        fn init<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) {
            if let Some(child) = forest.unpack_opt(node) {
                A::init(forest, child, state);
            }
        }
        fn read<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &[usize],
            fields: &mut [Option<Node<'i, G>>],
        ) {
            if let Some(child) = forest.unpack_opt(node) {
                A::read(forest, child, state, fields);
            }
        }
        fn step<'i, G: GrammarReflector, I: Input>(
            forest: &ParseForest<'i, G, I>,
            node: Node<'i, G>,
            state: &mut [usize],
        ) -> bool {
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
