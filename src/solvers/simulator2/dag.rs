use crate::solvers::{
    simulator2::{
        skyline::{Skyline, SkylineBuilder},
        Slice,
    },
    Variable, Width,
};
use hashbrown::{hash_map::Entry, HashMap};
use iset::IntervalMap;
use itertools::Itertools;
use std::{cell::Cell, fmt::Write as _};

/// All operation we are interested in keeping track of, for simulation purposes.
/// For the most part, these are copied from src/prelude/operators.egg, except
/// we exclude some operators that have a desugaring available to skip work.
///
/// No divisions for now, we do not care about those.
///
/// These are vaguely ordered in terms of how much bit-blasting based solver
/// would like them
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::solvers) enum Operation {
    Constant { table_index: usize },
    Equal,
    Concat,
    Extract(Slice),
    IfThenElse,
    Not,
    And,
    Or,
    Xor,
    Neg,
    Add,
    Ule,
    Ult,
    Sle,
    Slt,
    Mul,
    Shl,
    LShr,
    AShr,
}

impl std::fmt::Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Equal => write!(f, "equal"),
            Operation::Not => write!(f, "not"),
            Operation::And => write!(f, "and"),
            Operation::Or => write!(f, "or"),
            Operation::Xor => write!(f, "xor"),
            Operation::IfThenElse => write!(f, "ite"),
            Operation::Concat => write!(f, "concat"),
            Operation::Extract(slice) => write!(f, "extract[{}..{}]", slice.start, slice.end),
            Operation::Neg => write!(f, "neg"),
            Operation::Add => write!(f, "add"),
            Operation::Mul => write!(f, "mul"),
            Operation::Shl => write!(f, "shl"),
            Operation::LShr => write!(f, "lshr"),
            Operation::AShr => write!(f, "ashr"),
            Operation::Ule => write!(f, "ule"),
            Operation::Ult => write!(f, "ult"),
            Operation::Sle => write!(f, "sle"),
            Operation::Slt => write!(f, "slt"),
            Operation::Constant { table_index } => write!(f, "constant#{table_index}"),
        }
    }
}

enum Recipe<V: Variable> {
    Computed { op: Operation, inputs: Vec<V> },
    Slice(Slice),
}

/// Active (i.e. non-subsumed by parent UF)
struct Node<V: Variable> {
    /// Operation to compute value for the node
    recipe: Recipe<V>,
    /// Node's skyline, i.e. distance to all input slices
    skyline: Skyline,
    /// All portions of the input this node is in charge of computing
    input_portions: Vec<Slice>,
    /// Timestamp of the last recomputation of the skyline
    last_skyline_canonicalization_ts: Cell<u64>,
}

impl<V: Variable> Node<V> {
    /// Returns a slice of input matching Recipe::Slice if the (presumed canonicalized)
    /// skyline of the node matches that slice exactly. Alternatively, this means that
    /// no part of the slice is currently presumed to be computable from other parts of the
    /// input.
    fn canonical_slice(&self) -> Option<Slice> {
        let &Recipe::Slice(slice) = &self.recipe else {
            return None;
        };

        (self.skyline.updates == vec![(slice.start, 1), (slice.end, 0)]).then_some(slice)
    }
}

/// Mapping for the node.
enum NodeOrRedirect<V: Variable> {
    Active(Node<V>),
    SubsumedBy(Cell<V>),
}

impl<V: Variable> NodeOrRedirect<V> {
    #[track_caller]
    fn as_active_ref(&self) -> &Node<V> {
        match self {
            NodeOrRedirect::Active(node) => node,
            _ => unreachable!(),
        }
    }

    #[track_caller]
    fn as_active_mut(&mut self) -> &mut Node<V> {
        match self {
            NodeOrRedirect::Active(node) => node,
            _ => unreachable!(),
        }
    }

    #[track_caller]
    fn active(self) -> Node<V> {
        match self {
            NodeOrRedirect::Active(node) => node,
            _ => unreachable!(),
        }
    }
}

/// Map that keeps track of slices that are computable
type ComputableSlices<V> = IntervalMap<Width, V>;

pub(in crate::solvers) struct Dag<V: Variable> {
    /// For each e-class, we track how it's meant to be computed
    mappings: HashMap<V, NodeOrRedirect<V>>,
    /// Slices of input which can be computed
    computable_slices: ComputableSlices<V>,
    /// Timestamp of the last update which can trigger re-canonicalization
    last_update_ts: u64,
    /// Input e-classes by name, and their allocated input ranges
    input_slices: HashMap<String, Slice>,
    /// Size of the input bitvector. This includes computable input portions
    input_len: Width,
}

impl<V: Variable> Default for Dag<V> {
    fn default() -> Self {
        Self {
            mappings: Default::default(),
            computable_slices: Default::default(),
            last_update_ts: 0,
            input_slices: Default::default(),
            input_len: 0,
        }
    }
}

mod skyline_canon {
    use super::*;

    trait SplitByComputability<V> {
        /// Given a slice of input, split it into smaller ones, some of which
        /// are computable from others (not-neccessarily within this slice).
        /// Call the first function for non-computable ones and the second one
        /// for what can be computed.
        ///
        /// computable function can also optionally return a new value to put
        /// in the slice map
        fn split_by_computability(
            &mut self,
            slice: Slice,
            non_computable: impl FnMut(Slice),
            computable: impl FnMut(V) -> V,
        );
    }

    impl<V: Variable> SplitByComputability<V> for ComputableSlices<V> {
        fn split_by_computability(
            &mut self,
            slice: Slice,
            mut on_non_computable: impl FnMut(Slice),
            mut on_computable: impl FnMut(V) -> V,
        ) {
            let mut non_computable_range_start = slice.start;

            for (computable_interval, value) in self.iter_mut(slice.start..slice.end) {
                if computable_interval.start > non_computable_range_start {
                    on_non_computable(Slice {
                        start: non_computable_range_start,
                        end: computable_interval.start,
                    })
                }
                non_computable_range_start = computable_interval.end;
                let replacement_value = on_computable(*value);
                *value = replacement_value;
            }

            if non_computable_range_start < slice.end {
                on_non_computable(Slice {
                    start: non_computable_range_start,
                    end: slice.end,
                })
            }
        }
    }

    struct CanonicalizationWorklist<V: Variable> {
        pre: Vec<V>,
        post: Vec<(SkylineBuilder, HashMap<V, usize>, V)>,
    }

    impl<V: Variable> Default for CanonicalizationWorklist<V> {
        fn default() -> Self {
            Self {
                pre: Default::default(),
                post: Default::default(),
            }
        }
    }

    impl<V: Variable> Dag<V> {
        /// Prepare to canonicalize supplied skyline. This can queue canonicalization of skylines of other values in the graph.
        /// If None is returned, existing skyline can be used as is.
        fn schedule_pre_steps(
            computable_slices: &mut ComputableSlices<V>,
            mappings: &HashMap<V, NodeOrRedirect<V>>,
            worklist: &mut CanonicalizationWorklist<V>,
            skyline: &Skyline,
        ) -> Option<(SkylineBuilder, HashMap<V, usize>)> {
            let mut next_to_canonicalize = HashMap::new();
            let mut skyline_builder = SkylineBuilder::default();

            for (slice, height) in skyline.non_zero_height_slices_iter() {
                computable_slices.split_by_computability(
                    slice,
                    |non_computable_slice| {
                        // Since slice is non-computable, it's height stays the same
                        skyline_builder.add_slice(non_computable_slice, height);
                    },
                    |computable_dep| {
                        let computable_dep = Self::find_static(mappings, computable_dep);
                        worklist.pre.push(computable_dep);

                        // For computable values, we keep track of the highest possible height difference
                        let entry = next_to_canonicalize.entry(computable_dep).or_default();
                        *entry = std::cmp::max(*entry, height);

                        computable_dep
                    },
                );
            }

            (!next_to_canonicalize.is_empty()).then_some((skyline_builder, next_to_canonicalize))
        }

        fn schedule_pre_and_post_steps(
            computable_slices: &mut ComputableSlices<V>,
            mappings: &HashMap<V, NodeOrRedirect<V>>,
            worklist: &mut CanonicalizationWorklist<V>,
            skyline: &Skyline,
            value: V,
        ) {
            if let Some((skyline_builder, computable_deps)) =
                Self::schedule_pre_steps(computable_slices, mappings, worklist, skyline)
            {
                worklist
                    .post
                    .push((skyline_builder, computable_deps, value));
            }
        }

        /// Reassemble skyline after pre-pass
        fn run_post_step(
            mappings: &HashMap<V, NodeOrRedirect<V>>,
            mut skyline_builder: SkylineBuilder,
            computable_deps: HashMap<V, usize>,
        ) -> Skyline {
            for (computed_value, height_delta) in computable_deps {
                let computed_node = mappings[&computed_value].as_active_ref();

                for (computed_node_dep_slice, computed_node_dep_height) in
                    computed_node.skyline.non_zero_height_slices_iter()
                {
                    skyline_builder.add_slice(
                        computed_node_dep_slice,
                        computed_node_dep_height + height_delta,
                    );
                }
            }

            skyline_builder.build()
        }

        /// Empty canonicalization worklists by running pre/post until both worklists are exhausted
        fn canonicalization_fixpoint(&mut self, worklist: &mut CanonicalizationWorklist<V>) {
            while let Some(v) = worklist.pre.pop() {
                let node = self.mappings[&v].as_active_ref();
                if node.last_skyline_canonicalization_ts.get() == self.last_update_ts {
                    continue;
                }

                // Prevent further encounters of this vertex from doing any work
                node.last_skyline_canonicalization_ts
                    .set(self.last_update_ts);

                if let Some((skyline_builder, computable_deps)) = Self::schedule_pre_steps(
                    &mut self.computable_slices,
                    &self.mappings,
                    worklist,
                    &node.skyline,
                ) {
                    worklist.post.push((skyline_builder, computable_deps, v));
                }
            }

            while let Some((skyline_builder, computable_deps, v)) = worklist.post.pop() {
                let skyline = Self::run_post_step(&self.mappings, skyline_builder, computable_deps);
                self.mappings.get_mut(&v).unwrap().as_active_mut().skyline = skyline;
            }
        }

        /// Ensures that skyline for `v` is canonical. Returns a canonical ID of the e-class passed in
        pub(super) fn canonicalize_skyline_for(&mut self, v: V) -> V {
            let v = Self::find_static(&self.mappings, v);
            let node = self.mappings[&v].as_active_ref();
            // Check if skyline for the value has already been canonicalized
            if node.last_skyline_canonicalization_ts.get() == self.last_update_ts {
                return v;
            }

            let mut worklist = Default::default();
            Self::schedule_pre_and_post_steps(
                &mut self.computable_slices,
                &self.mappings,
                &mut worklist,
                &node.skyline,
                v,
            );
            self.canonicalization_fixpoint(&mut worklist);

            v
        }

        /// Canonicalize skyline that isn't associated with any value
        pub(super) fn canonicalize_skyline(&mut self, skyline: Skyline) -> Skyline {
            let mut worklist = Default::default();
            let Some((skyline_builder, computable_deps)) = Self::schedule_pre_steps(
                &mut self.computable_slices,
                &self.mappings,
                &mut worklist,
                &skyline,
            ) else {
                return skyline;
            };
            self.canonicalization_fixpoint(&mut worklist);

            Self::run_post_step(&self.mappings, skyline_builder, computable_deps)
        }
    }
}

impl<V: Variable> Dag<V> {
    fn find_static(mappings: &HashMap<V, NodeOrRedirect<V>>, mut variable: V) -> V {
        let mut result = variable;
        while let Some(NodeOrRedirect::SubsumedBy(cell)) = mappings.get(&result) {
            result = cell.get();
        }

        while let Some(NodeOrRedirect::SubsumedBy(cell)) = mappings.get(&variable) {
            variable = cell.get();
            cell.set(result);
        }

        result
    }

    fn find(&self, variable: V) -> V {
        Self::find_static(&self.mappings, variable)
    }

    // Merge two DAG nodes together (assuming canonicalized skylines). The output is needed in case one of the nodes is a canonical input, in which case we would like to introduce a functional dependency.
    fn merge_nodes(
        &mut self,
        mut old_node: Node<V>,
        mut new_node: Node<V>,
        output_eclass: V,
    ) -> Node<V> {
        let (old_higher_up, new_higher_up) = old_node.skyline.compare(&new_node.skyline);
        let mut input_portions = std::mem::take(&mut old_node.input_portions);
        input_portions.append(&mut new_node.input_portions);

        let pick_old_as_active = match (old_higher_up, new_higher_up) {
            (true, false) => false, // old is higher than new, pick new as the replacement,
            (false, true) => true,  // new is higher than old, pick old as the replacement,
            (false, false) => true, // heights match for all slices, it doesn't matter which one we pick
            (true, true) => {
                // if there is no overlap at all, one might be a canonical slice, in which case we want to pick another

                let (pick_old, canonical_slice) =
                    if let Some(canonical_slice) = new_node.canonical_slice() {
                        (true, Some(canonical_slice))
                    } else if let Some(canonical_slice) = old_node.canonical_slice() {
                        (false, Some(canonical_slice))
                    } else {
                        (false, None)
                    };

                if let Some(slice) = canonical_slice {
                    self.computable_slices
                        .insert(slice.start..slice.end, output_eclass);
                    input_portions.push(slice);
                    self.last_update_ts += 1;
                }

                pick_old
            }
        };

        Node {
            input_portions,
            ..if pick_old_as_active {
                old_node
            } else {
                new_node
            }
        }
    }

    // Union two e-classes
    pub(in crate::solvers::simulator2) fn union(&mut self, old: V, new: V) {
        let old = self.canonicalize_skyline_for(old);

        let old_node = self.mappings.remove(&old).unwrap().active();

        // Uhh, I couldn't figure out how to do this with entry() or even remove(). The tricky
        // bit is that we have to recanonicalize right in the middle.
        let new_node = if self.mappings.contains_key(&new) {
            self.canonicalize_skyline_for(new);
            self.mappings
                .remove(&new)
                .map(NodeOrRedirect::active)
                .unwrap()
        } else {
            self.mappings.insert(new, NodeOrRedirect::Active(old_node));
            self.mappings
                .insert(old, NodeOrRedirect::SubsumedBy(new.into()));
            return;
        };

        let active_node = self.merge_nodes(old_node, new_node, new);

        self.mappings
            .insert(old, NodeOrRedirect::SubsumedBy(new.into()));
        self.mappings
            .insert(new, NodeOrRedirect::Active(active_node));
    }

    // Add a new node for the e-class
    fn add_node(&mut self, new_node: Node<V>, output: V) {
        if !self.mappings.contains_key(&output) {
            self.mappings
                .insert(output, NodeOrRedirect::Active(new_node));
            return;
        }

        let output = self.canonicalize_skyline_for(output);
        let node_to_insert = if let Some(output_node) = self.mappings.remove(&output) {
            let output_node = output_node.active();
            self.merge_nodes(output_node, new_node, output)
        } else {
            new_node
        };

        self.mappings
            .insert(output, NodeOrRedirect::Active(node_to_insert));
    }

    // Add a new equation for the e-class
    pub(in crate::solvers::simulator2) fn add_equation(
        &mut self,
        op: Operation,
        mut inputs: Vec<V>,
        output: V,
    ) {
        // Compute a skyline for the new expression
        let mut skyline_builder = SkylineBuilder::default();
        for input in inputs.iter_mut() {
            *input = self.canonicalize_skyline_for(*input);
            let input = self.mappings[input].as_active_ref();
            skyline_builder.add_skyline(&input.skyline, 1);
        }
        let skyline = skyline_builder.build();

        let new_node = Node {
            recipe: Recipe::Computed { op, inputs },
            skyline,
            input_portions: vec![],
            last_skyline_canonicalization_ts: self.last_update_ts.into(),
        };

        self.add_node(new_node, output);
    }

    /// Add input slice mapping
    fn add_input_slice(&mut self, output: V, slice: Slice) {
        let skyline = self.canonicalize_skyline(slice.into());

        self.add_node(
            Node {
                recipe: Recipe::Slice(slice),
                skyline,
                input_portions: vec![],
                last_skyline_canonicalization_ts: self.last_update_ts.into(),
            },
            output,
        );
    }

    /// Add an extract node. This behaves differently on slices
    pub(in crate::solvers::simulator2) fn add_extract(
        &mut self,
        input: V,
        slice: Slice,
        output: V,
    ) {
        let input = self.find(input);
        let input_node = self.mappings[&input].as_active_ref();

        if let Recipe::Slice(input_slice) = input_node.recipe {
            let subslice = input_slice.subslice(slice);
            self.add_input_slice(output, subslice);
            return;
        }

        // Defer to normal, computed extract
        self.add_equation(Operation::Extract(slice), vec![input], output);
    }

    /// Add an input e-class
    pub(in crate::solvers::simulator2) fn declare_input(
        &mut self,
        input: V,
        width: Width,
        name: String,
    ) {
        match self.input_slices.entry(name) {
            Entry::Occupied(_) => {}
            Entry::Vacant(vacant_entry) => {
                let new_input_len = self.input_len + width;
                let slice = (self.input_len..new_input_len).into();
                self.input_len = new_input_len;
                vacant_entry.insert(slice);

                self.add_node(
                    Node {
                        recipe: Recipe::Slice(slice),
                        skyline: slice.into(),
                        input_portions: vec![],
                        last_skyline_canonicalization_ts: self.last_update_ts.into(),
                    },
                    input,
                );
            }
        }
    }

    /// Build a topological order for the DAG and canonicalize all nodes in the process.
    /// This only returns canonical elements and makes sure to purge all non-canonical
    /// elements from the map.
    pub(in crate::solvers::simulator2) fn build_topo_order(&mut self) -> Vec<V> {
        let all_eclasses: Vec<V> = self.mappings.keys().cloned().collect();
        let mut eclasses_with_heights = vec![];

        for eclass in all_eclasses.iter() {
            let eclass = self.canonicalize_skyline_for(*eclass);
            let node = self.mappings.get_mut(&eclass).unwrap().as_active_mut();
            let max_height = node.skyline.max_height();

            let mut recipe = std::mem::replace(
                &mut node.recipe,
                Recipe::Computed {
                    op: Operation::Add,
                    inputs: vec![],
                },
            );

            match &mut recipe {
                Recipe::Computed { inputs, .. } => {
                    for input in inputs.iter_mut() {
                        *input = self.find(*input);
                    }
                }
                Recipe::Slice(_) => {}
            }

            self.mappings
                .get_mut(&eclass)
                .unwrap()
                .as_active_mut()
                .recipe = recipe;

            eclasses_with_heights.push((max_height, eclass));
        }

        for (_, value) in self.computable_slices.iter_mut(0..) {
            *value = Self::find_static(&self.mappings, *value);
        }

        // Remove all non-canonical classes from the mapping
        for eclass in all_eclasses {
            match self.mappings.entry(eclass) {
                Entry::Occupied(occupied_entry) => {
                    if let NodeOrRedirect::SubsumedBy(_) = occupied_entry.get() {
                        occupied_entry.remove();
                    }
                }
                Entry::Vacant(_) => {}
            }
        }

        eclasses_with_heights
            .iter()
            .sorted()
            .map(|(_, value)| *value)
            .dedup()
            .collect()
    }

    /// Build a summary of the DAG in text format. Used for expect tests
    pub(in crate::solvers::simulator2) fn summary(&mut self) -> String {
        let mut result = String::new();
        for value in self.build_topo_order() {
            let node = self.mappings[&value].as_active_ref();

            for input_portion in node.input_portions.iter() {
                write!(
                    &mut result,
                    "input[{}..{}] = ",
                    input_portion.start, input_portion.end
                )
                .unwrap();
            }

            write!(&mut result, "{} = ", value.show()).unwrap();

            match &node.recipe {
                Recipe::Computed { op, inputs } => {
                    write!(
                        &mut result,
                        "{op}({}) ",
                        inputs
                            .iter()
                            .map(|input| self.find(*input).show())
                            .join(", ")
                    )
                    .unwrap();
                }
                Recipe::Slice(slice) => {
                    write!(&mut result, "input[{}..{}] ", slice.start, slice.end).unwrap();
                }
            }

            writeln!(
                &mut result,
                "(skyline: [{}])",
                node.skyline
                    .non_zero_height_slices_iter()
                    .map(|(slice, height)| format!("({}..{}, {})", slice.start, slice.end, height))
                    .join(", ")
            )
            .unwrap();
        }

        for (slice, value) in self.computable_slices.iter(0..) {
            writeln!(
                &mut result,
                "input[{}..{}] is computed by {}",
                slice.start,
                slice.end,
                value.show()
            )
            .unwrap();
        }

        result
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use expect_test::{expect, Expect};

    impl<V: Variable> Dag<V> {
        fn expect(&mut self, expect: Expect) {
            expect.assert_eq(&self.summary());
        }
    }

    #[test]
    fn test_input_slice_fdewp() {
        let mut dag: Dag<u64> = Dag::default();

        dag.declare_input(1, 64, "state".into());
        dag.add_extract(1, (0..32).into(), 2);
        dag.add_extract(1, (32..64).into(), 3);
        dag.add_equation(Operation::Not, vec![2], 3);

        dag.expect(expect![[r#"
            v2 = input[0..32] (skyline: [(0..32, 1)])
            input[32..64] = v3 = not(v2) (skyline: [(0..32, 2)])
            v1 = input[0..64] (skyline: [(0..32, 3)])
            input[32..64] is computed by v3
        "#]]);
    }

    #[test]
    fn test_add_or_and_union() {
        let mut dag: Dag<u64> = Dag::default();

        dag.declare_input(1, 512, "a".into());
        dag.declare_input(2, 512, "b".into());

        dag.add_equation(Operation::And, vec![1, 2], 3); // (and a b)
        dag.add_equation(Operation::Or, vec![1, 2], 4); // (or a b)
        dag.add_equation(Operation::Add, vec![3, 4], 5); // (add (and a b) (or a b))
        dag.add_equation(Operation::Add, vec![1, 2], 6); // (add a b)

        dag.expect(expect![[r#"
            v1 = input[0..512] (skyline: [(0..512, 1)])
            v2 = input[512..1024] (skyline: [(512..1024, 1)])
            v3 = and(v1, v2) (skyline: [(0..1024, 2)])
            v4 = or(v1, v2) (skyline: [(0..1024, 2)])
            v6 = add(v1, v2) (skyline: [(0..1024, 2)])
            v5 = add(v3, v4) (skyline: [(0..1024, 3)])
        "#]]);

        dag.union(6, 5);
        dag.expect(expect![[r#"
            v1 = input[0..512] (skyline: [(0..512, 1)])
            v2 = input[512..1024] (skyline: [(512..1024, 1)])
            v3 = and(v1, v2) (skyline: [(0..1024, 2)])
            v4 = or(v1, v2) (skyline: [(0..1024, 2)])
            v5 = add(v1, v2) (skyline: [(0..1024, 2)])
        "#]]);

        dag.union(1, 2);
        dag.expect(expect![[r#"
            input[512..1024] = v2 = input[0..512] (skyline: [(0..512, 1)])
            v3 = and(v2, v2) (skyline: [(0..512, 3)])
            v4 = or(v2, v2) (skyline: [(0..512, 3)])
            v5 = add(v2, v2) (skyline: [(0..512, 3)])
            input[512..1024] is computed by v2
        "#]]);
    }

    #[test]
    fn test_if_conversion_equivalent() {
        // Could you tell this was made by ChatGPT?
        let mut dag: Dag<u64> = Dag::default();

        // Declare enough input bits: cond + 4 values + 6 intermediates = 321 bits
        dag.declare_input(1, 321, "state".into());

        dag.add_extract(1, (0..1).into(), 2); // cond
        dag.add_extract(1, (1..33).into(), 3); // a
        dag.add_extract(1, (33..65).into(), 4); // b
        dag.add_extract(1, (65..97).into(), 5); // c
        dag.add_extract(1, (97..129).into(), 6); // d

        // a + b → 7
        dag.add_equation(Operation::Add, vec![3, 4], 7);
        // c + d → 8
        dag.add_equation(Operation::Add, vec![5, 6], 8);

        // if cond then (a + b) else (c + d) → 9
        dag.add_equation(Operation::IfThenElse, vec![2, 7, 8], 9);

        // if cond then a else c → 10
        dag.add_equation(Operation::IfThenElse, vec![2, 3, 5], 10);

        // if cond then b else d → 11
        dag.add_equation(Operation::IfThenElse, vec![2, 4, 6], 11);

        // add results of the two ifs → 12
        dag.add_equation(Operation::Add, vec![10, 11], 12);

        dag.add_extract(1, (129..161).into(), 7); // a + b
        dag.add_extract(1, (161..193).into(), 8); // c + d
        dag.add_extract(1, (193..225).into(), 9); // if (a + b, c + d)
        dag.add_extract(1, (225..257).into(), 10); // if a, c
        dag.add_extract(1, (257..289).into(), 11); // if b, d
        dag.add_extract(1, (289..321).into(), 12); // sum of ifs

        dag.expect(expect![[r#"
            v2 = input[0..1] (skyline: [(0..1, 1)])
            v3 = input[1..33] (skyline: [(1..33, 1)])
            v4 = input[33..65] (skyline: [(33..65, 1)])
            v5 = input[65..97] (skyline: [(65..97, 1)])
            v6 = input[97..129] (skyline: [(97..129, 1)])
            input[129..161] = v7 = add(v3, v4) (skyline: [(1..65, 2)])
            input[161..193] = v8 = add(v5, v6) (skyline: [(65..129, 2)])
            input[225..257] = v10 = ite(v2, v3, v5) (skyline: [(0..33, 2), (65..97, 2)])
            input[257..289] = v11 = ite(v2, v4, v6) (skyline: [(0..1, 2), (33..65, 2), (97..129, 2)])
            input[193..225] = v9 = ite(v2, v7, v8) (skyline: [(0..1, 2), (1..129, 3)])
            input[289..321] = v12 = add(v10, v11) (skyline: [(0..129, 3)])
            v1 = input[0..321] (skyline: [(0..129, 4)])
            input[129..161] is computed by v7
            input[161..193] is computed by v8
            input[193..225] is computed by v9
            input[225..257] is computed by v10
            input[257..289] is computed by v11
            input[289..321] is computed by v12
        "#]]);
    }

    #[test]
    fn dep_cycle() {
        let mut dag: Dag<u64> = Dag::default();

        dag.declare_input(1, 32, "a".into());
        dag.declare_input(2, 32, "b".into());

        dag.add_equation(Operation::Not, vec![1], 2);
        dag.add_equation(Operation::Not, vec![2], 1);

        dag.expect(expect![[r#"
            v1 = input[0..32] (skyline: [(0..32, 1)])
            input[32..64] = v2 = not(v1) (skyline: [(0..32, 2)])
            input[32..64] is computed by v2
        "#]]);
    }

    #[test]
    fn test_fdep_slice_cycle() {
        let mut dag: Dag<u64> = Dag::default();

        dag.declare_input(1, 64, "state".into());
        dag.add_extract(1, (0..32).into(), 2);
        dag.add_extract(1, (32..64).into(), 3);

        dag.add_equation(Operation::Not, vec![2], 3);
        dag.add_equation(Operation::Not, vec![3], 2);

        dag.expect(expect![[r#"
            v2 = input[0..32] (skyline: [(0..32, 1)])
            input[32..64] = v3 = not(v2) (skyline: [(0..32, 2)])
            v1 = input[0..64] (skyline: [(0..32, 3)])
            input[32..64] is computed by v3
        "#]]);
    }

    #[test]
    fn test_nested_extract() {
        let mut dag: Dag<u64> = Dag::default();

        dag.declare_input(1, 64, "state".into());
        dag.add_extract(1, (0..32).into(), 2);
        dag.add_extract(2, (0..16).into(), 3);

        dag.add_extract(1, (32..48).into(), 4);
        dag.add_equation(Operation::Not, vec![4], 5);
        dag.add_equation(Operation::Neg, vec![5], 6);

        dag.union(6, 3);
        dag.expect(expect![[r#"
            v4 = input[32..48] (skyline: [(32..48, 1)])
            v5 = not(v4) (skyline: [(32..48, 2)])
            input[0..16] = v3 = neg(v5) (skyline: [(32..48, 3)])
            v1 = input[0..64] (skyline: [(16..32, 1), (32..48, 4), (48..64, 1)])
            v2 = input[0..32] (skyline: [(16..32, 1), (32..48, 4)])
            input[0..16] is computed by v3
        "#]]);
    }

    #[test]
    fn test_nested_extract_fdep_cycle() {
        let mut dag: Dag<u64> = Dag::default();

        dag.declare_input(1, 64, "state".into());
        dag.add_extract(1, (0..32).into(), 2);
        dag.add_extract(2, (0..16).into(), 3);

        dag.add_extract(1, (32..48).into(), 4);
        dag.add_equation(Operation::Not, vec![4], 5);

        dag.add_extract(1, (16..32).into(), 6);

        dag.add_equation(Operation::Neg, vec![5], 7);

        dag.add_equation(Operation::Not, vec![6], 8);
        dag.union(7, 3);
        dag.union(8, 4);

        dag.expect(expect![[r#"
            v6 = input[16..32] (skyline: [(16..32, 1)])
            input[32..48] = v4 = not(v6) (skyline: [(16..32, 2)])
            v5 = not(v4) (skyline: [(16..32, 4)])
            input[0..16] = v3 = neg(v5) (skyline: [(16..32, 5)])
            v1 = input[0..64] (skyline: [(16..32, 6), (48..64, 1)])
            v2 = input[0..32] (skyline: [(16..32, 6)])
            input[0..16] is computed by v3
            input[32..48] is computed by v4
        "#]]);
    }

    #[test]
    fn test_partial_computability_split() {
        // Another ChatGPT made test
        let mut dag: Dag<u64> = Dag::default();

        // Declare a 32-bit input
        dag.declare_input(1, 32, "state".into());
        // Extract bits 0..16 and compute NOT over them ⇒ v3 computes [0..16]
        dag.add_extract(1, (0..16).into(), 2);
        dag.add_equation(Operation::Not, vec![2], 3);
        // Extract the remaining bits 16..32 as v4
        dag.add_extract(1, (16..32).into(), 4);
        // Now add across the full 0..32 range, mixing computed (v3) & raw (v4)
        dag.add_equation(Operation::Add, vec![3, 4], 5);

        dag.expect(expect![[r#"
            v1 = input[0..32] (skyline: [(0..32, 1)])
            v2 = input[0..16] (skyline: [(0..16, 1)])
            v4 = input[16..32] (skyline: [(16..32, 1)])
            v3 = not(v2) (skyline: [(0..16, 2)])
            v5 = add(v3, v4) (skyline: [(0..16, 3), (16..32, 2)])
        "#]]);
    }
}
