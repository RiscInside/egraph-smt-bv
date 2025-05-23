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

#[derive(Debug)]
enum Recipe<V: Variable> {
    Computed { op: Operation, inputs: Vec<Cell<V>> },
    Slice(Slice),
    NonComputable,
}

/// Active (i.e. non-subsumed by parent UF) node in the DAG. This roughly corresponds to e-graph e-nodes,
/// except we only keep cheapest nodes around.
#[derive(Debug)]
struct Node<V: Variable> {
    /// Node's output. For self.mappings[v], this would be equal to a canonical representative of `v`.
    /// Generally speaking we are fine with using non-canonical nodes - non-incremental pass would make
    /// sure that we are using a correct node.
    output: Cell<V>,
    /// Operation to compute value for the node.
    recipe: Recipe<V>,
    /// Node's skyline, i.e. distance to all input slices. This is used to infer topological ordering
    /// on nodes and aliasing checks for functional dependency introduction.
    skyline: Skyline,
    /// Timestamp of the last recomputation of the skyline. This field is used to skip repeated
    /// recanonicalizations, which can be quite expensive.
    last_skyline_canonicalization_ts: Cell<u64>,
    /// All portins of input this node is in charge of computing. This vector should be empty for
    /// removed or non-canonical ndoes
    input_portions: Vec<Slice>,
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

    fn non_computable(skyline: Skyline, output: V, ts: u64) -> Self {
        Self {
            output: output.into(),
            recipe: Recipe::NonComputable,
            skyline,
            last_skyline_canonicalization_ts: ts.into(),
            input_portions: vec![],
        }
    }
}

/// Map that keeps track of slices that are computable
type ComputableSlices<V> = IntervalMap<Width, V>;

pub(in crate::solvers) struct Dag<V: Variable> {
    /// E-class ID to matching node map.
    mappings: HashMap<V, Node<V>>,
    /// Slices of input which can be computed
    computable_slices: ComputableSlices<V>,
    /// Timestamp of the last update which can trigger re-canonicalization
    last_update_ts: u64,
    /// Input e-classes by name, and their allocated input ranges
    input_slices: HashMap<String, Slice>,
    /// Size of the input bitvector. This includes computable input portions
    input_len: Width,
    /// Alternative nodes, waiting to be processed. Since nodes store output inside them,
    /// we know what value they are supposed to be computing value for
    postponed: Vec<Node<V>>,
}

impl<V: Variable> Default for Dag<V> {
    fn default() -> Self {
        Self {
            mappings: Default::default(),
            computable_slices: Default::default(),
            last_update_ts: 0,
            input_slices: Default::default(),
            input_len: 0,
            postponed: vec![],
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
            computable: impl FnMut(V),
        );
    }

    impl<V: Variable> SplitByComputability<V> for ComputableSlices<V> {
        fn split_by_computability(
            &mut self,
            slice: Slice,
            mut on_non_computable: impl FnMut(Slice),
            mut on_computable: impl FnMut(V),
        ) {
            let mut non_computable_range_start = slice.start;

            for (computable_interval, value) in self.iter(slice.start..slice.end) {
                if computable_interval.start > non_computable_range_start {
                    on_non_computable(Slice {
                        start: non_computable_range_start,
                        end: computable_interval.start,
                    })
                }
                non_computable_range_start = computable_interval.end;
                on_computable(*value);
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
                        worklist.pre.push(computable_dep);

                        // For computable values, we keep track of the highest possible height difference
                        let entry = next_to_canonicalize.entry(computable_dep).or_default();
                        *entry = std::cmp::max(*entry, height);
                    },
                );
            }

            (!next_to_canonicalize.is_empty()).then_some((skyline_builder, next_to_canonicalize))
        }

        fn schedule_pre_and_post_steps(
            computable_slices: &mut ComputableSlices<V>,
            worklist: &mut CanonicalizationWorklist<V>,
            skyline: &Skyline,
            value: V,
        ) {
            if let Some((skyline_builder, computable_deps)) =
                Self::schedule_pre_steps(computable_slices, worklist, skyline)
            {
                worklist
                    .post
                    .push((skyline_builder, computable_deps, value));
            }
        }

        /// Reassemble skyline after pre-pass
        fn run_post_step(
            mappings: &HashMap<V, Node<V>>,
            mut skyline_builder: SkylineBuilder,
            computable_deps: HashMap<V, usize>,
        ) -> Skyline {
            for (computed_value, height_delta) in computable_deps {
                let computed_node = &mappings[&computed_value];

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
                let node = &self.mappings[&v];
                if node.last_skyline_canonicalization_ts.get() == self.last_update_ts {
                    continue;
                }

                // Prevent further encounters of this vertex from doing any work
                node.last_skyline_canonicalization_ts
                    .set(self.last_update_ts);

                if let Some((skyline_builder, computable_deps)) =
                    Self::schedule_pre_steps(&mut self.computable_slices, worklist, &node.skyline)
                {
                    worklist.post.push((skyline_builder, computable_deps, v));
                }
            }

            while let Some((skyline_builder, computable_deps, v)) = worklist.post.pop() {
                let skyline = Self::run_post_step(&self.mappings, skyline_builder, computable_deps);
                self.mappings.get_mut(&v).unwrap().skyline = skyline;
            }
        }

        /// Ensures that skyline for `v` is canonical. Returns a canonical ID of the e-class passed in
        pub(super) fn canonicalize_skyline_for(&mut self, v: V) -> V {
            let v = Self::find_static(&self.mappings, v);
            let node = &self.mappings[&v];
            // Check if skyline for the value has already been canonicalized
            if node.last_skyline_canonicalization_ts.get() == self.last_update_ts {
                return v;
            }

            let mut worklist = Default::default();
            Self::schedule_pre_and_post_steps(
                &mut self.computable_slices,
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
            let Some((skyline_builder, computable_deps)) =
                Self::schedule_pre_steps(&mut self.computable_slices, &mut worklist, &skyline)
            else {
                return skyline;
            };
            self.canonicalization_fixpoint(&mut worklist);

            Self::run_post_step(&self.mappings, skyline_builder, computable_deps)
        }
    }
}

impl<V: Variable> Dag<V> {
    fn find_static(mappings: &HashMap<V, Node<V>>, mut variable: V) -> V {
        let mut result = variable;
        while let Some(Node { output, .. }) = mappings.get(&result) {
            if output.get() == result {
                break;
            }
            result = output.get();
        }

        while let Some(Node { output, .. }) = mappings.get(&variable) {
            if output.get() == result {
                break;
            }
            variable = output.get();
            output.set(result);
        }

        result
    }

    fn find(&self, variable: V) -> V {
        Self::find_static(&self.mappings, variable)
    }

    // Attempt to merge two DAG nodes together (assuming canonicalized skylines). Two DAG nodes are merged if we know for sure that no
    // extra input functional dependency will affect evaluation ordering between them.
    #[allow(clippy::result_large_err)]
    fn merge_nodes(
        &mut self,
        mut old_node: Node<V>,
        mut new_node: Node<V>,
    ) -> Result<Node<V>, (Node<V>, Node<V>)> {
        let (old_higher_up, new_higher_up) = old_node.skyline.compare(&new_node.skyline);
        let mut input_portions = std::mem::take(&mut old_node.input_portions);
        input_portions.append(&mut new_node.input_portions);

        let pick_old_as_active = match (old_higher_up, new_higher_up) {
            (true, false) => false, // old is higher than new, pick new as the replacement,
            (false, true) => true,  // new is higher than old, pick old as the replacement,
            (false, false) => true, // heights match for all slices, it doesn't matter which one we pick - both nodes can be evaluated in any order
            (true, true) => {
                // if both nodes have segments they are higher on, we don't know which one will be evaluated first in the future - this would
                // depend on new input fdeps introduced in the future.
                //
                // However, if one of the nodes is a canonical input slice, we can introduce a new fdep, so that's nice
                if let Some((canonical_slice, pick_old)) = new_node
                    .canonical_slice()
                    .map(|slice| (slice, true))
                    .or_else(|| old_node.canonical_slice().map(|slice| (slice, false)))
                {
                    self.computable_slices.insert(
                        canonical_slice.start..canonical_slice.end,
                        old_node.output.get(),
                    );
                    input_portions.push(canonical_slice);
                    self.last_update_ts += 1;
                    pick_old
                } else {
                    // We can't introduce a new fdep here, so just accept the fact that two nodes can't be merged and defer to non-incremental pass.
                    // For now, decide arbitrarily that new node will be the representative for output and old_node will go into postponed list

                    new_node.input_portions = input_portions;
                    return Err((old_node, new_node));
                }
            }
        };

        let (active_node, _) = if pick_old_as_active {
            (old_node, new_node)
        } else {
            (new_node, old_node)
        };

        Ok(Node {
            input_portions,
            ..active_node
        })
    }

    // Union two e-classes
    pub(in crate::solvers::simulator2) fn union(&mut self, old: V, new: V) {
        let old = self.canonicalize_skyline_for(old);

        let old_node = self.mappings.remove(&old).unwrap();
        old_node.output.set(new);

        // Uhh, I couldn't figure out how to do this with entry() or even remove(). The tricky
        // bit is that we have to recanonicalize right in the middle.
        let new_node = if self.mappings.contains_key(&new) {
            self.canonicalize_skyline_for(new);
            self.mappings.remove(&new).unwrap()
        } else {
            let skyline = old_node.skyline.clone();
            self.mappings.insert(new, old_node);
            // We need to keep some node for `old` as a reference point for skyline computations.
            self.mappings
                .insert(old, Node::non_computable(skyline, new, self.last_update_ts));
            return;
        };

        match self.merge_nodes(old_node, new_node) {
            Ok(result) => {
                self.mappings.insert(
                    old,
                    Node::non_computable(result.skyline.clone(), new, self.last_update_ts),
                );
                self.mappings.insert(new, result);
            }
            Err((old_node, new_node)) => {
                self.mappings.insert(old, old_node);
                self.mappings.insert(new, new_node);
            }
        };
    }

    // Add a new node for the e-class
    fn add_node(&mut self, new_node: Node<V>) {
        let output = new_node.output.get();
        if !self.mappings.contains_key(&output) {
            self.mappings.insert(output, new_node);
            return;
        }

        let output = self.canonicalize_skyline_for(output);
        new_node.output.set(output);

        let node_to_insert = if let Some(output_node) = self.mappings.remove(&output) {
            match self.merge_nodes(output_node, new_node) {
                Ok(result) => result,
                Err((mut old_node, mut new_node)) => {
                    old_node.input_portions.append(&mut new_node.input_portions);
                    self.postponed.push(new_node);
                    old_node
                }
            }
        } else {
            new_node
        };

        self.mappings.insert(output, node_to_insert);
    }

    /// Compute canonical skyline for the equation. Skyline gives us a rough cost model for the equation.
    /// TODO: a proper cost model, now that we can accomodate them.
    fn compute_equation_skyline(
        mappings: &HashMap<V, Node<V>>,
        _op: Operation,
        inputs: &[Cell<V>],
    ) -> Skyline {
        let mut skyline_builder = SkylineBuilder::default();
        for input in inputs.iter() {
            skyline_builder.add_skyline(&mappings[&input.get()].skyline, 1);
        }
        skyline_builder.build()
    }

    /// Convert node's inputs and outputs to canonical e-class IDs
    fn canonicalize_node(&self, node: &Node<V>) {
        node.output.set(self.find(node.output.get()));
        if let Recipe::Computed { inputs, .. } = &node.recipe {
            for input in inputs.iter() {
                input.set(self.find(input.get()));
            }
        }
    }

    /// Add a new equation for the e-class
    pub(in crate::solvers::simulator2) fn add_equation(
        &mut self,
        op: Operation,
        inputs: Vec<V>,
        output: V,
    ) {
        // SAFETY: Cell<V> and V have the same representation
        let inputs: Vec<Cell<V>> = unsafe { std::mem::transmute(inputs) };

        for input in inputs.iter() {
            input.set(self.canonicalize_skyline_for(input.get()));
        }
        let skyline = Self::compute_equation_skyline(&self.mappings, op, &inputs);

        let new_node = Node {
            output: output.into(),
            skyline,
            recipe: Recipe::Computed { op, inputs },
            input_portions: vec![],
            last_skyline_canonicalization_ts: self.last_update_ts.into(),
        };

        self.add_node(new_node);
    }

    /// Add input slice mapping
    fn add_input_slice(&mut self, output: V, slice: Slice) {
        let skyline = self.canonicalize_skyline(slice.into());

        self.add_node(Node {
            output: output.into(),
            recipe: Recipe::Slice(slice),
            skyline,
            input_portions: vec![],
            last_skyline_canonicalization_ts: self.last_update_ts.into(),
        });
    }

    /// Add an extract node. This behaves differently on slices
    pub(in crate::solvers::simulator2) fn add_extract(
        &mut self,
        input: V,
        slice: Slice,
        output: V,
    ) {
        let input = self.find(input);
        let input_node = &self.mappings[&input];

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

                self.add_node(Node {
                    output: input.into(),
                    recipe: Recipe::Slice(slice),
                    skyline: slice.into(),
                    input_portions: vec![],
                    last_skyline_canonicalization_ts: self.last_update_ts.into(),
                });
            }
        }
    }

    /// Rebuild a DAG and return a new evaluation order.
    ///
    /// NOTE: this currently doesn't guarantee lowest cost extraction.
    pub(in crate::solvers::simulator2) fn rebuild(&mut self) -> Vec<V> {
        let all_eclasses: Vec<V> = self.mappings.keys().cloned().collect();

        // Start by canonicalizing all skylines for all nodes in the DAG
        for eclass in all_eclasses {
            self.canonicalize_skyline_for(eclass);
            self.canonicalize_node(&self.mappings[&eclass]);
        }

        let mut canonical_nodes = vec![];
        // Canonicalize all post-poned nodes as well
        for mut node in std::mem::take(&mut self.postponed) {
            node.skyline = self.canonicalize_skyline(node.skyline);
            self.canonicalize_node(&node);
        }

        // Canonicalize all entries in computable_intervals map
        for (_, output) in self.computable_slices.iter_mut(0..) {
            *output = Self::find_static(&self.mappings, *output);
        }

        // Finally, remove all DAG entries. We will rebuilt DAG from ground up based on heights
        for (_, node) in self.mappings.drain() {
            canonical_nodes.push(node);
        }

        // Filter non-computable nodes
        canonical_nodes.retain(|node| !matches!(node.recipe, Recipe::NonComputable));

        // Reinsert nodes while recomputing their costs
        canonical_nodes.sort_by_cached_key(|node| (node.skyline.max_height(), node.output.get()));

        let mut ordering = vec![];
        for mut node in canonical_nodes {
            // Recompute node's skyline
            node.skyline = match &node.recipe {
                Recipe::Computed { op, inputs } => {
                    Self::compute_equation_skyline(&self.mappings, *op, inputs)
                }
                &Recipe::Slice(slice) => self.canonicalize_skyline(slice.into()),
                Recipe::NonComputable => {
                    // Non-computable nodes have an alternative lowering
                    continue;
                }
            };

            match self.mappings.entry(node.output.get()) {
                Entry::Occupied(mut occupied_entry) => {
                    // Pick the node with the lowest cost
                    let current_node = occupied_entry.get_mut();
                    let node_is_better =
                        node.skyline.max_height() < current_node.skyline.max_height();
                    if node_is_better {
                        occupied_entry.insert(node);
                    }
                }
                Entry::Vacant(vacant_entry) => {
                    // First time node.output is being computed, push to the topological ordering
                    ordering.push(node.output.get());
                    vacant_entry.insert(node);
                }
            }
        }

        ordering
    }

    /// Build a summary of the DAG in text format. Used for expect tests
    pub(in crate::solvers::simulator2) fn summary(&mut self) -> String {
        let mut result = String::new();
        for value in self.rebuild() {
            let node = &self.mappings[&value];

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
                            .map(|input| self.find(input.get()).show())
                            .join(", ")
                    )
                }
                Recipe::Slice(slice) => {
                    write!(&mut result, "input[{}..{}] ", slice.start, slice.end)
                }
                Recipe::NonComputable => write!(&mut result, "noncomputable"),
            }
            .unwrap();

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
    fn test_input_slice_fdep() {
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
            v3 = and(v2, v2) (skyline: [(0..512, 2)])
            v4 = or(v2, v2) (skyline: [(0..512, 2)])
            v5 = add(v2, v2) (skyline: [(0..512, 2)])
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
            v5 = not(v4) (skyline: [(16..32, 3)])
            input[0..16] = v3 = neg(v5) (skyline: [(16..32, 4)])
            v1 = input[0..64] (skyline: [(16..32, 5), (48..64, 1)])
            v2 = input[0..32] (skyline: [(16..32, 5)])
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
