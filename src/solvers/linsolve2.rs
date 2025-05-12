//! Linear arithmetic solver over Z/2^NZ.
//!
//! Solver works by maintaining row echelon form for all available equations.
//! Row echelon form is represented sparsely in the following fashion:
//!
//! 1) For each pivot variable v_i, we store an equation expressing it in
//!    terms of other variables. Since we operate in Z/2^Z, which isn't a
//!    field, we have to settle for maintaining equation for 2^p_i * v_i
//!    where p_i is "parity" of v_i. There is only one equation for each
//!    v_i, and hence p_i can be looked up from v_i
//!
//! 2) To enforce REF, we add a side condition that all variables on the
//!    RHS of equation for v_i are greater than v_i according to partiy
//!    variable ordering. Parity variable ordering for v_i and v_j is
//!    defined as lexicographical ordering on (p_i, -v_i) (p_j, -v_j).
//!    This can be roughly interpreted as "you can only refer to
//!    variables of higher parity or equal parity if variable identifier
//!    is lower".
//!
//! 3) Every equation also carries a constant member. Those are blindly
//!    propogated when doing equation manipulation.
//!
//! 4) There is no canonicity requirement unless explicitly enforced
//!    by rebuilding. In other words, solver's state is in REF and
//!    not RREF.
//!
//! There are three key procedures the solver supports. First one is
//! canonicalization. Canonicalization takes any equation sorted with
//! respect to parity variable ordering and reduces it with equations
//! in context to a canonical form, i.e. one where no substitution
//! from equations in context can take place. Canonicalization
//! alterates between canonicilizing a single variable and an equation.
//! Single variable case is used to implement an equivalent of path
//! compression - if canonicalizing an equation requires canonicalizing
//! variable, we don't want to actually do this work ever again.
//!
//! Second procedure is solving equations. As it happens, solver
//! simultaneously solves a set of equations. At each step, it picks
//! an equation to solve and removes it from this set. Each individual
//! equation is solved in the following fashion:
//!
//! 1) Equation to be solved is canonicalized. If equation is reduced
//!    to a constant, we report UNSAT if constant is not zero and
//!    discard it.
//!
//! 2) For an equation in canonical form, we pick the variable to move
//!    to the left hand-side. We select the greatest variable according
//!    to parity variable ordering where parities are looked up from
//!    coefficients in equation (as opposed to context).
//!
//! 3) After splitting variables on RHS, we would like to add LHS -> RHS
//!    binding. We can't just do that though, as we can now have
//!    equations that don't satisfy the "all variables on RHS" are smaller
//!    invariant.
//!
//!    We use a simple method of resolving such conflicts - all conflicting
//!    definition equations are removed from the context and reinserted
//!    into the set of equations to solve.
//!
//!    To find all such conflicts, we maintain an inverse index. Inverse index
//!    tells us, for each variable, which variables are referencing it. The
//!    index is a simple B-tree set with all variable identifiers sorted by
//!    context's variable ordering. During conflict detection phase, we pop
//!    entries from this index one by one as long as conflct is observed.
//!
//! Termination is guaranteed, as on each step we either (1) do nothing
//! and simply remove equation from context (2) reduce parity of the variable.
//! Since we are not introducing any new variables and parities can't go below
//! 0, the alorithm would eventually run out of equations to solve.

use std::{
    cell::Cell,
    cmp::Reverse,
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    hash::{BuildHasher, Hash},
};

use crate::solvers::Width;
use hashbrown::{hash_map, DefaultHashBuilder, HashMap, HashTable};
use itertools::Itertools as _;
use num_bigint::BigUint;

type Coefficient = BigUint;
type Constant = BigUint;
type Parity = u64;

/// A trait for variable types
pub(super) trait Variable: Copy + Ord + std::hash::Hash + std::fmt::Debug + 'static {
    /// Display variable for debugging purposes
    fn show(&self) -> String;
}

/// Linear function of a set of variables.
#[derive(Debug, PartialEq, Eq, Hash)]
struct LinearFunction<V: Variable> {
    // N in Z/2^ZN
    width: Width,
    // Variables with their respective coefficients
    var_coeff_pairs: Vec<(Coefficient, V)>,
    // Constant value. Named this way to make it very clear that, when treated
    // as equation, constant is on the LHS, and RHS is just 0
    lhs_constant: Constant,
}

impl<V: Variable> std::fmt::Display for LinearFunction<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} (mod 2^{})",
            self.var_coeff_pairs
                .iter()
                .map(|(coeff, var)| format!("{}*{}", coeff, var.show()))
                .chain(std::iter::once(self.lhs_constant.to_string()))
                .join(" + "),
            self.width
        )
    }
}

/// Entry with some equation for the variable (e.g. `v`)
#[derive(Debug, PartialEq, Eq)]
struct DefEntry<V: Variable> {
    /// Parity, i.e. the lowest value of `p`` such that we have an
    /// expression for `2^p * v`.
    parity: Parity,
    /// Equation for `2^p * v`
    equation: LinearFunction<V>,
    /// Timestamp of the last canonicalization
    canonicalization_ts: u64,
    /// If set, equation has been bottom-up canonicalized, and
    /// hash matches that of equation
    bottom_up_hash: Cell<Option<u64>>,
}

impl<V: Variable> DefEntry<V> {
    /// Convert definition for the variable back into equation form. This is used when definition
    /// needs to be renormalized.
    fn equation(mut self, for_variable: V) -> LinearFunction<V> {
        // Move conflict_var back to RHS to get an equation to solve
        // -1 * 2^mapping.parity
        let lhs_coeff = (((BigUint::from(1u32) << self.equation.width) - BigUint::from(1u32))
            >> self.parity)
            << self.parity;
        self.equation
            .var_coeff_pairs
            .push((lhs_coeff, for_variable));

        self.equation
    }
}

#[derive(Debug)]
struct Context<V: Variable> {
    mappings: HashMap<V, DefEntry<V>>,
    /// Current canonicalization timestamp. Used to quickly check
    /// if we already converted equation to it's canonical form
    canonicalization_ts: u64,
    /// Reverse dependency map
    rev_deps_map: HashMap<V, (Width, BTreeSet<ParityOrdered<V>>)>,
    /// Updated variable set (for bottom up canonicalization)
    need_recanonicalization: BTreeSet<ParityOrdered<V>>,
    /// Hash-table with variables of parity 0 that uses hash function
    /// derived from the matching LinearFunction hash. This map
    /// is used to discover expressions equivalent to each other.
    ///
    /// Note that, by design, this hash-table will contain duplicate
    /// entries - i.e. it can contain multiple variables that are equal
    /// based on LinearFunction comparison predicate. Specifically,
    /// we have an entry for each value here. In fact, we use this
    /// table with two different equality functions - one comparing
    /// equations, and one comparing literal variables (for removals).
    functions_map: HashTable<V>,
    /// Hash builder for hashing equations in [`function_map`]
    hash_builder: DefaultHashBuilder,
}

impl<V: Variable> std::fmt::Display for Context<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{{{")?;
        for (lhs, entry) in self
            .mappings
            .iter()
            .sorted_by_key(|(lhs, entry)| (Reverse(entry.parity), *lhs))
        {
            writeln!(
                f,
                "  2^{}*{} = {}",
                entry.parity,
                lhs.show(),
                entry.equation
            )?;
        }

        writeln!(f)?;

        for (var, (width, uses)) in self.rev_deps_map.iter().sorted_by_key(|(var, _)| *var) {
            writeln!(
                f,
                "  {} of width {width} is used in equations for {}",
                var.show(),
                uses.iter().map(|(_, Reverse(v))| v.show()).join(", ")
            )?;
        }

        write!(f, "}}}}")
    }
}

/// `ParityOrdered<V>` should be used in place of `V` when we want
/// `Ord` to reflect parity variable ordering.
type ParityOrdered<V> = (Parity, Reverse<V>);

/// Reduce coefficient to a given parity
fn reduce_to_parity(coeff: &Coefficient, parity: Parity) -> (Coefficient, Coefficient) {
    (
        coeff >> parity,
        coeff & ((BigUint::from(1u32) << parity) - BigUint::from(1u32)),
    )
}

impl<V: Variable> Context<V> {
    fn get_parity(&self, var: V, width: Width) -> Parity {
        self.mappings
            .get(&var)
            .map(|entry| entry.parity)
            .unwrap_or(width)
    }

    fn as_ordered_var(&self, var: V, width: Width) -> ParityOrdered<V> {
        (self.get_parity(var, width), Reverse(var))
    }

    /// Update index when equation for `variable` (`2^parity * variable = removed_equation`) is
    /// being removed. ignore_variable is used for debug mode checks - normally all
    /// variables mentioned by expression should have an entry in reverse index, but during
    /// conflict resolution it is possible for the entry corresponding to solved var to be removed
    fn update_rev_dep_map_on_removal(
        rev_deps_map: &mut HashMap<V, (Width, BTreeSet<ParityOrdered<V>>)>,
        variable: V,
        parity: Parity,
        removed_equation: &LinearFunction<V>,
        #[cfg(debug_assertions)] ignore_variable: Option<V>,
    ) {
        for (_, result_var_dep) in removed_equation.var_coeff_pairs.iter() {
            let hashbrown::hash_map::Entry::Occupied(mut entry) =
                rev_deps_map.entry(*result_var_dep)
            else {
                #[cfg(debug_assertions)]
                assert_eq!(Some(*result_var_dep), ignore_variable);
                continue;
            };

            entry.get_mut().1.remove(&(parity, Reverse(variable)));
            if entry.get().1.is_empty() {
                entry.remove();
            }
        }
    }

    fn update_rev_dep_map_on_insertion(
        rev_deps_map: &mut HashMap<V, (Width, BTreeSet<ParityOrdered<V>>)>,
        variable: V,
        parity: Parity,
        inserted_equation: &LinearFunction<V>,
    ) {
        for (_, result_var_dep) in inserted_equation.var_coeff_pairs.iter() {
            rev_deps_map
                .entry(*result_var_dep)
                .or_insert_with(|| (inserted_equation.width, BTreeSet::new()))
                .1
                .insert((parity, Reverse(variable)));
        }
    }

    fn update_rev_dep_map_diff(
        rev_deps_map: &mut HashMap<V, (Width, BTreeSet<ParityOrdered<V>>)>,
        variable: V,
        parity: Parity,
        old: &LinearFunction<V>,
        new: &LinearFunction<V>,
    ) {
        Self::update_rev_dep_map_on_removal(
            rev_deps_map,
            variable,
            parity,
            old,
            #[cfg(debug_assertions)]
            None,
        );
        Self::update_rev_dep_map_on_insertion(rev_deps_map, variable, parity, new);
    }
}

/// Implementation of the canonicalization procedure. Since we might
/// be potentially be dealing with thousands of values, this implementation
/// is entirely non-recursive
mod canon {
    use super::*;

    /// One of the recursive canonicalizations in-flight.
    #[derive(Debug)]
    struct InProgress<V: Variable> {
        /// Aggregated constant
        cur_constant: BigUint,
        /// Computed coefficients + variable pairs
        cur_var_and_coeffs: Vec<(BigUint, V)>,
        /// If Some, this isn't the first call, and we need
        /// to look up canonicalized version for contained
        /// `v`, multiply it by the coefficient, and
        /// add terms to worklist before continuing
        subst: Option<(V, BigUint)>,
        /// Worklist - remaining set of variables to canonicalize
        pending: BTreeMap<ParityOrdered<V>, BigUint>,
        /// If Some, store the resulting equation as
        /// the canonicalized definition for the variable
        result_var: Option<(V, Parity)>,
    }

    impl<V: Variable> Context<V> {
        fn add_variable(
            &self,
            variable: V,
            width: Width,
            pending: &mut BTreeMap<ParityOrdered<V>, BigUint>,
            multiplier: BigUint,
            inclusive_bound: &BigUint,
        ) {
            match pending.entry(self.as_ordered_var(variable, width)) {
                Entry::Vacant(vacant_entry) => {
                    vacant_entry.insert(multiplier);
                }
                Entry::Occupied(mut occupied_entry) => {
                    *occupied_entry.get_mut() += multiplier;
                    *occupied_entry.get_mut() &= inclusive_bound;
                    if occupied_entry.get().bits() == 0 {
                        occupied_entry.remove();
                    }
                }
            }
        }

        fn add_equation(
            &self,
            constant: &mut BigUint,
            pending: &mut BTreeMap<ParityOrdered<V>, BigUint>,
            equation: &LinearFunction<V>,
            multiplier: &BigUint,
            inclusive_bound: &BigUint,
        ) {
            *constant += &equation.lhs_constant * multiplier;
            *constant &= inclusive_bound;

            for (coeff, var) in equation.var_coeff_pairs.iter() {
                let scaled_coeff = (multiplier * coeff) & inclusive_bound;
                self.add_variable(*var, equation.width, pending, scaled_coeff, inclusive_bound);
            }
        }

        fn first_entry(
            &self,
            equation: &LinearFunction<V>,
            inclusive_bound: &BigUint,
            result_var: Option<(V, Parity)>,
        ) -> InProgress<V> {
            let mut result = InProgress {
                cur_constant: BigUint::from(0u32),
                cur_var_and_coeffs: vec![],
                subst: None,
                pending: BTreeMap::new(),
                result_var,
            };
            self.add_equation(
                &mut result.cur_constant,
                &mut result.pending,
                equation,
                &BigUint::from(1u32),
                inclusive_bound,
            );
            result
        }

        pub(super) fn canonicalize(&mut self, equation: &LinearFunction<V>) -> LinearFunction<V> {
            // Set up the worklist
            let width = equation.width;
            let exclusive_bound = BigUint::from(1u32) << width;
            let inclusive_bound = &exclusive_bound - BigUint::from(1u32);
            let mut worklist = vec![self.first_entry(equation, &inclusive_bound, None)];

            'step: loop {
                let mut in_progress = worklist.pop().unwrap();

                // Substitute the canonicalized solution for `done_var`
                if let Some((done_var, multiplier)) = std::mem::take(&mut in_progress.subst) {
                    let done_var_equation = &self.mappings[&done_var].equation;
                    self.add_equation(
                        &mut in_progress.cur_constant,
                        &mut in_progress.pending,
                        done_var_equation,
                        &multiplier,
                        &inclusive_bound,
                    );
                }

                // Pick the next variable to canonicalize
                while let Some(((parity, Reverse(inner_var)), coeff)) =
                    in_progress.pending.pop_first()
                {
                    let Some(entry) = self
                        .mappings
                        .get(&inner_var)
                        .filter(|entry| entry.parity < coeff.bits())
                    else {
                        if coeff.bits() != 0 {
                            in_progress.cur_var_and_coeffs.push((coeff, inner_var));
                        }
                        continue;
                    };
                    assert_eq!(entry.parity, parity);

                    // Leave residual * inner_var in the cur_var_and_coeffs.
                    let (multiplier, residual) = reduce_to_parity(&coeff, entry.parity);
                    if residual.bits() != 0 {
                        in_progress.cur_var_and_coeffs.push((residual, inner_var));
                    }

                    assert_ne!(multiplier.bits(), 0);
                    // If entry has been recently canonicalized, we can skip outer loop iteration here
                    if entry.canonicalization_ts == self.canonicalization_ts {
                        self.add_equation(
                            &mut in_progress.cur_constant,
                            &mut in_progress.pending,
                            &entry.equation,
                            &multiplier,
                            &inclusive_bound,
                        );

                        continue;
                    }

                    // inner_var will be the next variable to canonicalize
                    worklist.push(InProgress {
                        subst: Some((inner_var, multiplier)),
                        ..in_progress
                    });
                    worklist.push(self.first_entry(
                        &entry.equation,
                        &inclusive_bound,
                        Some((inner_var, entry.parity)),
                    ));

                    continue 'step;
                }

                // At this point the local worklist is empty, which means that we have got canonical
                // version of the equation.
                let canon_equation = LinearFunction {
                    width,
                    var_coeff_pairs: in_progress.cur_var_and_coeffs,
                    lhs_constant: in_progress.cur_constant,
                };

                // If this isn't a recursive call (canonicalizing a variable), return canonicalized
                // equation as the result
                let Some((result_var, result_var_parity)) = in_progress.result_var else {
                    break canon_equation;
                };

                let mapping = self.mappings.get_mut(&result_var).unwrap();

                if mapping.equation != canon_equation {
                    // Update reverse dependency index
                    Self::update_rev_dep_map_diff(
                        &mut self.rev_deps_map,
                        result_var,
                        result_var_parity,
                        &mapping.equation,
                        &canon_equation,
                    );

                    // As the equation for V has now changed, we might need to remove an entry from `function_map`.
                    // New entry will be reinserted during bottom up canonicalization pass
                    if let Some(hash) = mapping.bottom_up_hash.get() {
                        self.functions_map
                            .find_entry(hash, |other_val| result_var == *other_val)
                            .unwrap()
                            .remove();
                        mapping.bottom_up_hash.set(None);
                    }

                    mapping.equation = canon_equation;
                    mapping.canonicalization_ts = self.canonicalization_ts;
                }
            }
        }

        /// Canonicalize an equation, assuming that all variables mentioned in it have already been canonicalized
        pub(super) fn canonicalize_shallow(
            &self,
            equation: &LinearFunction<V>,
        ) -> LinearFunction<V> {
            let mut constant = equation.lhs_constant.clone();
            let mut result_map = BTreeMap::new();
            let width = equation.width;
            let inclusive_bound = (BigUint::from(1u32) << width) - BigUint::from(1u32);

            for (inner_coeff, inner_var) in equation.var_coeff_pairs.iter() {
                let Some(entry) = self
                    .mappings
                    .get(inner_var)
                    .filter(|entry| entry.parity < inner_coeff.bits())
                else {
                    self.add_variable(
                        *inner_var,
                        width,
                        &mut result_map,
                        inner_coeff.clone(),
                        &inclusive_bound,
                    );
                    continue;
                };

                let (multiplier, residual) = reduce_to_parity(inner_coeff, entry.parity);
                if residual.bits() != 0 {
                    self.add_variable(
                        *inner_var,
                        width,
                        &mut result_map,
                        residual,
                        &inclusive_bound,
                    );
                }

                assert_ne!(multiplier.bits(), 0);
                self.add_equation(
                    &mut constant,
                    &mut result_map,
                    &entry.equation,
                    &multiplier,
                    &inclusive_bound,
                );
            }

            LinearFunction {
                width,
                var_coeff_pairs: result_map
                    .into_iter()
                    .map(|((_, Reverse(var)), coeff)| (coeff, var))
                    .collect(),
                lhs_constant: constant,
            }
        }

        pub(super) fn canonicalize_all_bottom_up(&mut self, mut report_equality: impl FnMut(V, V)) {
            let mut worklist = std::mem::take(&mut self.need_recanonicalization);

            while let Some((parity, Reverse(var))) = worklist.pop_last() {
                let definition = self.mappings.get(&var).unwrap();

                // Perform canonicalization of the entry
                let definition = if definition.canonicalization_ts != self.canonicalization_ts {
                    let canonicalized = self.canonicalize_shallow(&definition.equation);
                    if canonicalized != definition.equation {
                        let definition = self.mappings.get_mut(&var).unwrap();

                        // Update reverse dependency index
                        Self::update_rev_dep_map_diff(
                            &mut self.rev_deps_map,
                            var,
                            parity,
                            &definition.equation,
                            &canonicalized,
                        );

                        // Set new definition
                        definition.equation = canonicalized;
                        definition.canonicalization_ts = self.canonicalization_ts;

                        // Remove previous mapping from function_map if exists
                        if let Some(hash) = definition.bottom_up_hash.get() {
                            assert_eq!(definition.parity, 0);
                            // Remove previous mapping
                            self.functions_map
                                .find_entry(hash, |variable| *variable == var)
                                .unwrap()
                                .remove();
                            definition.bottom_up_hash.set(None);
                        }

                        self.mappings.get(&var).unwrap()
                    } else {
                        definition
                    }
                } else {
                    definition
                };

                if definition.bottom_up_hash.get().is_some() {
                    // Canonical entry with accurately computed hash
                    continue;
                }

                // Propogate changes upwards
                if let Some((_, rev_dep_map)) = self.rev_deps_map.get(&var) {
                    worklist.extend(rev_dep_map.iter());
                }

                if definition.parity != 0 {
                    // Not hashing definitions with parity above 0, as we can't identify equalities based on them
                    continue;
                }

                // Report equalities based on simple lhs = rhs equations. This is specifically needed when rhs
                // is a free variable
                if definition.equation.lhs_constant.bits() == 0 // Constant is 0
                    && definition.equation.var_coeff_pairs.len() == 1 // There is only one term
                    && definition.equation.var_coeff_pairs[0].0.bits() == 1 // It's coefficient is one
                    && !self
                        .mappings
                        .contains_key(&definition.equation.var_coeff_pairs[0].1)
                {
                    report_equality(var, definition.equation.var_coeff_pairs[0].1);
                }

                // Update hash for the parity 0 definition and discover equalities
                let hash = self.hash_builder.hash_one(&definition.equation);
                definition.bottom_up_hash.set(Some(hash));

                if let Ok(mapping) = self.functions_map.find_entry(hash, |other| {
                    self.mappings[other].equation == definition.equation
                }) {
                    // Discovered a match!
                    report_equality(*mapping.get(), var);
                }

                // Insert mapping for the equation
                self.functions_map.insert_unique(hash, var, |var| {
                    self.mappings[var].bottom_up_hash.get().unwrap()
                });
            }
        }
    }
}

impl<V: Variable> LinearFunction<V> {
    /// Pick variable to solve against and move other variables to RHS. Input equation needs to be
    /// canonical, but the result does not have to be.
    fn split_min_variable(mut self) -> Option<(V, Parity, LinearFunction<V>)> {
        // Select the variable with to be lowest parity
        let (variable_position, _) = self
            .var_coeff_pairs
            .iter()
            .enumerate()
            .min_by_key(|(_, (coeff, var))| (coeff.trailing_zeros(), Reverse(*var)))?;

        let (coeff, var) = self.var_coeff_pairs.swap_remove(variable_position);
        let parity = coeff.trailing_zeros().unwrap();

        let multiplier = coeff >> parity;

        let exclusive_bound = &(BigUint::from(1u32) << self.width);
        let inclusive_bound = &(exclusive_bound - BigUint::from(1u32));
        let rhs_multiplier = &(exclusive_bound - multiplier.modinv(exclusive_bound).unwrap());

        // NOTE: multiplication by rhs_multiplier and use of swap_remove earlier make the resulting
        // equation potentially non-canonical. We do not care that much.
        let new_rhs_coeff_pairs = self
            .var_coeff_pairs
            .into_iter()
            .map(|(coeff, var)| ((coeff * rhs_multiplier) & inclusive_bound, var))
            .collect();
        let new_constant = (self.lhs_constant * rhs_multiplier) & inclusive_bound;

        Some((
            var,
            parity,
            LinearFunction {
                width: self.width,
                var_coeff_pairs: new_rhs_coeff_pairs,
                lhs_constant: new_constant,
            },
        ))
    }
}

impl<V: Variable> Context<V> {
    /// Remove mapping for a definition
    fn remove_mapping(
        &mut self,
        variable: V,
        #[cfg(debug_assertions)] ignore_variable: Option<V>,
    ) -> Option<DefEntry<V>> {
        let removed = self.mappings.remove(&variable)?;
        Self::update_rev_dep_map_on_removal(
            &mut self.rev_deps_map,
            variable,
            removed.parity,
            &removed.equation,
            #[cfg(debug_assertions)]
            ignore_variable,
        );
        self.need_recanonicalization
            .remove(&(removed.parity, Reverse(variable)));

        if let Some(hash) = removed.bottom_up_hash.get() {
            assert_eq!(removed.parity, 0);
            self.functions_map
                .find_entry(hash, |other| *other == variable)
                .unwrap()
                .remove();
        }
        Some(removed)
    }

    /// Introduce a new mapping for the definition
    fn insert_mapping(&mut self, variable: V, mapping: DefEntry<V>) {
        assert!(mapping.bottom_up_hash.get().is_none());

        Self::update_rev_dep_map_on_insertion(
            &mut self.rev_deps_map,
            variable,
            mapping.parity,
            &mapping.equation,
        );
        self.need_recanonicalization
            .insert((mapping.parity, Reverse(variable)));

        self.mappings.insert(variable, mapping);
    }

    /// Get all ordering conflicts that arise as the result of lowering parity
    /// of variable from `old_parity` to `new_parity`.
    fn find_all_conflicts(
        &mut self,
        variable: V,
        new_parity: Parity,
    ) -> BTreeSet<ParityOrdered<V>> {
        let hash_map::Entry::Occupied(mut entry) = self.rev_deps_map.entry(variable) else {
            return BTreeSet::new();
        };

        let rev_deps_set = &mut entry.get_mut().1;
        let result = rev_deps_set.split_off(&(new_parity, Reverse(variable)));

        if rev_deps_set.is_empty() {
            // No more mentions, entry can be removed
            entry.remove();
        }

        result
    }

    /// Add a new definition for variable `variable` post-solve.
    fn add_solved_def(
        &mut self,
        variable: V,
        parity: Parity,
        equation: LinearFunction<V>,
        mut submit_new_equation: impl FnMut(LinearFunction<V>),
    ) {
        // If there has already been a definition for `V` in the past, we need to
        // add a linear equation that ensures they agree
        if let Some(old_mapping) = self.remove_mapping(
            variable,
            #[cfg(debug_assertions)]
            None,
        ) {
            assert!(old_mapping.parity > parity);
            submit_new_equation(old_mapping.equation(variable));
        }
        // Extract conflicts
        let conflicts = self.find_all_conflicts(variable, parity);
        for (_, Reverse(conflict_var)) in conflicts.iter().rev() {
            let mapping = self
                .remove_mapping(
                    *conflict_var,
                    #[cfg(debug_assertions)]
                    Some(variable),
                )
                .unwrap();
            submit_new_equation(mapping.equation(*conflict_var));
        }
        // Finally, add a new definition
        self.insert_mapping(
            variable,
            DefEntry {
                parity,
                equation,
                canonicalization_ts: self.canonicalization_ts,
                bottom_up_hash: Cell::new(None),
            },
        );
        // Update canonicalization timestamp
        self.canonicalization_ts += 1;
    }

    /// Perform one solve step - discharge a single equation, potentially generating
    /// new ones
    fn solve_step(
        &mut self,
        equation: LinearFunction<V>,
        submit_new_equation: impl FnMut(LinearFunction<V>),
    ) {
        let canonical = self.canonicalize(&equation);
        let Some((var, parity, def)) = canonical.split_min_variable() else {
            // TODO: add UNSAT detection if canonical constant is non-zero
            return;
        };
        self.add_solved_def(var, parity, def, submit_new_equation);
    }
}

pub(in crate::solvers) struct Solver<V: Variable> {
    context: Context<V>,
    // TODO: consider using a different data-structure to track pending-equations, e.g. based on parity
    pending_equations: Vec<LinearFunction<V>>,
    // Non-canonical values
    non_canonical: Vec<V>,
}

impl<V: Variable> Default for Solver<V> {
    fn default() -> Self {
        Self {
            context: Context {
                mappings: HashMap::new(),
                canonicalization_ts: 0,
                rev_deps_map: HashMap::new(),
                need_recanonicalization: BTreeSet::new(),
                functions_map: HashTable::new(),
                hash_builder: DefaultHashBuilder::default(),
            },
            pending_equations: vec![],
            non_canonical: vec![],
        }
    }
}

impl<V: Variable> Solver<V> {
    fn assert_is_zero(&mut self, equation: LinearFunction<V>) {
        self.pending_equations
            .push(self.context.canonicalize_shallow(&equation));
    }

    pub(crate) fn assert_is_equal(&mut self, old: V, new: V, width: Width) {
        assert!(old > new, "{} not greater than {}?", old.show(), new.show());
        self.non_canonical.push(old);
        self.assert_is_zero(LinearFunction {
            width,
            var_coeff_pairs: vec![
                ((BigUint::from(1u32) << width) - BigUint::from(1u32), new),
                (BigUint::from(1u32), old),
            ],
            lhs_constant: BigUint::from(0u32),
        });
    }

    pub(crate) fn assert_is_add(&mut self, lhs: V, rhs: V, result: V, width: Width) {
        self.assert_is_zero(LinearFunction {
            width,
            var_coeff_pairs: vec![
                ((BigUint::from(1u32) << width) - BigUint::from(1u32), result),
                (BigUint::from(1u32), lhs),
                (BigUint::from(1u32), rhs),
            ],
            lhs_constant: BigUint::from(0u32),
        });
    }

    pub(crate) fn assert_is_scaled(&mut self, lhs: V, constant: BigUint, result: V, width: Width) {
        self.assert_is_zero(LinearFunction {
            width,
            var_coeff_pairs: vec![
                ((BigUint::from(1u32) << width) - BigUint::from(1u32), result),
                (constant, lhs),
            ],
            lhs_constant: BigUint::from(0u32),
        });
    }

    pub(crate) fn assert_is_constant(&mut self, constant: BigUint, result: V, width: Width) {
        self.assert_is_zero(LinearFunction {
            width,
            var_coeff_pairs: vec![((BigUint::from(1u32) << width) - BigUint::from(1u32), result)],
            lhs_constant: constant,
        });
    }

    /// Remove non-canonical values AFTER bottom-up canonicalization. It is absolutely crucial this
    /// is done after, as otherwise solver will silently drop equations.
    fn remove_noncanonical(&mut self) {
        for value in std::mem::take(&mut self.non_canonical) {
            self.context.remove_mapping(
                value,
                #[cfg(debug_assertions)]
                None,
            );
        }
    }

    pub(crate) fn solve_all_pending(&mut self, report_equalities: impl FnMut(V, V)) {
        let mut worklist = std::mem::take(&mut self.pending_equations);
        while let Some(equation) = worklist.pop() {
            self.context
                .solve_step(equation, |equation| worklist.push(equation));
        }
        self.context.canonicalize_all_bottom_up(report_equalities);
        self.remove_noncanonical();
    }
}

#[cfg(test)]
mod test {
    // For testing purposes
    impl Variable for u64 {
        fn show(&self) -> String {
            format!("v{self}")
        }
    }

    use expect_test::expect;

    use super::*;

    #[test]
    fn test_linear_system1() {
        let mut solver: Solver<u64> = Solver::default();

        // Using larger coefficients and constants for Z/2^64Z
        // Equation 1: 12345678901234x1 + 98765432109876x2 + 45678901234567x3 + 78901234567890 ≡ 0 (mod 2^64)
        solver.assert_is_zero(LinearFunction {
            width: 64,
            var_coeff_pairs: vec![
                (BigUint::from(12345678901234u64), 1),
                (BigUint::from(98765432109876u64), 2),
                (BigUint::from(45678901234567u64), 3),
            ],
            lhs_constant: BigUint::from(78901234567890u64),
        });

        // Equation 2: 55555555555555x1 + 77777777777777x2 + 33333333333333x4 + 11111111111111 ≡ 0 (mod 2^64)
        solver.assert_is_zero(LinearFunction {
            width: 64,
            var_coeff_pairs: vec![
                (BigUint::from(55555555555555u64), 1),
                (BigUint::from(77777777777777u64), 2),
                (BigUint::from(33333333333333u64), 4),
            ],
            lhs_constant: BigUint::from(11111111111111u64),
        });

        // Equation 3: 99999999999999x1 + 88888888888888x3 + 66666666666666x4 + 44444444444444 ≡ 0 (mod 2^64)
        solver.assert_is_zero(LinearFunction {
            width: 64,
            var_coeff_pairs: vec![
                (BigUint::from(99999999999999u64), 1),
                (BigUint::from(88888888888888u64), 3),
                (BigUint::from(66666666666666u64), 4),
            ],
            lhs_constant: BigUint::from(44444444444444u64),
        });

        // Solve equations submitted to the system
        solver.solve_all_pending(|_, _| {
            // No equalities in this problem
            unreachable!();
        });

        // Since we don't know the exact expected output, we can use a placeholder expectation
        // and then update it with the actual output after first run
        let expected = expect![[r#"
            {{
              2^0*v1 = 7199159949078366642*v2 + 15517855851107310130 (mod 2^64)
              2^0*v3 = 17040796058130653496*v2 + 6551417999815801670 (mod 2^64)
              2^0*v4 = 12597058849815457749*v2 + 11030395062240253015 (mod 2^64)

              v2 of width 64 is used in equations for v4, v3, v1
            }}"#]];

        let actual = format!("{}", solver.context);
        expected.assert_eq(&actual);
    }

    #[test]
    fn test_linear_system2() {
        // This test is accompanied by test_system2.smt2 file. Since we operate in Z/16Z,
        // you can check this one fairly straightforwardly with e.g. z3 test_system2.smt2
        let mut solver: Solver<u64> = Solver::default();

        // (1) 5x1 + 11x2 + 7x3 + 2x5 ≡ 4 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(5u32), 1),
                (BigUint::from(11u32), 2),
                (BigUint::from(7u32), 3),
                (BigUint::from(2u32), 5),
            ],
            lhs_constant: BigUint::from(12u32),
        });

        // (2) 3x1 + 13x2 + 4x4 + 9x6 ≡ 10 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(3u32), 1),
                (BigUint::from(13u32), 2),
                (BigUint::from(4u32), 4),
                (BigUint::from(9u32), 6),
            ],
            lhs_constant: BigUint::from(6u32),
        });

        // (3) 7x1 + 9x2 + 5x3 + 12x7 ≡ 6 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(7u32), 1),
                (BigUint::from(9u32), 2),
                (BigUint::from(5u32), 3),
                (BigUint::from(12u32), 7),
            ],
            lhs_constant: BigUint::from(10u32),
        });

        // (4) 2x1 + 14x2 + 3x5 + 11x8 ≡ 8 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(2u32), 1),
                (BigUint::from(14u32), 2),
                (BigUint::from(3u32), 5),
                (BigUint::from(11u32), 8),
            ],
            lhs_constant: BigUint::from(8u32),
        });

        // (5) 6x1 + 10x2 + 1x4 + 13x6 ≡ 12 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(6u32), 1),
                (BigUint::from(10u32), 2),
                (BigUint::from(1u32), 4),
                (BigUint::from(13u32), 6),
            ],
            lhs_constant: BigUint::from(4u32),
        });

        // (6) 8x1 + 8x2 + 2x7 + 5x3 ≡ 14 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(8u32), 1),
                (BigUint::from(8u32), 2),
                (BigUint::from(2u32), 7),
                (BigUint::from(5u32), 3),
            ],
            lhs_constant: BigUint::from(2u32),
        });

        // (7) 4x1 + 12x2 + 6x5 + 3x8 ≡ 3 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![
                (BigUint::from(4u32), 1),
                (BigUint::from(12u32), 2),
                (BigUint::from(6u32), 5),
                (BigUint::from(3u32), 8),
            ],
            lhs_constant: BigUint::from(13u32),
        });

        // (8) 9x1 + 7x2 ≡ 0 (mod 16)
        solver.assert_is_zero(LinearFunction {
            width: 4,
            var_coeff_pairs: vec![(BigUint::from(9u32), 1), (BigUint::from(7u32), 2)],
            lhs_constant: BigUint::from(0u32),
        });

        // Solve equations submitted to the system
        let mut pending_equalities = vec![];
        solver.solve_all_pending(|lhs, rhs| {
            pending_equalities.push((std::cmp::min(lhs, rhs), std::cmp::max(lhs, rhs)));
        });

        let expected = expect![[r#"
            {{
              2^1*v7 = 8 (mod 2^4)
              2^0*v2 = 1*v1 + 0 (mod 2^4)
              2^0*v3 = 14 (mod 2^4)
              2^0*v4 = 2 (mod 2^4)
              2^0*v5 = 1 (mod 2^4)
              2^0*v6 = 2 (mod 2^4)
              2^0*v8 = 15 (mod 2^4)

              v1 of width 4 is used in equations for v2
            }}"#]];
        let actual = format!("{}", solver.context);
        expected.assert_eq(&actual);
        // Assert that solver inferred v1 == v2 and v4 == v6
        assert_eq!(pending_equalities, vec![(1, 2), (4, 6)]);
    }

    #[test]
    fn test_associativity_of_add() {
        let mut solver: Solver<u64> = Solver::default();
        solver.assert_is_add(1, 2, 12, 32);
        solver.assert_is_add(2, 3, 23, 32);

        solver.assert_is_add(1, 23, 100, 32);
        solver.assert_is_add(12, 3, 200, 32);

        solver.solve_all_pending(|lhs, rhs| {
            assert_eq!(std::cmp::min(lhs, rhs), 100);
            assert_eq!(std::cmp::max(lhs, rhs), 200);
        });

        let expected = expect![[r#"
            {{
              2^0*v12 = 1*v2 + 1*v1 + 0 (mod 2^32)
              2^0*v23 = 1*v3 + 1*v2 + 0 (mod 2^32)
              2^0*v100 = 1*v3 + 1*v2 + 1*v1 + 0 (mod 2^32)
              2^0*v200 = 1*v3 + 1*v2 + 1*v1 + 0 (mod 2^32)

              v1 of width 32 is used in equations for v200, v100, v12
              v2 of width 32 is used in equations for v200, v100, v23, v12
              v3 of width 32 is used in equations for v200, v100, v23
            }}"#]];
        let actual = format!("{}", solver.context);
        expected.assert_eq(&actual);
    }

    #[test]
    fn test_union_prune() {
        let mut solver: Solver<u64> = Solver::default();
        solver.assert_is_add(1, 2, 4, 32);
        solver.assert_is_equal(4, 3, 32);

        let mut pending_equalities = vec![];
        solver.solve_all_pending(|lhs, rhs| {
            pending_equalities.push((lhs, rhs));
        });

        // Note no mention of v4
        let expected = expect![[r#"
            {{
              2^0*v3 = 1*v2 + 1*v1 + 0 (mod 2^32)

              v1 of width 32 is used in equations for v3
              v2 of width 32 is used in equations for v3
            }}"#]];
        let actual = format!("{}", solver.context);
        expected.assert_eq(&actual);

        // We currently push equalities back to the user, but that's probably not a huge deal
        assert_eq!(pending_equalities, vec![(3, 4)]);
    }
}
