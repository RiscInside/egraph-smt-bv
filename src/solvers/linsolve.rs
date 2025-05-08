//! Solver for bitvector linear equations
use std::{
    collections::HashSet,
    hash::BuildHasher,
    sync::{Arc, Mutex},
};

use crate::{
    intercept::{Listener, ProxySort},
    plan::PlanResult,
    Context,
};
use anyhow::Context as _;
use egglog::{
    ast::{Command, GenericSchedule, RunConfig, Symbol},
    sort::{EqSort, FromSort, I64Sort, IntoSort, UnitSort},
    span, ArcSort, EGraph, PrimitiveLike, Value,
};
use hashbrown::{DefaultHashBuilder, HashMap};
use itertools::{EitherOrBoth, Itertools};
use num_bigint::BigUint;

/// Width of any particular bitvector
type Width = u64;
/// Bit-vector parity
type Parity = u64;

/// Linear combination of values
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LinearRow<T: Copy> {
    width: Width,
    // Coefficients for all free variables, sorted by value, no T duplicates
    values: Vec<(BigUint, T)>,
    constant: BigUint,
}

impl<T: Copy + Ord> LinearRow<T> {
    /// Get 2^width bigint
    fn exclusive_bound(&self) -> BigUint {
        BigUint::from(1u32) << self.width
    }

    /// Get 2^width - 1 bigint
    fn inclusive_bound(&self) -> BigUint {
        self.exclusive_bound() - BigUint::from(1u32)
    }

    /// Substitute one linear function into another. Returns None if left unchanged
    fn subst(&self, subst_for: T, parity: u64, new_values: &LinearRow<T>) -> Option<LinearRow<T>> {
        assert!(self.width == new_values.width);

        let Ok(idx) = self.values.binary_search_by_key(&subst_for, |elem| elem.1) else {
            return None;
        };

        let coeff = self.values[idx].0.clone();
        if coeff.bits() < parity {
            return None;
        }
        let truncation_constant = self.inclusive_bound();

        let multiplier = &coeff >> parity;
        let mut remainder = &coeff - (&multiplier << parity);
        let constant = (&self.constant + &new_values.constant * &multiplier) & &truncation_constant;

        let values = self
            .values
            .iter()
            .merge_join_by(new_values.values.iter(), |lhs, rhs| lhs.1.cmp(&rhs.1))
            .map(|merge| match merge {
                EitherOrBoth::Both((lhs_coeff, value), (rhs_coeff, _)) => (
                    (lhs_coeff + &multiplier * rhs_coeff) & &truncation_constant,
                    *value,
                ),
                EitherOrBoth::Left((coeff, value)) => (
                    if *value == subst_for {
                        std::mem::take(&mut remainder)
                    } else {
                        coeff.clone()
                    },
                    *value,
                ),
                EitherOrBoth::Right((coeff, value)) => {
                    ((coeff * &multiplier) & &truncation_constant, *value)
                }
            })
            .filter(|(coeff, _)| coeff.bits() != 0)
            .collect();

        Some(LinearRow {
            width: self.width,
            values,
            constant,
        })
    }

    /// Solve a simplified equation against some variable. Variable is picked based on some key function
    fn solve<Key: Ord>(self, key: impl Fn(&BigUint, T) -> Key) -> Option<(T, u64, LinearRow<T>)> {
        // Find a variable to solve for
        let one = BigUint::from(1u32);
        let exclusive_bound = self.exclusive_bound();
        let inclusive_bound = &exclusive_bound - &one;

        // Pick the variable to solve for. We prefer -1 here, then goes 1, then anything else with lowest parity.
        let (mut coeff, variable) = self
            .values
            .iter()
            .min_by_key(|value| key(&value.0, value.1))?
            .clone();

        // We are solving for `variable`. First, we move `variable` with it's coefficient to LHS
        //
        // (2 ^ width - coeff) * variable = values
        //
        // Next, we separate parity bits out
        //
        // (2 ^ width - coeff) = coeff' * (2 ^ parity)
        // coeff' * (2 ^ parity) * variables = values
        //
        // Finally, we compute multiplicative inverse of coeff'
        //
        // (2 ^ parity) * variable = mulinv(coeff') * values
        //
        // yielding a solution for `variable` up to parity

        coeff = &exclusive_bound - coeff; // move to LHS
        let parity = coeff.trailing_zeros().unwrap();
        coeff >>= parity; // divide by max power of two
        let rhs_multiplier = coeff.modinv(&exclusive_bound).unwrap();

        // Assemble a new RHS list
        let rhs_values = self
            .values
            .into_iter()
            .filter(|(_, var)| *var != variable)
            .map(|(coeff, var)| ((coeff * &rhs_multiplier) & &inclusive_bound, var))
            .collect();

        Some((
            variable,
            parity,
            LinearRow {
                width: self.width,
                values: rhs_values,
                constant: (self.constant * &rhs_multiplier) & &inclusive_bound,
            },
        ))
    }

    // Add up two linear rows with a coefficient for the second row.
    fn add_mul(
        &self,
        other: &LinearRow<T>,
        multiplier: &BigUint,
        inclusive_bound: &BigUint,
    ) -> LinearRow<T> {
        LinearRow {
            width: self.width,
            values: self
                .values
                .iter()
                .merge_join_by(other.values.iter(), |lhs, rhs| lhs.1.cmp(&rhs.1))
                .map(|merge| match merge {
                    EitherOrBoth::Both((lhs_coeff, val), (rhs_coeff, _)) => {
                        ((lhs_coeff + rhs_coeff * multiplier) & inclusive_bound, *val)
                    }
                    EitherOrBoth::Left((coeff, val)) => (coeff.clone(), *val),
                    EitherOrBoth::Right((coeff, val)) => {
                        ((coeff * multiplier) & inclusive_bound, *val)
                    }
                })
                .filter(|(coeff, _)| coeff.bits() != 0)
                .collect(),
            constant: (&self.constant + (&other.constant * multiplier)) & inclusive_bound,
        }
    }

    /// Add two equations
    fn add(&self, other: &LinearRow<T>) -> LinearRow<T> {
        self.add_mul(other, &BigUint::from(1u32), &self.inclusive_bound())
    }

    /// Subtract two equations
    fn subtract(&self, other: &LinearRow<T>) -> LinearRow<T> {
        let inclusive_bound = self.inclusive_bound();
        self.add_mul(other, &inclusive_bound, &inclusive_bound)
    }

    /// Add constant
    fn add_constant(self, constant: &BigUint) -> LinearRow<T> {
        let bound = self.inclusive_bound();
        Self {
            width: self.width,
            values: self.values,
            constant: (self.constant + constant) & bound,
        }
    }
}

pub(crate) struct LinearSolver<T: Copy + Ord + std::hash::Hash + 'static> {
    hasher: DefaultHashBuilder,
    /// Solved form of currently known equations - linear equation in terms of unknowns, along with parities.
    /// RHS should not contain any of the keys in this map with coefficients higher than 2^parity.
    /// Additionally, if LHS has some parity value, all RHS coefficients should have parities greater
    /// than or equal to than that of LHS.
    ///
    /// Additionally, we also store hash of parity, as recomputing it is quite expensive. Hash is only computed
    /// if parity is 0 and linear row is not a single variable
    defs: HashMap<T, (Parity, LinearRow<T>, Option<u64>)>,
    /// Free variable index - width information and set of non-free Ts that refer to it. Any given T can have
    /// entries in both `defs` and `free_vars`, but in that case the parity of entry in `defs` must be greater
    /// than zero (otherwise it would have been posssible to fully eliminate the variable).
    free_vars: HashMap<T, (Width, HashSet<T>)>,
    /// Entries in this hashmap
    keyed_by_def: hashbrown::HashTable<T>,
    /// All inferred unions
    pending_unions: Vec<(T, T)>,
    /// Symbol for "V"
    v: Symbol,
}

impl<T: Copy + Ord + std::hash::Hash + 'static> Default for LinearSolver<T> {
    fn default() -> Self {
        Self {
            hasher: DefaultHashBuilder::default(),
            defs: Default::default(),
            free_vars: Default::default(),
            keyed_by_def: Default::default(),
            pending_unions: Default::default(),
            v: "V".into(),
        }
    }
}

impl<T: Copy + Ord + std::hash::Hash + 'static> LinearSolver<T> {
    fn width(&self, val: T) -> Option<u64> {
        if let Some((_, row, _)) = self.defs.get(&val) {
            Some(row.width)
        } else if let Some((width, _)) = self.free_vars.get(&val) {
            Some(*width)
        } else {
            None
        }
    }

    /// Insert a variable -> definition mapping
    fn insert(&mut self, lhs: T, rhs: LinearRow<T>, parity: Parity) {
        // Update inverse index
        for (_, free_var) in rhs.values.iter() {
            self.free_vars
                .entry(*free_var)
                .or_insert_with(|| (rhs.width, Default::default()))
                .1
                .insert(lhs);
        }

        let hash = if parity == 0 {
            // Identifying equations of the form x = y. Those aren't hashed -
            // we simply add a pending union
            if rhs.constant.bits() == 0
                && rhs.values.len() == 1
                && rhs.values[0].0 == BigUint::from(1u32)
            {
                // Exact equality with some value (rhs.values[1].0)
                self.pending_unions.push((lhs, rhs.values[0].1));
                None
            } else {
                let hash = self.hasher.hash_one(&rhs);
                // Find if there are any matching rows currently inserted.
                if let Some(matching) = self
                    .keyed_by_def
                    .find(hash, |value| self.defs.get(value).unwrap().1 == rhs)
                    .cloned()
                {
                    self.pending_unions.push((lhs, matching));
                    None
                } else {
                    self.keyed_by_def
                        .insert_unique(hash, lhs, |elem| self.defs.get(elem).unwrap().2.unwrap());
                    Some(hash)
                }
            }
        } else {
            None
        };

        self.defs.insert(lhs, (parity, rhs, hash));
    }

    /// Eliminate all uses of a variable from defs and update free_vars index. This only has any effect
    /// if eliminatee is a free variable.
    fn elim_free_var_from_rhs(
        &mut self,
        eliminatee: T,
        parity: Parity,
        elim_to: &LinearRow<T>,
    ) -> bool {
        let Some((width, uses)) = self.free_vars.remove(&eliminatee) else {
            // eliminatee isn't a free variable, so there is no equation to update
            return false;
        };

        for rev_dep in uses {
            assert!(rev_dep != eliminatee); // Cycles aren't allowed.
                                            // Remove equation for reverse dependency. We will insert it back after simplification.
            let (rev_dep_parity, rev_dep_equation, prev_row_hash) =
                self.defs.remove(&rev_dep).unwrap();

            // If value was part of the hashcons, we remove it from the hashmap. We only need to remove it if values match exactly,
            // but our equality predicate takes equality of matching linear rows into account.
            if let Some(prev_row_hash) = prev_row_hash {
                // The reason why it's safe to just call entry.remove() here is subtle - all other equations
                // referring to this hashtable entry are exactly equal to rev_dep_equation, and are thus also
                // affected by substitution (thus no longer discoverable).
                if let Ok(entry) = self.keyed_by_def.find_entry(prev_row_hash, |val| {
                    *val == rev_dep || self.defs.get(val).unwrap().1 == rev_dep_equation
                }) {
                    entry.remove();
                }
            }

            assert_eq!(rev_dep_equation.width, width);
            let subbed_in = rev_dep_equation
                .subst(eliminatee, parity, elim_to)
                .expect("inverse index mismatch - no use of eliminatee found");
            // Rebuild inverse index for this equation - remove all old dependenices...
            for (_, old_free_var) in rev_dep_equation.values.iter() {
                if *old_free_var != eliminatee {
                    // Skip eliminatee as it's no longer part of the inverse index
                    let uses = &mut self.free_vars.get_mut(old_free_var).unwrap().1;
                    uses.remove(&rev_dep);
                    // Remove the entry from index if not used anymore
                    if uses.is_empty()
                        && subbed_in
                            .values
                            .binary_search_by_key(old_free_var, |key| key.1)
                            .is_err()
                    {
                        self.free_vars.remove(old_free_var);
                    }
                }
            }

            // Insert the entry
            self.insert(rev_dep, subbed_in, rev_dep_parity);
        }

        true
    }

    /// Replace usages of the variable with a row. This may yield a new equation to solve.
    /// This does not add eliminatee -> elim_to mapping, this has to be done manually
    fn elim_variable(
        &mut self,
        eliminatee: T,
        parity: Parity,
        elim_to: &LinearRow<T>,
    ) -> Option<LinearRow<T>> {
        // Start by removing the variable from RHSes
        self.elim_free_var_from_rhs(eliminatee, parity, elim_to);

        // Variable can now only be on LHS. If it is, we have an equation to solve (old and new interpretation of eliminatee have to agree)
        if let Some((old_parity, rhs_equation, _)) = self.defs.remove(&eliminatee) {
            assert!(old_parity > parity);
            Some(elim_to.subtract(&rhs_equation))
        } else {
            None
        }
    }

    fn solve_step(&mut self, equation: LinearRow<T>) -> Option<LinearRow<T>> {
        // Pick the variable with the lowest parity. In case of a tie, pick the variable with the least number of uses on RHS
        // to minimize number of updates we have to do
        let inclusive_bound = equation.inclusive_bound();
        let Some((eliminatee, parity, elim_to)) = equation.solve(|coeff, value| {
            (
                coeff.trailing_zeros().unwrap(),
                self.free_vars
                    .get(&value)
                    .map(|(_, mentions)| mentions.len()),
                // Last comparison is a bonus for debuggability. We want to pick variable with -1 coefficient to make output prettier
                coeff != &inclusive_bound,
            )
        }) else {
            // TODO: check if constant in equation is non-zero. Can report UNSAT in this case
            return None;
        };
        let next_equation = self.elim_variable(eliminatee, parity, &elim_to);
        // Add mapping
        self.insert(eliminatee, elim_to, parity);
        next_equation
    }

    fn solve(&mut self, mut equation: LinearRow<T>) {
        while let Some(next_equation) = self.solve_step(equation) {
            equation = next_equation;
        }
    }

    /// Get equation for the variable
    fn get_exact_equation(&mut self, variable: T, width: Width) -> LinearRow<T> {
        self.defs
            .get(&variable)
            .filter(|(parity, _, _)| *parity == 0)
            .map(|(_, equation, _)| equation.clone())
            .unwrap_or_else(|| LinearRow {
                width,
                values: vec![(BigUint::from(1u32), variable)],
                constant: BigUint::from(0u32),
            })
    }

    /// Biased equality, used for eliminating old into new
    fn assert_equal(&mut self, old: T, new: T) {
        let Some(width) = self.width(old).or(self.width(new)) else {
            // Equality between two values we don't even know about is not worth considering
            return;
        };

        let equation = self
            .get_exact_equation(old, width)
            .subtract(&self.get_exact_equation(new, width));
        self.solve(equation)
    }

    /// Assert that value is equal to some big-int constant
    #[allow(dead_code)]
    fn assert_is_constant(&mut self, value: T, constant: BigUint, width: Width) {
        let equation = self.get_exact_equation(value, width);
        let negated_constant = if constant.bits() == 0 {
            constant
        } else {
            equation.exclusive_bound() - constant
        };
        self.solve(equation.add_constant(&negated_constant));
    }

    /// Assert that the value is equal to sum of two other values
    fn assert_is_add(&mut self, lhs: T, rhs: T, res: T, width: Width) {
        let equation = self
            .get_exact_equation(lhs, width)
            .add(&self.get_exact_equation(rhs, width))
            .subtract(&self.get_exact_equation(res, width));
        self.solve(equation);
    }

    /// Assert that value is equal to other value multiplied
    #[allow(dead_code)]
    fn assert_is_mul(&mut self, op: T, constant: BigUint, res: T, width: Width) {
        let res_equation = self.get_exact_equation(res, width);
        let exclusive_bound = res_equation.exclusive_bound();
        let inclusive_bound = exclusive_bound - BigUint::from(1u32);
        let negated_constant = if constant.bits() == 0 {
            constant
        } else {
            res_equation.exclusive_bound() - constant
        };
        let equation = res_equation.add_mul(
            &self.get_exact_equation(op, width),
            &negated_constant,
            &inclusive_bound,
        );
        self.solve(equation);
    }

    /// Flush all inferrred equalities
    fn new_inferred_eqs(&mut self, mut on_eq: impl FnMut(T, T)) {
        for (lhs, rhs) in std::mem::take(&mut self.pending_unions) {
            on_eq(lhs, rhs);
        }
    }
}

impl<T: Copy + Ord + std::hash::Hash + 'static> LinearSolver<T> {
    fn dump(&self, mut print_t: impl FnMut(&T) -> String) {
        eprintln!("{{");
        eprintln!("  Equations: {{");
        for (key, (parity, row, hash)) in self.defs.iter() {
            eprintln!(
                "    2^{parity} * {} = {} + {} (width: {}, hash: {hash:?})",
                print_t(key),
                row.values
                    .iter()
                    .map(|(coeff, var)| format!("{coeff} * {}", print_t(var)))
                    .join(" + "),
                row.constant,
                row.width
            )
        }
        eprintln!("  }}");
        eprintln!("  Free variable index: {{");
        for (key, (width, refs)) in self.free_vars.iter() {
            eprintln!(
                "    {} -> width: {width}, reverse deps: {{ {} }}",
                print_t(key),
                refs.iter().sorted().map(&mut print_t).join(", ")
            )
        }
        eprintln!("  }}");
        eprintln!(
            "  Keyed elements: {{ {} }}",
            self.keyed_by_def
                .iter()
                .sorted()
                .map(&mut print_t)
                .join(", ")
        );
        eprintln!("}}");
    }
}

impl LinearSolver<Value> {
    #[allow(dead_code)]
    fn dump_egglog(&self) {
        self.dump(|val| format!("v{}", val.bits));
    }
}

struct AssertAdd {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    int_sort: Arc<I64Sort>,
    solver: Arc<Mutex<LinearSolver<Value>>>,
}

impl PrimitiveLike for AssertAdd {
    fn name(&self) -> egglog::ast::Symbol {
        "linsolve-add".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "linsolve-add".into(),
            vec![
                self.v_sort.clone(),
                self.v_sort.clone(),
                self.v_sort.clone(),
                self.int_sort.clone(),
                self.unit_sort.clone(),
            ],
            span.clone(),
        ))
    }

    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut EGraph>,
    ) -> Option<Value> {
        let mut solver = self.solver.lock().unwrap();
        solver.assert_is_add(
            values[0],
            values[1],
            values[2],
            i64::load(&self.int_sort, &values[3]).try_into().unwrap(),
        );

        IntoSort::store((), &self.unit_sort)
    }
}

impl Listener for LinearSolver<Value> {
    fn on_merge(&mut self, old: Value, new: Value) {
        self.assert_equal(old, new);
    }

    fn register_extra_primitives(arc_self: Arc<Mutex<Self>>, info: &mut egglog::TypeInfo) {
        info.add_primitive(AssertAdd {
            v_sort: info
                .get_sort_by(|sort: &Arc<EqSort>| sort.name.as_str() == "V")
                .unwrap(),
            unit_sort: info.get_sort_by(|_| true).unwrap(),
            int_sort: info.get_sort_by(|_| true).unwrap(),
            solver: arc_self.clone(),
        });
    }
}

pub(crate) fn create_linear_solver(egraph: &mut EGraph) -> Arc<Mutex<LinearSolver<Value>>> {
    let solver = Arc::new(Mutex::new(LinearSolver::<Value>::default()));
    let v_sort: Arc<EqSort> = egraph
        .get_sort_by(|sort: &Arc<EqSort>| sort.name.as_str() == "V")
        .context("No value sort defined yet")
        .unwrap();

    egraph
        .add_arcsort(
            Arc::new(ProxySort::new(
                "LinSolveProxy".into(),
                "linsolve-proxy".into(),
                v_sort,
                solver.clone(),
            )),
            span!(),
        )
        .context("Adding proxy sort LinSolveProxy for the linear bitvector solver")
        .unwrap();

    solver
}

impl Context {
    pub(crate) fn linsolve_tactic(&mut self) -> PlanResult<bool> {
        // Rebuild e-graph to get all union-find updates
        self.egraph.rebuild_nofail();

        // Run linsolve ruleset to get updates
        self.run_cmds(vec![Command::RunSchedule(GenericSchedule::Run(
            span!(),
            RunConfig {
                ruleset: "linsolve".into(),
                until: None,
            },
        ))])?;

        // Process inferred unions
        let mut solver = self.linear_solver.lock().unwrap();
        let mut changed = false;
        let v = solver.v;
        solver.new_inferred_eqs(|lhs, rhs| {
            self.egraph.union(lhs.bits, rhs.bits, v);
            changed = true;
        });
        drop(solver);

        self.egraph.rebuild_nofail();

        Ok(changed)
    }
}
