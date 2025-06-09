use crate::solvers::simulator2::dag::Dag;
use crate::solvers::{Hypothesis, Variable};
use egglog::util::IndexSet;
use hashbrown::hash_map::Entry;
use hashbrown::HashMap;
use num_bigint::BigUint;
use std::str::FromStr as _;
use z3::ast::{Ast, Bool, BV};

use super::{
    dag::{Node, Recipe},
    Operation, SimulationCore,
};

// Convert from Bool<'ctx> to BV<'ctx>
fn bool_to_bv<'ctx>(ctx: &'ctx z3::Context, bool: Bool<'ctx>) -> BV<'ctx> {
    bool.ite(&BV::from_i64(ctx, 1, 1), &BV::from_i64(ctx, 0, 1))
}

// Depth threshold
const MAX_DEPTH: usize = 7;

type Visited = bool;
type Depth = u64;

struct DagSolveContext<'ctx, 'constants, 'dag, V: Variable> {
    dag: &'dag Dag<V>,
    constants: &'constants IndexSet<BigUint>,
    input_var: BV<'ctx>,
    reflected_vars: HashMap<V, (BV<'ctx>, &'dag Node<V>, Visited, Depth)>,
    worklist: Vec<V>,
}

impl<'ctx, 'dag, V: Variable> DagSolveContext<'ctx, '_, 'dag, V> {
    fn eclass_entry(
        &mut self,
        ctx: &'ctx z3::Context,
        eclass: V,
        depth: Depth,
    ) -> &mut (BV<'ctx>, &'dag Node<V>, Visited, Depth) {
        let node = &self.dag.mappings[&eclass];
        let width = node.width;
        match self.reflected_vars.entry(eclass) {
            Entry::Occupied(occupied_entry) => occupied_entry.into_mut(),
            Entry::Vacant(vacant_entry) => {
                let new_var = BV::new_const(ctx, eclass.show(), width.try_into().unwrap());
                vacant_entry.insert((new_var, node, false, depth))
            }
        }
    }

    /// Get z3 variable from e-class
    fn z3_variable_for_eclass(&mut self, ctx: &'ctx z3::Context, eclass: V) -> &BV<'ctx> {
        &self.eclass_entry(ctx, eclass, 0).0
    }

    /// Introduce definition for the eclass into the context
    fn introduce_var_def(
        &mut self,
        eclass: V,
        ctx: &'ctx z3::Context,
        solver: &'ctx z3::Solver<'ctx>,
    ) {
        let eclass = self.dag.find(eclass);
        let (bv, node, visited, depth) = self.eclass_entry(ctx, eclass, 0);
        if *visited {
            return;
        }
        *visited = true;

        let bv = bv.clone();
        let depth = *depth;

        let width = bv.get_size();

        solver.assert(&BV::_eq(
            &bv,
            &match &node.recipe {
                Recipe::Computed { op, inputs } => {
                    let inputs: Vec<_> = inputs
                        .iter()
                        .map(|eclass| {
                            let eclass = self.dag.find(eclass.get());
                            self.worklist.push(eclass);
                            self.eclass_entry(ctx, eclass, depth + 1).0.clone()
                        })
                        .collect();

                    match op {
                        Operation::Constant { table_index } => {
                            let constant = self.constants.get_index(*table_index).unwrap().clone();
                            BV::from_str(ctx, width, &constant.to_string()).unwrap()
                        }
                        Operation::Equal => bool_to_bv(ctx, inputs[0]._eq(&inputs[1])),
                        Operation::Concat => inputs[0].concat(&inputs[1]),
                        Operation::Extract(slice) => inputs[0].extract(
                            (slice.end - 1).try_into().unwrap(),
                            slice.start.try_into().unwrap(),
                        ),
                        Operation::IfThenElse => {
                            (inputs[0]._eq(&BV::from_u64(ctx, 1, 1))).ite(&inputs[1], &inputs[2])
                        }
                        Operation::Not => inputs[0].bvnot(),
                        Operation::And => inputs[0].bvand(&inputs[1]),
                        Operation::Or => inputs[0].bvor(&inputs[1]),
                        Operation::Xor => inputs[0].bvxor(&inputs[1]),
                        Operation::Neg => inputs[0].bvneg(),
                        Operation::Add => inputs[0].bvadd(&inputs[1]),
                        Operation::Ule => bool_to_bv(ctx, inputs[0].bvule(&inputs[1])),
                        Operation::Ult => bool_to_bv(ctx, inputs[0].bvult(&inputs[1])),
                        Operation::Sle => bool_to_bv(ctx, inputs[0].bvsle(&inputs[1])),
                        Operation::Slt => bool_to_bv(ctx, inputs[0].bvslt(&inputs[1])),
                        Operation::Mul => inputs[0].bvmul(&inputs[1]),
                        Operation::Shl => inputs[0].bvshl(&inputs[1]),
                        Operation::LShr => inputs[0].bvlshr(&inputs[1]),
                        Operation::AShr => inputs[0].bvashr(&inputs[1]),
                        Operation::UDiv => inputs[0].bvudiv(&inputs[1]),
                        Operation::URem => inputs[0].bvurem(&inputs[1]),
                    }
                }
                Recipe::Slice(slice) => {
                    // Add compute dependencies for the slice
                    for (_, compute_dep) in self.dag.computable_slices.iter(slice.start..slice.end)
                    {
                        self.worklist.push(self.dag.find(*compute_dep));
                    }

                    self.input_var.extract(
                        (slice.end - 1).try_into().unwrap(),
                        (slice.start).try_into().unwrap(),
                    )
                }
                Recipe::NonComputable => unreachable!(),
            },
        ));
    }

    fn solve(
        &mut self,
        ctx: &'ctx z3::Context,
        solver: &'ctx z3::Solver<'ctx>,
    ) -> Result<(), Option<BigUint>> {
        for _ in 0..MAX_DEPTH {
            for eclass in std::mem::take(&mut self.worklist) {
                self.introduce_var_def(eclass, ctx, solver);
            }

            let result = solver.check();
            match result {
                z3::SatResult::Unsat => {
                    // No counter-example found, thus hypothesis has been proven.
                    return Ok(());
                }
                z3::SatResult::Unknown => {
                    // TODO: these require better handling, but I don't have time
                    return Err(None);
                }
                z3::SatResult::Sat => {
                    if !self.worklist.is_empty() {
                        // We can still recurse into child nodes, so continue to do so
                        continue;
                    }

                    // We found a counter-example!
                    let model = solver.get_model().unwrap();
                    let input_str = model
                        .eval(&self.input_var.to_int(false), false)
                        .unwrap()
                        .to_string();

                    let Ok(input) = BigUint::from_str(&input_str) else {
                        // Exact input was irrelevant since we didn't even need model
                        // completition
                        return Err(None);
                    };

                    return Err(Some(input));
                }
            }
        }

        Err(None)
    }
}

impl<V: Variable> SimulationCore<V> {
    /// Check if equality holds with z3
    fn z3_thinks_hypothesis_holds(
        &mut self,
        constants: &IndexSet<BigUint>,
        input_var: BV<'_>,
        ctx: &z3::Context,
        hypothesis: &Hypothesis<V>,
    ) -> bool {
        let solver = z3::Solver::new_for_logic(ctx, "QF_BV").unwrap();
        let mut dag_solve_context = DagSolveContext {
            dag: &self.dag,
            constants,
            input_var,
            reflected_vars: HashMap::new(),
            worklist: vec![],
        };

        match hypothesis {
            &Hypothesis::Equal(lhs, rhs) => {
                dag_solve_context.worklist.extend([lhs, rhs]);
                let lhs = dag_solve_context.z3_variable_for_eclass(ctx, lhs).clone();
                solver.assert(
                    &lhs._eq(dag_solve_context.z3_variable_for_eclass(ctx, rhs))
                        .not(),
                );
            }
            Hypothesis::IsConstant(lhs, value, _) => {
                dag_solve_context.worklist.push(*lhs);
                let lhs = dag_solve_context.z3_variable_for_eclass(ctx, *lhs).clone();
                solver.assert(
                    &lhs._eq(&BV::from_str(ctx, lhs.get_size(), &value.to_string()).unwrap())
                        .not(),
                );
            }
        }

        match dag_solve_context.solve(ctx, &solver) {
            Ok(()) => true,
            Err(Some(example)) => {
                self.good_vectors.push(example);
                false
            }
            Err(None) => false,
        }
    }

    /// Solve at most one hypothesis from pending set. We are not trying to solve more, as we want
    /// to benefit from faster equality/constant propogation in the egraph to potentially make
    /// other assertions redundant
    pub(in crate::solvers) fn prove_any_one_hypothesis(
        &mut self,
        constants: &IndexSet<BigUint>,
    ) -> Option<Hypothesis<V>> {
        while let Some(hypothesis) = self.candidate_hypotheses.pop_front() {
            // Check if hypothesis is now outdated
            let hypothesis = match hypothesis {
                Hypothesis::Equal(lhs, rhs) => {
                    let lhs = self.dag.find(lhs);
                    let rhs = self.dag.find(rhs);
                    if lhs == rhs {
                        continue;
                    }
                    Hypothesis::Equal(lhs, rhs)
                }
                Hypothesis::IsConstant(lhs, value, width) => {
                    let lhs = self.dag.find(lhs);
                    if self.dag.mappings[&lhs].is_constant() {
                        // NOTE: it would be unsound to report unsat here if constant is different, as
                        // we don't actually know if all assertions in the e-graph hold.
                        continue;
                    }
                    Hypothesis::IsConstant(lhs, value, width)
                }
            };

            let mut cfg = z3::Config::new();
            cfg.set_param_value("rlimit", "2000000");
            let ctx = z3::Context::new(&cfg);
            let input_var = BV::new_const(&ctx, "input", self.dag.input_len.try_into().unwrap());

            if self.z3_thinks_hypothesis_holds(constants, input_var, &ctx, &hypothesis) {
                return Some(hypothesis);
            }
        }

        None
    }
}
