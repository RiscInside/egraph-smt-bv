use std::{
    fs::File,
    io::Write as _,
    ops::DerefMut,
    path::PathBuf,
    sync::{Arc, Mutex},
};

use crate::{plan::PlanResult, Context};
use anyhow::Context as _;
use egglog::{
    ast::Symbol,
    call, lit,
    sort::{EqSort, FromSort as _, I64Sort, StringSort, UnitSort},
    span, ArcSort, EGraph, PrimitiveLike, Value,
};

/// Width of any particular bitvector
type Width = u64;

mod slice;

pub(crate) mod bvconst;
pub(crate) mod bvrange;
pub(crate) mod linsolve2;
pub(crate) mod proxy;
pub(crate) mod simulator2;

use bvconst::{BvConstSort, BvConstTable};
use bvrange::{BvRangeSort, BvRangeTable};
use num_bigint::BigUint;
use proxy::ProxySort;
use simulator2::{Operation, SimulationCore};
use slice::Slice;

/// A trait for symbolic variable types. This is implemented for [`Value`] and [`u64`]
/// (for testing purposes).
pub(super) trait Variable: Copy + Ord + std::hash::Hash + std::fmt::Debug + 'static {
    /// Display variable for debugging purposes
    fn show(&self) -> String;
}

impl Variable for u64 {
    fn show(&self) -> String {
        format!("v{self}")
    }
}

impl Variable for Value {
    fn show(&self) -> String {
        format!("v{}", self.bits)
    }
}

#[derive(Debug)]
pub(crate) enum Hypothesis<V: Variable> {
    Equal(V, V),
    IsConstant(V, BigUint, Width),
}

/// Combined solvers state
pub(crate) struct Solvers {
    /// Linear solver
    linear: linsolve2::Solver<Value>,
    /// Simulation core
    sim_core: simulator2::SimulationCore<Value>,
    /// Sort of values
    v_sort: ArcSort,
    /// Table of bitvector constants
    pub(crate) bv_constants_index: BvConstTable,
    /// Table of bitvector ranges
    pub(crate) bv_ranges_index: BvRangeTable,
    /// Symbol for "V"
    pub(crate) v_symbol: Symbol,
}

pub(crate) type SolversRef = Arc<Mutex<Solvers>>;

impl Solvers {
    pub(crate) fn new(egraph: &mut EGraph) -> Arc<Mutex<Solvers>> {
        let v_sort: Arc<EqSort> = egraph
            .get_sort_by(|sort: &Arc<EqSort>| sort.name.as_str() == "V")
            .context("No value sort defined yet")
            .unwrap();

        let solver = Arc::new(Mutex::new(Solvers {
            linear: Default::default(),
            sim_core: SimulationCore::default(),
            v_sort: v_sort.clone(),
            bv_constants_index: Default::default(),
            bv_ranges_index: Default::default(),
            v_symbol: "V".into(),
        }));

        egraph
            .add_arcsort(Arc::new(BvConstSort::new(solver.clone())), span!())
            .context("Adding bit-vector constant sort")
            .unwrap();

        egraph
            .add_arcsort(Arc::new(BvRangeSort::new(solver.clone())), span!())
            .context("Adding bit-vector range sort")
            .unwrap();

        egraph
            .add_arcsort(Arc::new(ProxySort::new(egraph, solver.clone())), span!())
            .context("Adding proxy sort")
            .unwrap();

        let unit_sort: Arc<UnitSort> = egraph.get_sort_by(|_| true).unwrap();
        let int_sort: Arc<I64Sort> = egraph.get_sort_by(|_| true).unwrap();
        let bvconst_sort: Arc<BvConstSort> = egraph.get_sort_by(|_| true).unwrap();
        let string_sort: Arc<StringSort> = egraph.get_sort_by(|_| true).unwrap();

        egraph.add_primitive(AssertConstant {
            v_sort: v_sort.clone(),
            unit_sort: unit_sort.clone(),
            int_sort: int_sort.clone(),
            bvconst_sort: bvconst_sort.clone(),
            solvers: solver.clone(),
        });

        let mut add_sim_binop = |name: &'static str, binop| {
            egraph.add_primitive(AssertSimulatorBinOp {
                v_sort: v_sort.clone(),
                int_sort: int_sort.clone(),
                unit_sort: unit_sort.clone(),
                name: name.into(),
                handler: move |solver, lhs, rhs, result, width| {
                    solver.assert_is_binop(binop, lhs, rhs, result, width)
                },
                solvers: solver.clone(),
            })
        };

        add_sim_binop("solvers-eq", Operation::Equal);
        add_sim_binop("solvers-concat", Operation::Concat);
        add_sim_binop("solvers-and", Operation::And);
        add_sim_binop("solvers-or", Operation::Or);
        add_sim_binop("solvers-xor", Operation::Xor);
        add_sim_binop("solvers-mul", Operation::Mul);
        add_sim_binop("solvers-shl", Operation::Shl);
        add_sim_binop("solvers-lshr", Operation::LShr);
        add_sim_binop("solvers-ashr", Operation::AShr);
        add_sim_binop("solvers-ule", Operation::Ule);
        add_sim_binop("solvers-ult", Operation::Ult);
        add_sim_binop("solvers-sle", Operation::Sle);
        add_sim_binop("solvers-slt", Operation::Slt);
        add_sim_binop("solvers-udiv", Operation::UDiv);
        add_sim_binop("solvers-urem", Operation::URem);

        let mut add_sim_unop = |name: &'static str, unop| {
            egraph.add_primitive(AssertSimulatorUnOp {
                v_sort: v_sort.clone(),
                int_sort: int_sort.clone(),
                unit_sort: unit_sort.clone(),
                name: name.into(),
                handler: move |solver, operand, result, width| {
                    solver.assert_is_unop(unop, operand, result, width);
                },
                solvers: solver.clone(),
            });
        };

        add_sim_unop("solvers-not", Operation::Not);
        add_sim_unop("solvers-neg", Operation::Neg);

        egraph.add_primitive(AssertAdd {
            v_sort: v_sort.clone(),
            unit_sort: unit_sort.clone(),
            int_sort: int_sort.clone(),
            solvers: solver.clone(),
        });

        egraph.add_primitive(AssertIfThenElse {
            v_sort: v_sort.clone(),
            int_sort: int_sort.clone(),
            unit_sort: unit_sort.clone(),
            solvers: solver.clone(),
        });

        egraph.add_primitive(AssertExtract {
            v_sort: v_sort.clone(),
            unit_sort: unit_sort.clone(),
            solvers: solver.clone(),
            int_sort: int_sort.clone(),
        });

        egraph.add_primitive(AssertMulConstant {
            v_sort: v_sort.clone(),
            unit_sort: unit_sort.clone(),
            int_sort: int_sort.clone(),
            bvconst_sort: bvconst_sort.clone(),
            solvers: solver.clone(),
        });

        egraph.add_primitive(AssertInput {
            v_sort: v_sort.clone(),
            unit_sort: unit_sort.clone(),
            int_sort: int_sort.clone(),
            string_sort: string_sort.clone(),
            solvers: solver.clone(),
        });

        solver
    }

    fn on_merge(&mut self, old: Value, new: Value, width: Width) {
        self.linear.assert_is_equal(old, new, width);
        self.sim_core.union(old, new);
    }

    fn load_constant(&self, value: Value) -> BigUint {
        self.bv_constants_index
            .get_index(value.bits as usize)
            .unwrap()
            .clone()
    }

    fn assert_extract(&mut self, input: Value, i: Width, j: Width, out: Value) {
        self.sim_core.add_extract(
            input,
            Slice {
                start: j,
                end: i + 1,
            },
            out,
        );
    }

    fn assert_is_input(&mut self, input: Value, name: String, width: Width) {
        self.sim_core.add_input(input, name, width);
    }

    fn assert_if_then_else(
        &mut self,
        cond: Value,
        then: Value,
        otherwise: Value,
        out: Value,
        width: Width,
    ) {
        self.sim_core.add_operation(
            simulator2::Operation::IfThenElse,
            vec![cond, then, otherwise],
            out,
            width,
        );
    }

    fn assert_is_add(&mut self, lhs: Value, rhs: Value, result: Value, width: Width) {
        self.sim_core
            .add_operation(simulator2::Operation::Add, vec![lhs, rhs], result, width);
        self.linear.assert_is_add(lhs, rhs, result, width);
    }

    fn assert_is_mul_const(&mut self, lhs: Value, constant: Value, result: Value, width: Width) {
        let constant = self.load_constant(constant);
        self.linear.assert_is_scaled(lhs, constant, result, width);
    }

    fn assert_is_unop(
        &mut self,
        op: simulator2::Operation,
        input: Value,
        result: Value,
        width: Width,
    ) {
        self.sim_core.add_operation(op, vec![input], result, width);
    }

    fn assert_is_binop(
        &mut self,
        op: simulator2::Operation,
        lhs: Value,
        rhs: Value,
        result: Value,
        width: Width,
    ) {
        self.sim_core
            .add_operation(op, vec![lhs, rhs], result, width);
    }

    fn assert_is_constant(&mut self, constant: Value, val: Value, width: Width) {
        let big_uint = self.load_constant(constant);
        self.sim_core.add_operation(
            simulator2::Operation::Constant {
                table_index: constant.bits as usize,
            },
            vec![],
            val,
            width,
        );
        self.linear.assert_is_constant(big_uint, val, width);
    }
}

struct AssertAdd {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    int_sort: Arc<I64Sort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertAdd {
    fn name(&self) -> Symbol {
        "solvers-add".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "solvers-add".into(),
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
        let solver = &mut self.solvers.lock().unwrap();
        solver.assert_is_add(values[0], values[1], values[2], values[3].bits);
        Some(Value::unit())
    }
}

struct AssertConstant {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    bvconst_sort: Arc<BvConstSort>,
    int_sort: Arc<I64Sort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertConstant {
    fn name(&self) -> Symbol {
        "solvers-constant".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "solvers-constant".into(),
            vec![
                self.bvconst_sort.clone(),
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
        let solver: &mut std::sync::MutexGuard<'_, Solvers> = &mut self.solvers.lock().unwrap();
        solver.assert_is_constant(values[0], values[1], values[2].bits);
        Some(Value::unit())
    }
}

struct AssertMulConstant {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    bvconst_sort: Arc<BvConstSort>,
    int_sort: Arc<I64Sort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertMulConstant {
    fn name(&self) -> Symbol {
        "solvers-mul-constant".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "solvers-mul-constant".into(),
            vec![
                self.v_sort.clone(),
                self.bvconst_sort.clone(),
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
        let solver: &mut std::sync::MutexGuard<'_, Solvers> = &mut self.solvers.lock().unwrap();
        solver.assert_is_mul_const(values[0], values[1], values[2], values[3].bits);
        Some(Value::unit())
    }
}

struct AssertSimulatorUnOp<F: Fn(&mut Solvers, Value, Value, Width)> {
    v_sort: ArcSort,
    int_sort: Arc<I64Sort>,
    unit_sort: Arc<UnitSort>,
    solvers: Arc<Mutex<Solvers>>,
    name: Symbol,
    handler: F,
}

impl<F: Fn(&mut Solvers, Value, Value, Width)> PrimitiveLike for AssertSimulatorUnOp<F> {
    fn name(&self) -> Symbol {
        self.name
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            self.name,
            vec![
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
        let solver = &mut self.solvers.lock().unwrap();
        (self.handler)(solver, values[0], values[1], values[2].bits);
        Some(Value::unit())
    }
}

struct AssertSimulatorBinOp<F: Fn(&mut Solvers, Value, Value, Value, Width)> {
    v_sort: ArcSort,
    int_sort: Arc<I64Sort>,
    unit_sort: Arc<UnitSort>,
    solvers: Arc<Mutex<Solvers>>,
    name: Symbol,
    handler: F,
}

impl<F: Fn(&mut Solvers, Value, Value, Value, Width)> PrimitiveLike for AssertSimulatorBinOp<F> {
    fn name(&self) -> Symbol {
        self.name
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            self.name,
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
        let solver = &mut self.solvers.lock().unwrap();
        (self.handler)(solver, values[0], values[1], values[2], values[3].bits);

        Some(Value::unit())
    }
}

struct AssertIfThenElse {
    v_sort: ArcSort,
    int_sort: Arc<I64Sort>,
    unit_sort: Arc<UnitSort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertIfThenElse {
    fn name(&self) -> Symbol {
        "solvers-ite".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "solvers-ite".into(),
            vec![
                self.v_sort.clone(),
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
        let solver = &mut self.solvers.lock().unwrap();
        solver.assert_if_then_else(values[0], values[1], values[2], values[3], values[4].bits);
        Some(Value::unit())
    }
}

struct AssertExtract {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    int_sort: Arc<I64Sort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertExtract {
    fn name(&self) -> Symbol {
        "solvers-extract".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "solvers-extract".into(),
            vec![
                self.v_sort.clone(),
                self.int_sort.clone(),
                self.int_sort.clone(),
                self.v_sort.clone(),
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
        let solver = &mut self.solvers.lock().unwrap();

        solver.assert_extract(values[0], values[1].bits, values[2].bits, values[3]);
        Some(Value::unit())
    }
}

struct AssertInput {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    int_sort: Arc<I64Sort>,
    string_sort: Arc<StringSort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertInput {
    fn name(&self) -> Symbol {
        "solvers-input".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(egglog::constraint::SimpleTypeConstraint::new(
            "solvers-input".into(),
            vec![
                self.v_sort.clone(),
                self.string_sort.clone(),
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
        let solver = &mut self.solvers.lock().unwrap();
        let name = Symbol::load(&self.string_sort, &values[1]);
        solver.assert_is_input(values[0], name.to_string(), values[2].bits);
        Some(Value::unit())
    }
}

impl Context {
    pub(crate) fn linsolve_tactic(&mut self) -> PlanResult<bool> {
        self.egraph.rebuild_nofail();
        self.text("Running linsolve tactic")?;

        let mut unions_count = 0;
        {
            let mut solvers_guard = self.solvers.lock().unwrap();
            let solvers = solvers_guard.deref_mut();

            // Push equalities from the union solver
            let v_symbol = solvers.v_symbol;
            solvers.linear.solve_all_pending(|lhs, rhs| {
                let lhs = self.egraph.find(&solvers.v_sort, lhs);
                let rhs = self.egraph.find(&solvers.v_sort, rhs);

                if lhs != rhs {
                    unions_count += 1;
                    self.egraph.union(lhs.bits, rhs.bits, v_symbol);
                }
            });
        }

        // Rebuild the e-graph again
        self.egraph.rebuild_nofail();
        self.text(&format!("Linear solver submitted {} unions", unions_count))?;

        Ok(unions_count != 0)
    }

    pub(crate) fn mine_hypotheses_tactic(&mut self) -> PlanResult<bool> {
        self.text("Running simulation tactic")?;
        self.egraph.rebuild_nofail();

        let mut solvers_guard = self.solvers.lock().unwrap();
        let solvers = solvers_guard.deref_mut();

        solvers
            .sim_core
            .mine_hypotheses(&solvers.bv_constants_index, 10);

        let hypotheses_pending = solvers.sim_core.hypotheses_pending();

        drop(solvers_guard);
        self.egraph.rebuild_nofail();

        self.text(&format!(
            "Simulation mined out {} hypotheses (some of them potentially redundant)",
            hypotheses_pending
        ))?;

        Ok(hypotheses_pending != 0)
    }

    pub(crate) fn smt_solve_one_tactic(&mut self) -> PlanResult<bool> {
        self.egraph.rebuild_nofail();
        self.text("Running smt-one tactic")?;

        let (hypotheses, v_symbol, remaining) = {
            let mut solvers_guard = self.solvers.lock().unwrap();
            let solvers = solvers_guard.deref_mut();

            let Some(hypotheses) = solvers
                .sim_core
                .prove_any_one_hypothesis(&solvers.bv_constants_index)
            else {
                return Ok(false);
            };

            (
                hypotheses,
                solvers.v_symbol,
                solvers.sim_core.hypotheses_pending(),
            )
        };

        // Reflect the hypothesis back to the e-graph
        match hypotheses {
            Hypothesis::Equal(lhs, rhs) => {
                self.egraph.union(lhs.bits, rhs.bits, v_symbol);
            }
            Hypothesis::IsConstant(lhs, value, width) => {
                let (_, result) = self
                    .egraph
                    .eval_expr(&call!(
                        "BvConst",
                        [
                            call!(
                                "bvconst-from-string",
                                [lit!(Symbol::from(value.to_string()))]
                            ),
                            lit!(i64::try_from(width).unwrap())
                        ]
                    ))
                    .unwrap();
                self.egraph.union(lhs.bits, result.bits, v_symbol);
            }
        }

        // Rebuild the e-graph again
        self.egraph.rebuild_nofail();

        self.text(&format!(
            "SMT solver contributed to the e-graph. {remaining} hypothesis left to solve"
        ))?;

        Ok(true)
    }

    pub(crate) fn dump_dag_tactic(&mut self, path: &PathBuf) -> anyhow::Result<()> {
        let mut solvers = self.solvers.lock().unwrap();
        let summary = solvers.sim_core.summary();
        drop(solvers);

        File::create(path)?.write_all(summary.as_bytes())?;
        Ok(())
    }
}
