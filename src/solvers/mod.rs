use std::sync::{Arc, Mutex};

use crate::{plan::PlanResult, Context};
use anyhow::Context as _;
use egglog::{
    ast::{Command, GenericSchedule, RunConfig, Symbol},
    sort::{EqSort, I64Sort, IntoSort, UnitSort},
    span, ArcSort, EGraph, PrimitiveLike, Value,
};

/// Width of any particular bitvector
type Width = u64;

pub(crate) mod bvconst;
pub(crate) mod linsolve2;
pub(crate) mod proxy;

use bvconst::{BvConst, BvConstSort, BvConstTable};
use proxy::ProxySort;

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

/// Combined solvers state
pub(crate) struct Solvers {
    /// Linear solver
    linear: linsolve2::Solver<Value>,
    /// Table of bitvector constants
    pub(crate) bv_constants_index: BvConstTable,
    /// Symbol for "V"
    pub(crate) v_symbol: Symbol,
}

pub(crate) type SolversRef = Arc<Mutex<Solvers>>;

impl Default for Solvers {
    fn default() -> Self {
        Self {
            linear: Default::default(),
            bv_constants_index: Default::default(),
            v_symbol: "V".into(),
        }
    }
}

impl Solvers {
    fn on_merge(&mut self, old: Value, new: Value, width: Width) {
        self.linear.assert_is_equal(old, new, width);
    }

    fn load_constant(&self, value: Value) -> BvConst {
        self.bv_constants_index
            .get_index(value.bits as usize)
            .unwrap()
            .clone()
    }

    fn assert_is_add(&mut self, lhs: Value, rhs: Value, result: Value, width: Width) {
        self.linear.assert_is_add(lhs, rhs, result, width);
    }

    fn assert_is_mul_const(&mut self, lhs: Value, constant: Value, result: Value, width: Width) {
        let constant = self.load_constant(constant).0;
        self.linear.assert_is_scaled(lhs, constant, result, width);
    }

    fn assert_is_constant(&mut self, constant: Value, val: Value, width: Width) {
        let constant = self.load_constant(constant).0;
        self.linear.assert_is_constant(constant, val, width);
    }
}

pub(crate) fn create_solvers(egraph: &mut EGraph) -> Arc<Mutex<Solvers>> {
    let solver = Arc::new(Mutex::new(Solvers::default()));
    let v_sort: Arc<EqSort> = egraph
        .get_sort_by(|sort: &Arc<EqSort>| sort.name.as_str() == "V")
        .context("No value sort defined yet")
        .unwrap();

    egraph
        .add_arcsort(Arc::new(BvConstSort::new(solver.clone())), span!())
        .context("Adding bit-vector constant sort")
        .unwrap();

    egraph
        .add_arcsort(Arc::new(ProxySort::new(egraph, solver.clone())), span!())
        .context("Adding proxy sort")
        .unwrap();

    let unit_sort: Arc<UnitSort> = egraph.get_sort_by(|_| true).unwrap();
    let int_sort: Arc<I64Sort> = egraph.get_sort_by(|_| true).unwrap();
    let bvconst_sort: Arc<BvConstSort> = egraph.get_sort_by(|_| true).unwrap();

    egraph.add_primitive(AssertAdd {
        v_sort: v_sort.clone(),
        unit_sort: unit_sort.clone(),
        int_sort: int_sort.clone(),
        solvers: solver.clone(),
    });

    egraph.add_primitive(AssertMulConstant {
        v_sort: v_sort.clone(),
        unit_sort: unit_sort.clone(),
        int_sort: int_sort.clone(),
        bvconst_sort: bvconst_sort.clone(),
        solvers: solver.clone(),
    });

    egraph.add_primitive(AssertConstant {
        v_sort: v_sort.clone(),
        unit_sort: unit_sort.clone(),
        int_sort: int_sort.clone(),
        bvconst_sort: bvconst_sort.clone(),
        solvers: solver.clone(),
    });

    solver
}

struct AssertAdd {
    v_sort: ArcSort,
    unit_sort: Arc<UnitSort>,
    int_sort: Arc<I64Sort>,
    solvers: Arc<Mutex<Solvers>>,
}

impl PrimitiveLike for AssertAdd {
    fn name(&self) -> egglog::ast::Symbol {
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

        IntoSort::store((), &self.unit_sort)
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
    fn name(&self) -> egglog::ast::Symbol {
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
        IntoSort::store((), &self.unit_sort)
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
    fn name(&self) -> egglog::ast::Symbol {
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
        IntoSort::store((), &self.unit_sort)
    }
}

impl Context {
    pub(crate) fn solvers_tactic(&mut self) -> PlanResult<bool> {
        // Rebuild e-graph to get all union-find updates
        self.egraph.rebuild_nofail();

        // Run solve_premises ruleset to send premises to solvers
        self.run_cmds(vec![Command::RunSchedule(GenericSchedule::Run(
            span!(),
            RunConfig {
                ruleset: "solve_premises".into(),
                until: None,
            },
        ))])?;

        let mut solvers = self.solvers.lock().unwrap();

        // Push equalities from the union solver
        let v_symbol = solvers.v_symbol;
        let mut unions_count = 0;
        solvers.linear.solve_all_pending(|lhs, rhs| {
            unions_count += 1;
            self.egraph.union(lhs.bits, rhs.bits, v_symbol);
        });
        drop(solvers);

        // Rebuild the e-graph again
        self.egraph.rebuild_nofail();

        if unions_count != 0 {
            self.text(&format!(
                "Linear solver submitted {} unions (not all of them necessarily canonical)",
                unions_count
            ))?;
        }

        Ok(unions_count != 0)
    }
}
