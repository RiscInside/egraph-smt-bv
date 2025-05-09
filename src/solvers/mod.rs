use std::sync::{Arc, Mutex};

use crate::{plan::PlanResult, Context};
use anyhow::Context as _;
use egglog::{
    ast::{Command, GenericSchedule, RunConfig, Symbol},
    sort::{EqSort, FromSort, I64Sort, IntoSort, UnitSort},
    span, ArcSort, EGraph, PrimitiveLike, Value,
};

/// Width of any particular bitvector
type Width = u64;

pub(crate) mod bvconst;
pub(crate) mod linsolve;

use bvconst::{BvConstSort, BvConstTable};
use linsolve::LinearSolver;

use crate::intercept::{Listener, ProxySort};

impl LinearSolver<Value> {
    #[allow(dead_code)]
    fn dump_egglog(&self) {
        self.dump(|val| format!("v{}", val.bits));
    }
}

/// Combined solvers state
pub(crate) struct Solvers {
    /// Linear solver
    pub(crate) linear: LinearSolver<Value>,
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

impl Listener for Solvers {
    fn on_merge(&mut self, old: Value, new: Value) {
        self.linear.assert_equal(old, new);
    }

    fn register_extra_primitives(arc_self: Arc<Mutex<Self>>, info: &mut egglog::TypeInfo) {
        info.add_primitive(AssertAdd {
            v_sort: info
                .get_sort_by(|sort: &Arc<EqSort>| sort.name.as_str() == "V")
                .unwrap(),
            unit_sort: info.get_sort_by(|_| true).unwrap(),
            int_sort: info.get_sort_by(|_| true).unwrap(),
            solvers: arc_self.clone(),
        });
    }
}

impl Solvers {
    fn report_new_equalities(&mut self, egraph: &mut EGraph) -> bool {
        let mut changed = false;
        self.linear.process_new_unions(|lhs, rhs| {
            egraph.union(lhs.bits, rhs.bits, self.v_symbol);
            changed = true;
        });
        changed
    }

    fn assert_is_add(&mut self, lhs: Value, rhs: Value, result: Value, width: Width) {
        self.linear.assert_is_add(lhs, rhs, result, width);
    }
}

pub(crate) fn create_solvers(egraph: &mut EGraph) -> Arc<Mutex<Solvers>> {
    let solver = Arc::new(Mutex::new(Solvers::default()));
    let v_sort: Arc<EqSort> = egraph
        .get_sort_by(|sort: &Arc<EqSort>| sort.name.as_str() == "V")
        .context("No value sort defined yet")
        .unwrap();

    egraph
        .add_arcsort(
            Arc::new(ProxySort::new(
                "Proxy".into(),
                "proxy".into(),
                v_sort,
                solver.clone(),
            )),
            span!(),
        )
        .context("Adding proxy sort")
        .unwrap();

    egraph
        .add_arcsort(Arc::new(BvConstSort::new(solver.clone())), span!())
        .context("Adding bit-vector constant sort")
        .unwrap();

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
        let solver = &mut self.solvers.lock().unwrap();
        solver.assert_is_add(
            values[0],
            values[1],
            values[2],
            i64::load(&self.int_sort, &values[3]).try_into().unwrap(),
        );

        IntoSort::store((), &self.unit_sort)
    }
}

impl Context {
    pub(crate) fn solvers_tactic(&mut self) -> PlanResult<bool> {
        let mut changed = false;
        let mut changing = true;
        while changing {
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

            // Process inferred unions
            let mut solvers = self.solvers.lock().unwrap();
            changing = solvers.report_new_equalities(&mut self.egraph);
            if changing {
                changed = true;
            }
            drop(solvers); // Need to drop as inferred equalities will propogate back to solvers here

            // Rebuild the e-graph again
            self.egraph.rebuild_nofail();
        }

        Ok(changed)
    }
}
