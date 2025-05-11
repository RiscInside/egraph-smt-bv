//! Using primitives to intercept SMT2LIB value unions. Additionally, we store width of the bitvector
//! alongside the egglog value (in high bits of the bitvector).
//!
//! We assume here that width is bounded by 16 bits.

use crate::solvers::{SolversRef, Width};
use egglog::{
    ast::Symbol,
    constraint::SimpleTypeConstraint,
    sort::{EqSort, FromSort, I64Sort, IntoSort, Sort},
    ArcSort, EGraph, PrimitiveLike, UnionFind, Value,
};
use std::sync::Arc;

const WIDTH_BITS: u64 = 20;
const WIDTH_OFFSET: u64 = 64 - WIDTH_BITS;
const VALUE_MASK: u64 = (1u64 << WIDTH_OFFSET) - 1;

struct Proxy {
    value: Value,
    width: Width,
}

pub(crate) struct ProxySort {
    name: Symbol,
    intro_name: Symbol,
    #[cfg(debug_assertions)]
    v: Symbol,
    v_sort: ArcSort,
    solvers: SolversRef,
}

impl std::fmt::Debug for ProxySort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ProxySort")
    }
}

impl FromSort for Proxy {
    type Sort = ProxySort;

    fn load(
        #[cfg_attr(not(debug_assertions), allow(unused_variables))] sort: &Self::Sort,
        value: &Value,
    ) -> Proxy {
        Proxy {
            value: Value {
                bits: value.bits & VALUE_MASK,
                #[cfg(debug_assertions)]
                tag: sort.v,
            },
            width: value.bits >> WIDTH_OFFSET,
        }
    }
}

impl IntoSort for Proxy {
    type Sort = ProxySort;

    fn store(
        self,
        #[cfg_attr(not(debug_assertions), allow(unused_variables))] sort: &Self::Sort,
    ) -> Option<Value> {
        if self.width >= (1 << WIDTH_BITS) || self.value.bits > VALUE_MASK {
            return None;
        }

        Some(Value {
            bits: self.value.bits | (self.width << WIDTH_OFFSET),
            #[cfg(debug_assertions)]
            tag: sort.name,
        })
    }
}

impl ProxySort {
    pub(crate) fn new(egraph: &EGraph, solvers: SolversRef) -> ProxySort {
        ProxySort {
            name: "Proxy".into(),
            intro_name: "proxy".into(),
            #[cfg(debug_assertions)]
            v: "V".into(),
            v_sort: egraph
                .get_sort_by(|sort: &Arc<EqSort>| sort.name == "V".into())
                .unwrap(),
            solvers,
        }
    }
}

impl Sort for ProxySort {
    fn name(&self) -> egglog::ast::Symbol {
        self.name
    }

    fn is_container_sort(&self) -> bool {
        true
    }

    fn is_eq_container_sort(&self) -> bool {
        true
    }

    fn inner_values(&self, value: &Value) -> Vec<(ArcSort, Value)> {
        vec![(self.v_sort.clone(), Proxy::load(self, value).value)]
    }

    fn canonicalize(&self, value: &mut Value, unionfind: &UnionFind) -> bool {
        let proxy = Proxy::load(self, value);
        // Set value of the tag to what wrapped sort expects
        *value = proxy.value;

        let changed = self.v_sort.canonicalize(value, unionfind);
        if changed {
            self.solvers
                .lock()
                .expect("listeners shouldn't panic")
                .on_merge(proxy.value, *value, proxy.width);
        }

        *value = Proxy::store(
            Proxy {
                value: *value,
                width: proxy.width,
            },
            self,
        )
        .unwrap();
        changed
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(ProxyIntro {
            name: self.intro_name,
            proxy_sort: self.clone(),
            v_sort: self.v_sort.clone(),
            i64_sort: info.get_sort_nofail(),
        });
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn extract_term(
        &self,
        _egraph: &egglog::EGraph,
        value: Value,
        extractor: &egglog::extract::Extractor,
        termdag: &mut egglog::TermDag,
    ) -> Option<(egglog::extract::Cost, egglog::Term)> {
        let proxy = Proxy::load(self, &value);
        let (cost, child) = extractor.find_best(proxy.value, termdag, &self.v_sort)?;
        let lit = termdag.lit(egglog::ast::Literal::Int(proxy.width as i64));
        let term = termdag.app(self.intro_name, vec![child, lit]);
        Some((cost, term))
    }
}

struct ProxyIntro {
    name: Symbol,
    proxy_sort: Arc<ProxySort>,
    v_sort: ArcSort,
    i64_sort: Arc<I64Sort>,
}

impl PrimitiveLike for ProxyIntro {
    fn name(&self) -> Symbol {
        self.name
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(SimpleTypeConstraint::new(
            self.name,
            vec![
                self.v_sort.clone(),
                self.i64_sort.clone(),
                self.proxy_sort.clone(),
            ],
            span.clone(),
        ))
    }

    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut egglog::EGraph>,
    ) -> Option<Value> {
        Proxy::store(
            Proxy {
                value: values[0],
                width: values[1].bits,
            },
            &self.proxy_sort,
        )
    }
}
