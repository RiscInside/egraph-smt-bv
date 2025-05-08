//! Using primitives to intercept value unions and bitvector e-nodes

use std::sync::{Arc, Mutex};

use egglog::{
    ast::Symbol, constraint::SimpleTypeConstraint, sort::Sort, ArcSort, PrimitiveLike, UnionFind,
    Value,
};

pub(crate) trait Listener: Send + 'static {
    fn on_merge(&mut self, old: Value, new: Value);

    fn register_extra_primitives(_arc_self: Arc<Mutex<Self>>, _info: &mut egglog::TypeInfo) {}
}

pub(crate) struct ProxySort<L> {
    name: Symbol,
    intro_name: Symbol,
    #[cfg(debug_assertions)]
    wrapped_name: Symbol,
    wrapped: ArcSort,
    listener: Arc<Mutex<L>>,
}

impl<L> ProxySort<L> {
    pub(crate) fn new(
        name: Symbol,
        intro_name: Symbol,
        wrapped_sort: ArcSort,
        listener: Arc<Mutex<L>>,
    ) -> ProxySort<L> {
        ProxySort {
            name,
            intro_name,
            #[cfg(debug_assertions)]
            wrapped_name: wrapped_sort.name(),
            wrapped: wrapped_sort,
            listener,
        }
    }

    fn to_wrapped(&self, value: Value) -> Value {
        Value {
            bits: value.bits,
            #[cfg(debug_assertions)]
            tag: self.wrapped_name,
        }
    }

    fn to_proxy(&self, value: Value) -> Value {
        Value {
            bits: value.bits,
            #[cfg(debug_assertions)]
            tag: self.name,
        }
    }
}

impl<L> std::fmt::Debug for ProxySort<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ProxySort").field(&self.name).finish()
    }
}

impl<L: Listener> Sort for ProxySort<L> {
    fn name(&self) -> egglog::ast::Symbol {
        self.name
    }

    fn is_container_sort(&self) -> bool {
        true
    }

    fn is_eq_container_sort(&self) -> bool {
        self.wrapped.is_eq_sort()
    }

    fn inner_values(&self, value: &Value) -> Vec<(ArcSort, Value)> {
        vec![(self.wrapped.clone(), self.to_wrapped(*value))]
    }

    fn canonicalize(&self, value: &mut Value, unionfind: &UnionFind) -> bool {
        // Set value of the tag to what wrapped sort expects
        let old_value = self.to_wrapped(*value);
        *value = old_value;

        let changed = self.wrapped.canonicalize(value, unionfind);
        if changed {
            self.listener
                .lock()
                .expect("listeners shouldn't panic")
                .on_merge(old_value, *value);
        }

        *value = self.to_proxy(*value);
        changed
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(ProxyIntro {
            name: self.intro_name,
            proxy_sort: self.clone(),
            wrapped_sort: self.wrapped.clone(),
            #[cfg(debug_assertions)]
            proxy_sort_name: self.name,
        });

        L::register_extra_primitives(self.listener.clone(), info);
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
        let wrapped_value = Value {
            #[cfg(debug_assertions)]
            tag: self.wrapped_name,
            bits: value.bits,
        };

        let (cost, child) = extractor.find_best(wrapped_value, termdag, &self.wrapped)?;

        let term = termdag.app(self.intro_name, vec![child]);
        Some((cost, term))
    }
}

struct ProxyIntro {
    name: Symbol,
    proxy_sort: ArcSort,
    #[cfg(debug_assertions)]
    proxy_sort_name: Symbol,
    wrapped_sort: ArcSort,
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
            vec![self.wrapped_sort.clone(), self.proxy_sort.clone()],
            span.clone(),
        ))
    }

    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut egglog::EGraph>,
    ) -> Option<Value> {
        Some(Value {
            #[cfg(debug_assertions)]
            tag: self.proxy_sort_name,
            bits: values[0].bits,
        })
    }
}
