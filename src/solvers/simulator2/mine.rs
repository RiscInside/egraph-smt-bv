use crate::solvers::{
    simulator2::{dag::Recipe, SimulationCore},
    Variable,
};
use crate::solvers::{Hypothesis, Width};
use egglog::util::IndexSet;
use hashbrown::hash_map::Entry;
use hashbrown::HashMap;
use itertools::repeat_n;
use num_bigint::BigUint;
use rand::Rng;
use std::hash::{DefaultHasher, Hash, Hasher};

use super::Operation;

impl<V: Variable> SimulationCore<V> {
    fn run_on_input(
        &mut self,
        ordering: &[V],
        constants: &IndexSet<BigUint>,
        input: &mut BigUint,
    ) -> HashMap<V, (BigUint, Width)> {
        let mut values: HashMap<V, (BigUint, Width)> = HashMap::new();
        for eclass in ordering {
            let node = &self.dag.mappings[eclass];
            let value = match &node.recipe {
                Recipe::Computed {
                    op,
                    inputs: eclasses,
                } => {
                    let inputs: Vec<&BigUint> = eclasses
                        .iter()
                        .map(|eclass| &values[&eclass.get()].0)
                        .collect();

                    match op {
                        Operation::Constant { table_index } => {
                            constants.get_index(*table_index).unwrap().clone()
                        }
                        Operation::Equal => BigUint::from(inputs[0] == inputs[1]),
                        Operation::Concat => {
                            let rhs_width = values[&eclasses[1].get()].1;
                            inputs[0] << rhs_width | inputs[1]
                        }
                        Operation::Extract(slice) => {
                            (inputs[0] >> slice.start)
                                & ((BigUint::from(1u32) << (slice.end - slice.start))
                                    - BigUint::from(1u32))
                        }
                        Operation::IfThenElse => if inputs[0].bits() != 0 {
                            inputs[1]
                        } else {
                            inputs[2]
                        }
                        .clone(),
                        Operation::Not => {
                            inputs[0] ^ ((BigUint::from(1u32) << node.width) - BigUint::from(1u32))
                        }
                        Operation::And => inputs[0] & inputs[1],
                        Operation::Or => inputs[0] | inputs[1],
                        Operation::Xor => inputs[0] ^ inputs[1],
                        Operation::Neg => {
                            if inputs[0].bits() == 0 {
                                BigUint::from(0u32)
                            } else {
                                (BigUint::from(1u32) << node.width) - inputs[0]
                            }
                        }
                        Operation::Add => {
                            (inputs[0] + inputs[1])
                                & ((BigUint::from(1u32) << node.width) - BigUint::from(1u32))
                        }
                        Operation::Ule => BigUint::from(inputs[0] <= inputs[1]),
                        Operation::Ult => BigUint::from(inputs[0] < inputs[1]),
                        Operation::Sle => {
                            let width = values[&eclasses[1].get()].1;
                            let input0_high_bit = inputs[0] & (BigUint::from(1u32) << (width - 1));
                            let input1_high_bit = inputs[1] & (BigUint::from(1u32) << (width - 1));

                            let input0_rest = inputs[0] - &input0_high_bit;
                            let input1_rest = inputs[1] - &input1_high_bit;

                            BigUint::from(
                                (input1_high_bit + input0_rest) <= (input0_high_bit + input1_rest),
                            )
                        }
                        Operation::Slt => {
                            let width = values[&eclasses[1].get()].1;
                            let input0_high_bit = inputs[0] & (BigUint::from(1u32) << (width - 1));
                            let input1_high_bit = inputs[1] & (BigUint::from(1u32) << (width - 1));

                            let input0_rest = inputs[0] - &input0_high_bit;
                            let input1_rest = inputs[1] - &input1_high_bit;

                            BigUint::from(
                                (input1_high_bit + input0_rest) < (input0_high_bit + input1_rest),
                            )
                        }
                        Operation::Mul => {
                            (inputs[0] * inputs[1])
                                & ((BigUint::from(1u32) << node.width) - BigUint::from(1u32))
                        }
                        Operation::Shl => {
                            if inputs[1].bits() > (Width::BITS - node.width.leading_zeros()) as u64
                            {
                                BigUint::from(0u32)
                            } else {
                                (inputs[0] << Width::try_from(inputs[1]).unwrap())
                                    & (((BigUint::from(1u32)) << node.width) - BigUint::from(1u32))
                            }
                        }
                        Operation::LShr => {
                            if inputs[1].bits() > (Width::BITS - node.width.leading_zeros()) as u64
                            {
                                BigUint::from(0u32)
                            } else {
                                inputs[0] >> Width::try_from(inputs[1]).unwrap()
                            }
                        }
                        Operation::AShr => todo!(),
                    }
                }
                Recipe::Slice(slice) => {
                    ((input as &BigUint) >> slice.start)
                        & ((BigUint::from(1u32) << (slice.end - slice.start)) - BigUint::from(1u32))
                }
                Recipe::NonComputable => unreachable!(),
            };

            for slice in node.input_portions.iter() {
                let target_range =
                    ((BigUint::from(1u32) << slice.width()) - BigUint::from(1u32)) << slice.start;
                *input &= (input as &BigUint) ^ target_range;
                *input |= &value << slice.start;
            }

            values.insert(*eclass, (value, node.width));
        }

        values
    }

    pub(in crate::solvers) fn mine_hypotheses(
        &mut self,
        constants: &IndexSet<BigUint>,
        extra_trials: usize,
    ) {
        self.candidate_hypotheses.clear();

        let ordering = self.dag.rebuild();
        let distribution = num_bigint::RandomBits::new(self.dag.input_len);

        enum ConstantState {
            MaybeConstant,
            Matches(BigUint),
            NotAConstant,
        }

        let mut rolling_results_map: HashMap<V, (DefaultHasher, ConstantState, Width)> = ordering
            .iter()
            .map(|eclass| {
                let mut hasher = DefaultHasher::new();
                let node = &self.dag.mappings[eclass];
                let width = node.width;
                hasher.write_u64(width);
                (
                    *eclass,
                    (
                        hasher,
                        if node.is_constant() {
                            // Counter-intuitive, but the goal here is to prevent smt solver from trying to prove what we already know
                            ConstantState::NotAConstant
                        } else {
                            ConstantState::MaybeConstant
                        },
                        width,
                    ),
                )
            })
            .collect();

        let unsat_vectors = self.good_vectors.clone();

        // Start with good vectors, then focus on new extra_trials vectors
        for input in unsat_vectors
            .into_iter()
            .map(Some)
            .chain(repeat_n(None, extra_trials))
        {
            let mut input = input.unwrap_or_else(|| self.rng.sample(distribution));
            let results = self.run_on_input(&ordering, constants, &mut input);

            for (value, (result, _)) in results {
                let rolling_hashes_entry = rolling_results_map.get_mut(&value).unwrap();

                result.hash(&mut rolling_hashes_entry.0);

                match &rolling_hashes_entry.1 {
                    ConstantState::MaybeConstant => {
                        rolling_hashes_entry.1 = ConstantState::Matches(result);
                    }
                    ConstantState::Matches(prev_result) => {
                        if prev_result != &result {
                            rolling_hashes_entry.1 = ConstantState::NotAConstant;
                        }
                    }
                    ConstantState::NotAConstant => {}
                }
            }
        }

        let mut value_for_hash = HashMap::new();

        for current in ordering.iter() {
            let (hasher, constant_state, width) = rolling_results_map.remove(current).unwrap();

            match constant_state {
                ConstantState::MaybeConstant => unreachable!(),
                ConstantState::Matches(settled_on) => {
                    self.candidate_hypotheses
                        .push_back(Hypothesis::IsConstant(*current, settled_on, width));
                    // don't need equality checks, those will be introduced via equality with a constant
                    continue;
                }
                ConstantState::NotAConstant => {}
            }

            let key = hasher.finish();
            match value_for_hash.entry(key) {
                Entry::Occupied(occupied) => {
                    self.candidate_hypotheses
                        .push_back(Hypothesis::Equal(*occupied.get(), *current));
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(*current);
                }
            };
        }
    }
}
