use std::{
    collections::{BTreeSet, HashMap},
    fmt::Write as _,
    ops::{BitAnd, BitOr, Not, Sub},
};

use bittle::{Bits, BitsMut};

type State = u16;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct StateBitSet {
    set: Vec<usize>,
    len: State,
}

impl StateBitSet {
    fn new(states: State) -> StateBitSet {
        StateBitSet {
            set: vec![0; states.div_ceil(usize::BITS as State) as usize],
            len: states,
        }
    }

    fn insert(&mut self, index: State) {
        assert!(index < self.len);
        self.set.set_bit(index as u32);
    }

    fn contains(&self, index: State) -> bool {
        assert!(index < self.len);
        self.set.test_bit(index as u32)
    }

    fn cardinality(&self) -> State {
        self.set.count_ones() as State
    }

    fn pop(&mut self) -> Option<State> {
        let result = self.set.iter_ones().next()?;
        self.set.clear_bit(result);
        Some(result as State)
    }

    fn from_iter<T: IntoIterator<Item = State>>(states: State, iter: T) -> StateBitSet {
        let mut result = StateBitSet::new(states);
        for state in iter {
            result.insert(state);
        }
        result
    }

    fn normalize_vec(states: State, set: &mut [usize]) {
        // Ensure canoncity
        if states % (usize::BITS as State) != 0 {
            if let Some(last) = set.last_mut() {
                *last &= (1usize << (states % (usize::BITS as State))).wrapping_sub(1);
            }
        }
    }
}

impl BitOr for &StateBitSet {
    type Output = StateBitSet;

    fn bitor(self, rhs: Self) -> Self::Output {
        assert_eq!(self.len, rhs.len);
        let mut res = self.set.clone();
        res.union_assign(&rhs.set);
        StateBitSet {
            set: res,
            len: self.len,
        }
    }
}

impl std::fmt::Debug for StateBitSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.set.iter_ones()).finish()
    }
}

impl BitAnd for &StateBitSet {
    type Output = StateBitSet;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.len, rhs.len);
        let mut res = self.set.clone();
        res.conjunction_assign(&rhs.set);
        StateBitSet {
            set: res,
            len: self.len,
        }
    }
}

impl Sub for &StateBitSet {
    type Output = StateBitSet;

    fn sub(self, rhs: Self) -> Self::Output {
        assert_eq!(self.len, rhs.len);
        let mut res = self.set.clone();
        res.difference_assign(&rhs.set);
        StateBitSet::normalize_vec(self.len, &mut res);
        StateBitSet {
            set: res,
            len: self.len,
        }
    }
}

impl Not for StateBitSet {
    type Output = StateBitSet;

    fn not(self) -> StateBitSet {
        let mut res = self.set.clone();
        for val in res.iter_mut() {
            *val = !*val;
        }
        StateBitSet::normalize_vec(self.len, &mut res);
        StateBitSet {
            set: res,
            len: self.len,
        }
    }
}

/// Renaming of old states to new ones.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Renaming {
    new_count: State,
    old_to_new: HashMap<State, State>,
    new_to_old: Vec<State>,
}

impl Renaming {
    fn new(new_count: State) -> Renaming {
        Renaming {
            new_count,
            old_to_new: HashMap::new(),
            new_to_old: vec![0; new_count as usize],
        }
    }

    fn add(&mut self, old: State, new: State) {
        self.old_to_new.insert(old, new);
        self.new_to_old[new as usize] = old;
    }

    fn rename_slice(&self, vec: &mut [State]) {
        for elem in vec.iter_mut() {
            *elem = self.old_to_new[elem];
        }
    }

    fn rename_set(&self, set: &StateBitSet) -> StateBitSet {
        let mut res = StateBitSet::new(self.new_count);
        for i in 0..self.new_count {
            if set.contains(self.new_to_old[i as usize]) {
                res.insert(i);
            }
        }

        res
    }

    fn old_to_new(&self, old: State) -> State {
        self.old_to_new[&old]
    }

    fn new_to_old(&self, new: State) -> State {
        self.new_to_old[new as usize]
    }
}

/// DFA representing a bitvector-valued function of some bitvector inputs.
/// State 0 is considered the starting state and is never accepting (returning 1).
/// No state should link to state 0 - it is used as a unique starting point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Dfa {
    // Number of inputs. u8 is enough here, as having more inputs than that would
    // make Dfa not fit in RAM.
    inputs: u8,
    // Number of states
    states: State,
    // Set of accepting states
    accepting: StateBitSet,
    // Transition table. We have a state transition table for each state, and
    // each state transition table has an entry for all combination of inputs.
    transitions: Vec<State>,
    // Initial state table
    init_states: Vec<State>,
}

impl Dfa {
    #[inline]
    fn next_state(&self, state: State, edge: usize) -> State {
        self.transitions[(state as usize) * (1usize << self.inputs) + edge]
    }

    fn states(&self) -> impl Iterator<Item = State> {
        (0 as State)..self.states
    }

    fn alphabet_size(&self) -> usize {
        1usize << self.inputs
    }

    fn alphabet(&self) -> impl DoubleEndedIterator<Item = usize> {
        0..self.alphabet_size()
    }

    fn to_dot(&self) -> String {
        let mut result = String::new();

        let _ = writeln!(&mut result, "digraph G {{");
        let _ = writeln!(&mut result, "  start [shape=ellipse, label=start];");

        for state in self.states() {
            let shape = if self.accepting.contains(state) {
                "doublecircle"
            } else {
                "circle"
            };
            let _ = writeln!(&mut result, "  s{state} [shape={shape}, label={state}];");
        }

        let _ = writeln!(&mut result);

        let input_label =
            |input: usize| format!("{:0width$b}", input, width = self.inputs as usize);

        for (input, init_state) in self.init_states.iter().enumerate() {
            let _ = writeln!(
                &mut result,
                "  start -> s{init_state} [label={}];",
                input_label(input)
            );
        }

        let _ = writeln!(&mut result);

        for state in self.states() {
            for input in self.alphabet() {
                let label = input_label(input);
                let _ = writeln!(
                    &mut result,
                    "  s{state} -> s{} [label={label}];",
                    self.next_state(state, input)
                );
            }
        }

        let _ = write!(&mut result, "}}");

        result
    }

    #[cfg(debug_assertions)]
    fn validate(&self) {
        for transition in self.transitions.iter() {
            assert!(*transition < self.states);
        }
        for transition in self.init_states.iter() {
            assert!(*transition < self.states);
        }
    }

    #[cfg(not(debug_assertions))]
    fn validate(&self) {}

    fn dfs(&self, mut visit: impl FnMut(State)) -> StateBitSet {
        let mut reachable: StateBitSet = StateBitSet::new(self.states);
        let mut stack = vec![];

        for init_state in self.init_states.iter() {
            if reachable.contains(*init_state) {
                continue;
            }
            reachable.insert(*init_state);
            stack.push(*init_state);
        }
        // it's a bit easier to debug with this. For instance,
        // combinatorial functions transition tables are just
        // truth tables repeated twice
        stack.reverse();

        while let Some(state) = stack.pop() {
            visit(state);

            for label in self.alphabet().rev() {
                let next_state = self.next_state(state, label);
                if reachable.contains(next_state) {
                    continue;
                }
                reachable.insert(next_state);
                stack.push(next_state);
            }
        }

        reachable
    }

    fn dfs_renaming(&self) -> Renaming {
        let mut renaming: Renaming = Renaming {
            new_count: 0,
            old_to_new: HashMap::new(),
            new_to_old: vec![],
        };

        self.dfs(|state| {
            if renaming.old_to_new.contains_key(&state) {
                return;
            }
            renaming.old_to_new.insert(state, renaming.new_count);
            renaming.new_to_old.push(state);
            renaming.new_count += 1;
            assert_eq!(renaming.new_count as usize, renaming.new_to_old.len());
        });
        renaming
    }

    fn shrink_states(&self, renaming: &Renaming) -> Dfa {
        let mut new_transitions = vec![];
        new_transitions.reserve_exact(renaming.new_count as usize * self.alphabet_size());

        for new_state in 0..renaming.new_count {
            let old_state = renaming.new_to_old(new_state);
            for label in self.alphabet() {
                new_transitions.push(renaming.old_to_new(self.next_state(old_state, label)));
            }
        }

        let mut new_init_states = self.init_states.clone();
        renaming.rename_slice(&mut new_init_states);

        Dfa {
            inputs: self.inputs,
            states: renaming.new_count,
            accepting: renaming.rename_set(&self.accepting),
            transitions: new_transitions,
            init_states: new_init_states,
        }
    }

    // Canonical DFAs form of the DFA can be used to compare for equality.
    // This does not perform minimization, but it does prune unreachable states.
    fn canonical(&self) -> Dfa {
        let renaming = self.dfs_renaming();
        self.shrink_states(&renaming)
    }

    // Minimize the DFA using Hopcroft's algorithm. Does not return a canonical
    // form of the DFA. Does not prune unreachable states.
    fn hopcroft(&self) -> Dfa {
        if self.accepting.cardinality() == self.states {
            return Dfa::constant(true, self.inputs);
        } else if self.accepting.cardinality() == 0 {
            return Dfa::constant(false, self.inputs);
        }

        let mut worklist = BTreeSet::new();
        worklist.insert(self.accepting.clone());
        worklist.insert(!self.accepting.clone());
        let mut states_eq_classes = worklist.clone();
        // Iterate until fixpoint is reached and we computed all states in the minimal DFA.
        while let Some(set) = worklist.pop_first() {
            assert_ne!(set.cardinality(), 0);
            assert!(set.set.iter_ones().all(|x| (x as u16) < self.states));

            for label in self.alphabet() {
                let mut go_into_set = StateBitSet::new(self.states);
                for state in self.states() {
                    let next_state = self.next_state(state, label);
                    if set.contains(next_state) {
                        go_into_set.insert(state);
                    }
                }

                let mut new_states_eq_classes = BTreeSet::new();
                for class in states_eq_classes.into_iter() {
                    let class_goes_into_set = &class & &go_into_set;
                    let class_does_not_go_into_set = &class - &go_into_set;

                    if class_goes_into_set.cardinality() == 0
                        || class_does_not_go_into_set.cardinality() == 0
                    {
                        new_states_eq_classes.insert(class);
                        continue;
                    }
                    new_states_eq_classes.insert(class_goes_into_set.clone());
                    new_states_eq_classes.insert(class_does_not_go_into_set.clone());

                    // Not all members of the class behave in the same way now,
                    // introduce a split.
                    if worklist.remove(&class) {
                        worklist.insert(class_does_not_go_into_set);
                        worklist.insert(class_goes_into_set);
                    } else if class_goes_into_set.cardinality()
                        < class_does_not_go_into_set.cardinality()
                    {
                        worklist.insert(class_goes_into_set);
                    } else {
                        worklist.insert(class_does_not_go_into_set);
                    }
                }

                states_eq_classes = new_states_eq_classes;
            }
        }

        let mut class_elements = states_eq_classes.into_iter().collect::<Vec<_>>();
        let mut renaming = Renaming::new(class_elements.len() as State);

        for i in 0..(class_elements.len() as State) {
            let set = &mut class_elements[i as usize];
            while let Some(state) = set.pop() {
                renaming.add(state as State, i);
            }
        }

        self.shrink_states(&renaming)
    }

    fn minimize(&self) -> Dfa {
        self.canonical().hopcroft().canonical()
    }

    /// Apply unary function to the accepting states bitmask of the DFA
    fn unary(
        self,
        extra_memory_states: State,
        initial_state: State,
        f: impl Fn(bool, State) -> (bool, State),
    ) -> Dfa {
        self.binary(
            &Dfa::constant(false, self.inputs),
            extra_memory_states,
            initial_state,
            |a, _, state| f(a, state),
        )
    }

    /// Produce a new DFA that is the product of this DFA and another DFA.
    /// This assumes self.inputs == other.inputs.
    /// `transition_fn` combines two boolean values and previous remembered
    /// value and returns boolean output and a new remembered value.
    /// State usage is 1 + (N - 1) * (M - 1) * extra_memory_states.
    ///
    /// For combinatorial functions, `extra_memory_states` should be set to 1,
    /// in which case `transition_fn` would always get 0.
    fn binary(
        &self,
        other: &Dfa,
        extra_memory_states: State,
        initial_memory_state: State,
        transition_fn: impl Fn(bool, bool, State) -> (bool, State),
    ) -> Dfa {
        assert!(extra_memory_states > 0);
        assert_eq!(self.inputs, other.inputs);
        let new_states = 2 * self.states * other.states * extra_memory_states;

        let to_prod_state = |accepting, x, y, extra| {
            (((accepting as State) * self.states + x) * other.states + y) * extra_memory_states
                + extra
        };

        // Build initial transitions
        let mut new_init_states = vec![];
        new_init_states.reserve_exact(self.alphabet_size());
        for label in self.alphabet() {
            let self_init_state = self.init_states[label];
            let other_init_state = other.init_states[label];

            let (accepting, new_memory_state) = transition_fn(
                self.accepting.contains(self_init_state),
                other.accepting.contains(other_init_state),
                initial_memory_state,
            );
            let target_state = to_prod_state(
                accepting,
                self_init_state,
                other_init_state,
                new_memory_state,
            );

            new_init_states.push(target_state);
        }

        // Iterate over all states in the product DFA to build transition tables
        let mut new_transitions = vec![];
        new_transitions.reserve_exact(self.alphabet_size() * new_states as usize);
        for self_state in 0..self.states {
            for other_state in 0..other.states {
                for memory in 0..extra_memory_states {
                    for label in self.alphabet() {
                        let self_next_state = self.next_state(self_state, label);
                        let other_next_state = other.next_state(other_state, label);
                        let (accepting, new_memory_state) = transition_fn(
                            self.accepting.contains(self_next_state),
                            other.accepting.contains(other_next_state),
                            memory,
                        );
                        assert!(new_memory_state < extra_memory_states);
                        let next_prod_state = to_prod_state(
                            accepting,
                            self_next_state,
                            other_next_state,
                            new_memory_state,
                        );

                        assert!(next_prod_state < new_states);
                        new_transitions.push(next_prod_state);
                    }
                }
            }
        }
        // Repeat same transition table second time. We have to do this,
        // since otherwise accepting/non-accepting states may alias.
        new_transitions.extend_from_within(0..);

        let mut new_accepting = StateBitSet::new(new_states);
        for i in (new_states / 2)..new_states {
            new_accepting.insert(i);
        }

        assert_eq!(
            new_transitions.len(),
            new_states as usize * self.alphabet_size()
        );

        let res = Dfa {
            inputs: self.inputs,
            states: new_states,
            transitions: new_transitions,
            accepting: new_accepting,
            init_states: new_init_states,
        };
        res.validate();
        res
    }

    fn input(ith: u8, out_of: u8) -> Dfa {
        let mut init_states = vec![];
        for label in 0..(1 << out_of) {
            init_states.push(((label & (1 << ith)) != 0) as State)
        }

        let mut transitions = vec![];
        transitions.extend_from_slice(&init_states);
        transitions.extend_from_slice(&init_states);

        let mut accepting = StateBitSet::new(2);
        accepting.insert(1);

        let res = Dfa {
            inputs: out_of,
            states: 2,
            accepting,
            transitions,
            init_states,
        };
        res.validate();
        res
    }

    fn constant(value: bool, inputs: u8) -> Dfa {
        let mut accepting = StateBitSet::new(1);
        if value {
            accepting.insert(0);
        }

        Dfa {
            inputs,
            states: 1,
            accepting,
            transitions: vec![0; 1 << inputs],
            init_states: vec![0; 1 << inputs],
        }
    }

    /// DFA that accepts bitvector one constant and nothing else
    fn one(inputs: u8) -> Dfa {
        let mut accepting = StateBitSet::new(2);
        accepting.insert(0);

        Dfa {
            inputs,
            states: 2,
            accepting,
            transitions: vec![1; 2 << inputs],
            init_states: vec![0; 1 << inputs],
        }
    }
}

impl std::ops::BitAnd for &Dfa {
    type Output = Dfa;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.binary(rhs, 1, 0, |a, b, _| (a & b, 0)).minimize()
    }
}

impl std::ops::BitAnd for Dfa {
    type Output = Dfa;

    fn bitand(self, rhs: Self) -> Self::Output {
        &self & &rhs
    }
}

impl std::ops::BitOr for &Dfa {
    type Output = Dfa;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.binary(rhs, 1, 0, |a, b, _| (a | b, 0)).minimize()
    }
}

impl std::ops::BitOr for Dfa {
    type Output = Dfa;

    fn bitor(self, rhs: Self) -> Self::Output {
        &self | &rhs
    }
}

impl std::ops::BitXor for &Dfa {
    type Output = Dfa;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.binary(rhs, 1, 0, |a, b, _| (a ^ b, 0)).minimize()
    }
}

impl std::ops::BitXor for Dfa {
    type Output = Dfa;

    fn bitxor(self, rhs: Self) -> Self::Output {
        &self ^ &rhs
    }
}

impl std::ops::Not for Dfa {
    type Output = Dfa;

    fn not(self) -> Self::Output {
        self.unary(1, 0, |a, _| (!a, 0)).minimize()
    }
}

impl std::ops::Not for &Dfa {
    type Output = Dfa;

    fn not(self) -> Self::Output {
        !self.clone()
    }
}

impl std::ops::Add for &Dfa {
    type Output = Dfa;

    fn add(self, rhs: Self) -> Self::Output {
        self.binary(rhs, 2, 0, |a, b, carry| {
            let sum = a as State + b as State + carry;
            (sum & 1 != 0, sum >> 1)
        })
        .minimize()
    }
}

impl std::ops::Add for Dfa {
    type Output = Dfa;

    fn add(self, rhs: Self) -> Self::Output {
        &self + &rhs
    }
}

impl std::ops::Neg for Dfa {
    type Output = Dfa;

    fn neg(self) -> Self::Output {
        self.unary(2, 1, |a, carry| {
            let half_adder = (!a) as State + carry;
            (half_adder & 1 != 0, half_adder >> 1)
        })
        .minimize()
    }
}

impl std::ops::Neg for &Dfa {
    type Output = Dfa;

    fn neg(self) -> Self::Output {
        -self.clone()
    }
}

impl std::ops::Sub for &Dfa {
    type Output = Dfa;

    fn sub(self, rhs: Self) -> Self::Output {
        self.binary(rhs, 2, 1, |a, b, carry| {
            let sum = a as State + (!b) as State + carry;
            (sum & 1 != 0, sum >> 1)
        })
        .minimize()
    }
}

impl std::ops::Sub for Dfa {
    type Output = Dfa;

    fn sub(self, rhs: Self) -> Self::Output {
        &self - &rhs
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_fully_reachable() {
        let dfa = Dfa {
            inputs: 2,
            states: 3,
            accepting: StateBitSet::from_iter(3, [0, 2]),
            transitions: vec![2, 0, 1, 1, 1, 0, 2, 2, 2, 1, 2, 0],
            init_states: vec![0, 2, 2, 0],
        };

        let dfa_actual = dfa.canonical();
        assert_eq!(dfa, dfa_actual);
    }

    #[test]
    fn input_canonical() {
        let input = Dfa::input(0, 2);
        assert_eq!(input, input.minimize());
    }

    #[test]
    fn and_comm() {
        let left_dfa = Dfa::input(0, 2) & Dfa::input(1, 2);
        let right_dfa = Dfa::input(1, 2) & Dfa::input(0, 2);
        assert_eq!(left_dfa, right_dfa);
    }

    #[test]
    fn and_assoc() {
        let left_dfa = (Dfa::input(0, 3) & Dfa::input(1, 3)) & Dfa::input(2, 3);
        let right_dfa = Dfa::input(0, 3) & (Dfa::input(1, 3) & Dfa::input(2, 3));
        assert_eq!(left_dfa, right_dfa);
    }

    #[test]
    fn de_morgan() {
        let left_dfa = !(Dfa::input(0, 2) & Dfa::input(1, 2));
        let right_dfa = !Dfa::input(0, 2) | !Dfa::input(1, 2);
        assert_eq!(left_dfa, right_dfa);
    }

    #[test]
    fn and_of_x_and_not_x() {
        let dfa = Dfa::input(0, 1) & !Dfa::input(0, 1);
        assert_eq!(dfa, Dfa::constant(false, 1));
    }

    #[test]
    fn add_comm() {
        let left_dfa = Dfa::input(0, 2) + Dfa::input(1, 2);
        let right_dfa = Dfa::input(1, 2) + Dfa::input(0, 2);
        assert_eq!(left_dfa, right_dfa);
    }

    #[test]
    fn add_cancel() {
        let x = || Dfa::input(0, 2);
        let y = || Dfa::input(1, 2);

        assert_eq!(x() + y() + (-y()), x());
    }

    #[test]
    fn add_assoc() {
        let left_dfa = (Dfa::input(0, 3) + Dfa::input(1, 3)) + Dfa::input(2, 3);
        let right_dfa = Dfa::input(0, 3) + (Dfa::input(1, 3) + Dfa::input(2, 3));
        assert_eq!(left_dfa, right_dfa);
    }

    #[test]
    fn add_or_and() {
        let left_dfa = Dfa::input(0, 2) + Dfa::input(1, 2);
        let right_dfa =
            (Dfa::input(0, 2) & Dfa::input(1, 2)) + (Dfa::input(1, 2) | Dfa::input(0, 2));
        assert_eq!(left_dfa, right_dfa);
    }

    #[test]
    fn fast_absolute_value() {
        let x = || Dfa::input(0, 2);
        let y = || Dfa::input(1, 2);

        // x > y case
        let unoptimized_xy = x() - y();
        let optimized_xy = !(y() + !x());
        assert_eq!(unoptimized_xy, optimized_xy);

        // y > x case
        let unoptimized_yx = y() - x();
        let optimized_yz = y() + !x() + Dfa::one(2);

        assert_eq!(unoptimized_yx, optimized_yz);
    }

    #[test]
    fn z3_killer() {
        // (set-logic QF_BV)
        // (declare-fun y () (_ BitVec 64))
        // (declare-fun x () (_ BitVec 64))
        // (assert (let ((a!1 (bvsub (bvsub (bvsub x #x0000000000000002) y)
        //   (bvshl (bvor x (bvnot y)) #x0000000000000001))))
        // (let ((a!2 (bvmul (bvand (bvxor a!1 x) (bvnot y))
        //   (bvand y (bvnot (bvxor a!1 x))))))
        // (let ((a!3 (bvadd (bvmul (bvor (bvxor a!1 x) y) (bvand (bvxor a!1 x) y)) a!2)))
        //   (distinct a!3 (bvmul y y))))))
        // (check-sat)

        let x = Dfa::input(0, 2);
        let y = Dfa::input(1, 2);
        let two = Dfa::one(2) + Dfa::one(2);

        let x_or_not_y = &x | &!&y;

        let a1 = (&(&x - &two) - &y) - (&x_or_not_y + &x_or_not_y);

        let xor_a1_x = &a1 ^ &x;

        let a2_1 = &y & &!&xor_a1_x;
        assert_eq!(a2_1, Dfa::constant(false, 2));
        // a2 = a2_0 * a2_1 = a2_0 * 0 = 0

        let a3_0 = &xor_a1_x | &y;
        let a3_1 = &xor_a1_x & &y;
        assert_eq!(a3_1, y);
        assert_eq!(a3_0, y);
    }
}
