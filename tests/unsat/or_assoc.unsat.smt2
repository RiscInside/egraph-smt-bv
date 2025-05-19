; Associativity of or, solvable without any unsafe rules.
(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))
(declare-const c (_ BitVec 512))
(declare-const d (_ BitVec 512))

(assert (distinct (bvor a b c d) (bvor d c a b)))
(check-sat)
