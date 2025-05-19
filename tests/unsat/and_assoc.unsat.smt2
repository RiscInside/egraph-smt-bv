; Associativity of and, solvable without any unsafe rules.
(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))
(declare-const c (_ BitVec 512))
(declare-const d (_ BitVec 512))

(assert (distinct (bvand a b c d) (bvand d c a b)))
(check-sat)
