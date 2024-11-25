(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))
(declare-const c (_ BitVec 512))
(declare-const d (_ BitVec 512))

(assert (distinct (bvadd a b c d) (bvadd d c a b)))
(check-sat)
