(declare-const a Bool)
(declare-const b Bool)

(assert (=> a b))
(assert (=> b a))
(assert (distinct a b))

(check-sat)
