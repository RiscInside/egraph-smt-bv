(declare-const a Bool)
(declare-const b Bool)

(assert (xor a b))
(assert a)
(assert b)

(check-sat)
