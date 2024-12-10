(declare-const a Bool)
(declare-const b Bool)

; Part of the (a & b) + (a | b) proof
(assert (distinct (xor (and a b) (or a b)) (xor a b)))
(check-sat)
