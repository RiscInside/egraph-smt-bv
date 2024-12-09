(declare-const a Bool)
(declare-const b Bool)

(assert (distinct (xor a b) (not (and (not (and a (not b))) (not (and (not a) b))))))
(check-sat)
