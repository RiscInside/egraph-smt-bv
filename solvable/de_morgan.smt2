(declare-const a Bool)
(declare-const b Bool)
(assert (distinct (not (and a b)) (or (not a) (not b))))
(check-sat)
