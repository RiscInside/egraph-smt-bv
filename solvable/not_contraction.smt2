(declare-const b Bool)

(assert (distinct b (not (not b))))

(check-sat)
