(declare-const a Bool)
(declare-const b Bool)

; Part of the (a & b) + (a | b) proof, we need to show that carry bits
; are preserved.
(assert (distinct (xor a b) (xor (and a b) (or a b))))
(check-sat)
