(declare-const a (_ BitVec 1024))
(declare-const b (_ BitVec 1024))

; concat supports multiple arguments and is left-associative
(assert (= (concat a #x1111 b) (concat a (concat #x0111 b))))
(check-sat)
