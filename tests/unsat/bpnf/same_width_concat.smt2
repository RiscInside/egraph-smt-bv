(declare-const a (_ BitVec 1024))
(declare-const b (_ BitVec 1024))
(declare-const c (_ BitVec 1024))
(declare-const d (_ BitVec 1024))

(assert (= (concat a b) (concat c d)))
(assert (distinct a c))
(check-sat)
