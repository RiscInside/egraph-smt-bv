(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))
(declare-const c (_ BitVec 512))
(declare-const d (_ BitVec 512))

(assert (distinct (concat (bvand a b) (bvand c d)) (bvand (concat a c) (concat b d))))
(check-sat)
