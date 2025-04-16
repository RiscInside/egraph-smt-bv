(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))

(assert (distinct (bvadd (bvor a b) (bvand a b)) (bvadd a b)))
(check-sat)
