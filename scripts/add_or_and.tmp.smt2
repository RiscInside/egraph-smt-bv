(declare-const a (_ BitVec <WIDTH>))
(declare-const b (_ BitVec <WIDTH>))

(assert (distinct (bvadd (bvor a b) (bvand a b)) (bvadd a b)))
(check-sat)
