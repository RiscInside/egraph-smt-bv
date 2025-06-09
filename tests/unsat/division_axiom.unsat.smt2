(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))

(assert (distinct (bvadd (bvmul (bvudiv a b) b) (bvurem a b)) a))
(check-sat)
