(declare-fun f ((_ BitVec 512)) Bool)
(declare-const b (_ BitVec 512))

(assert (f (bvneg b)))
(check-sat)
