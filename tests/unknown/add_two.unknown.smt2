(declare-const a (_ BitVec 256))
(declare-const b (_ BitVec 256))

(assert (= (bvmul (_ bv2 256) a) (bvmul (_ bv2 256) b)))
(check-sat)
