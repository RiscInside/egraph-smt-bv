(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (distinct (bvmul a (bvadd b #x00000001)) (bvadd (bvmul a b) (bvmul a #x00000001))))
(check-sat)
