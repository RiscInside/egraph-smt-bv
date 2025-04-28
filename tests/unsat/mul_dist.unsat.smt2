(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(set-option :plan (seq (saturate eq width fold) unsafe (saturate eq width fold)))
(assert (distinct (bvmul a (bvadd b #x00000001)) (bvadd (bvmul a b) (bvmul a #x00000001))))
(check-sat)
