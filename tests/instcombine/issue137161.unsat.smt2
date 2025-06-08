(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))


(assert (distinct (bvor (ite (= x (_ bv0 64)) y (_ bv0 64)) x) (ite (= x (_ bv0 64)) y x)))
(check-sat)
