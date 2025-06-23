(declare-const a (_ BitVec <WIDTH>))
(declare-const b (_ BitVec <WIDTH>))

(declare-const abs_diff_opt (_ BitVec <WIDTH>))

(assert (= abs_diff_opt (ite (bvsge a b) (bvnot (bvadd b (bvnot a))) (bvadd b (bvnot a) (_ bv1 <WIDTH>)))))

(assert (distinct (bvmul (bvsub a b) (bvsub a b)) (bvmul abs_diff_opt abs_diff_opt)))

(check-sat)
