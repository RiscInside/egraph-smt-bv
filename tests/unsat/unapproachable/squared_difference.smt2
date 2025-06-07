; Based on fast_absolute_value.unsat.smt2 example.

(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))

(declare-const abs_diff_opt (_ BitVec 512))

(assert (= abs_diff_opt (ite (bvsge a b) (bvnot (bvadd b (bvnot a))) (bvadd b (bvnot a) (_ bv1 512)))))

(assert (distinct (bvmul (bvsub a b) (bvsub a b)) (bvmul abs_diff_opt abs_diff_opt)))

(check-sat)
