; Example given in Application-Specific Arithmetic, Chapter 5.3.8 "Fast Absolute Difference Operator".
; To show: a > b ? a - b : b - a = a > b ? ~(a + ~b) : (a + ~b + 1)

(declare-const a (_ BitVec 512))
(declare-const b (_ BitVec 512))

(declare-const abs_diff_raw (_ BitVec 512))
(declare-const abs_diff_opt (_ BitVec 512))

(assert (= abs_diff_raw (ite (bvsge a b) (bvsub a b) (bvsub b a))))
(assert (= abs_diff_opt (ite (bvsge a b) (bvnot (bvadd b (bvnot a))) (bvadd b (bvnot a) (_ bv1 512)))))

(assert (distinct abs_diff_raw abs_diff_opt))

(check-sat)
