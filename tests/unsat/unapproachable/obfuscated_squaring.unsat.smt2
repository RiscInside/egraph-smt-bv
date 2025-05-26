; https://stackoverflow.com/questions/66001975/can-z3-apply-bit-width-reduction-techniques-to-solve-a-bit-vector-equivalence

(set-logic QF_BV)
(declare-fun y () (_ BitVec 64))
(declare-fun x () (_ BitVec 64))
(assert (let ((a!1 (bvsub (bvsub (bvsub x #x0000000000000002) y)
                  (bvshl (bvor x (bvnot y)) #x0000000000000001))))
(let ((a!2 (bvmul (bvand (bvxor a!1 x) (bvnot y))
                  (bvand y (bvnot (bvxor a!1 x))))))
(let ((a!3 (bvadd (bvmul (bvor (bvxor a!1 x) y) (bvand (bvxor a!1 x) y)) a!2)))
  (distinct a!3 (bvmul y y))))))
(check-sat)
