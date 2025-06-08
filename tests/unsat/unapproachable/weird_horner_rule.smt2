(declare-const x (_ BitVec 256))
(declare-const a0 (_ BitVec 256))
(declare-const a1 (_ BitVec 256))
(declare-const a2 (_ BitVec 256))

(set-option :timeout 20000)

(assert
  (distinct
    (bvadd a0
      (bvand (bvmul a1 x) (bvmul a2 x x))
      (bvor (bvmul a1 x) (bvmul a2 x x)))
    (bvadd a0 (bvmul (bvadd a1 (bvmul a2 x)) x))))

(check-sat)
