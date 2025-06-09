(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const c (_ BitVec 3))

(assert
  (distinct
    (bvadd
      ((_ zero_extend 3) a)
      ((_ zero_extend 3) b)
      ((_ zero_extend 2) c))
    ((_ zero_extend 1)
      (bvadd
        ((_ zero_extend 2) a)
        ((_ zero_extend 2) b)
        ((_ zero_extend 1) c)))))

(check-sat)
