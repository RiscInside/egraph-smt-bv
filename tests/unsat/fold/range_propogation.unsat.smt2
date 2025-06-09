(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert (bvule a (_ bv5 64)))
(assert (bvule b (_ bv4 64)))
(assert (bvugt (bvadd a b (bvsub b b)) (_ bv9 64)))

(check-sat)
