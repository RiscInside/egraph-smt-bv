(declare-const a (_ BitVec 16))
(declare-const b (_ BitVec 16))
(declare-fun f ((_ BitVec 16)) Bool)

(assert (f (bvadd b a (_ bv1 16))))
(check-sat)
