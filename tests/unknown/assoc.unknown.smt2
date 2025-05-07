(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert (distinct
    a
    (bvadd (bvadd a a) a)
))

(check-sat)
