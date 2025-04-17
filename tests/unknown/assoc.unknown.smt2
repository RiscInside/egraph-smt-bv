(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert (distinct
    (bvadd a (bvadd a b))
    (bvadd (bvadd a a) a)
))

(check-sat)
