(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert (distinct
    a
    (bvadd (bvadd a a) a)
))

(set-option :plan (seq (saturate fold width eq safe) once (repeat 2 (saturate fold width eq safe) unsafe)))

(check-sat)
