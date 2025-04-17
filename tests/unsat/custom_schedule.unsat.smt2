(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert (distinct (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a b))))))))
(bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd a a) a) a) a) a) a) a) b)))

; This example currently won't terminate in a reasonable time with the default schedule.
; We can use a custom schedule to solve it in hundreds of milliseconds.
(set-option :plan (seq (repeat 3 "unsafe" "safe") (repeat 3 "fold")))

(check-sat)
