(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert (distinct (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a (bvadd a b))))))))
(bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd a a) a) a) a) a) a) a) b)))

; This example won't work with a standard schedule, but we can make it work with a custom one
(set-option :plan (seq (repeat 3 "unsafe" "safe") (repeat 3 "fold" "fold" "fold")))

(check-sat)
