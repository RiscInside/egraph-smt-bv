(set-logic QF_UFBV)

%%

(declare-const state1 |miter1_s|)
(declare-const state2 |miter2_s|)
(declare-const state3 |miter3_s|)
(declare-const state4 |miter4_s|)
(declare-const state5 |miter5_s|)
(declare-const state6 |miter6_s|)

(assert (|miter1_h| state1))
(assert (|miter2_h| state2))
(assert (|miter3_h| state3))
(assert (|miter4_h| state4))
(assert (|miter5_h| state5))
(assert (|miter6_h| state5))

(assert (or
    (not (|miter1_a| state1))
    (not (|miter2_a| state2))
    (not (|miter3_a| state3))
    (not (|miter4_a| state4))
    (not (|miter5_a| state5))
    (not (|miter6_a| state5))))

(check-sat)
