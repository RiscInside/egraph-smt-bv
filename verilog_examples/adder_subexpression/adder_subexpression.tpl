(set-logic QF_UFBV)

%%

(declare-const state1 |miter1_s|)
(declare-const state2 |miter2_s|)
(declare-const state3 |miter3_s|)
(declare-const state4 |miter3_s|)

(assert (|miter1_h| state1))
(assert (|miter2_h| state2))
(assert (|miter3_h| state3))
(assert (|miter4_h| state4))

(assert (or
    (not (|miter1_a| state1))
    (not (|miter2_a| state2))
    (not (|miter3_a| state3))
    (not (|miter4_a| state4))))

(check-sat)
