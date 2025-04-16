(set-logic QF_UFBV)

%%

(declare-const state1 |miter1_s|)
(assert (|miter1_h| state1))

(declare-const state2 |miter2_s|)
(assert (|miter2_h| state2))

(declare-const state3 |miter3_s|)
(assert (|miter3_h| state3))

(assert (or (not (|miter1_a| state1)) (not (|miter2_a| state2)) (not (|miter3_a| state3))))


(check-sat)
