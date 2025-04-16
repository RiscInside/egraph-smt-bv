(set-logic QF_UFBV)

%%

(declare-const state |miter_s|)
(assert (|miter_h| state)) ; Hierarchy assertion
(assert (not (|miter_a| state))) ; Miter assertion failure - output of miter is true
(check-sat)
