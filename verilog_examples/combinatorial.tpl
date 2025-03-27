(set-logic QF_UFBV)

%%

(declare-const state |miter_s|) ; Assert random input state
(assert (|miter_h| state)) ; Inputs match
(assert (not (|miter#2| state))) ; Outputs don't match
(check-sat)
