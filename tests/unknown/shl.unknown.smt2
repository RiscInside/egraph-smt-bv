(declare-const a (_ BitVec 8))

(assert (distinct #x00 (bvadd a (concat ((_ extract 3 0) a) #b0000))))
(check-sat)
