(declare-fun test ((_ BitVec 4)) Bool)

(assert (= (test #x0) (= (bvadd #b1111 #b0010) #b0001)))
(assert (= (test #x1) (= (bvneg #b01) #b11)))
(assert (= (test #x2) (= (concat #b01 #b10 #b11) #b011011)))
(assert (= (test #x3) (= ((_ extract 3 1) #b011011) #b101)))
(assert (= (test #x4) (= (bvmul #b1110 #b0010) #b1100)))
(assert (= (test #x5) (= (bvshl #b1100 #b0010) #b0000)))
(assert (= (test #x6) (= (bvlshr #b1100 #b0001) #b0110)))

(assert (not (and (test #x0) (test #x1) (test #x2) (test #x3) (test #x4) (test #x5) (test #x6))))
(check-sat)
