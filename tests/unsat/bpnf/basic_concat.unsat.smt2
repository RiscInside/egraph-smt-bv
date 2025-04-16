(assert (= ((_ extract 3 0) (concat #b1111 #b0000)) #b1111))
(check-sat)
