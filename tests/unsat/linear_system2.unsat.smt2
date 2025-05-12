(set-logic QF_BV)

;; Declare variables x1 through x6
(declare-const x1 (_ BitVec 4))
(declare-const x2 (_ BitVec 4))
(declare-const x3 (_ BitVec 4))
(declare-const x4 (_ BitVec 4))
(declare-const x5 (_ BitVec 4))
(declare-const x6 (_ BitVec 4))
(declare-const x7 (_ BitVec 4))
(declare-const x8 (_ BitVec 4))

;; (1) 5x1+11x2+7x3+2x5 ≡ 4
(assert (= (bvadd (bvadd (bvmul #b0101 x1) (bvmul #b1011 x2))
                  (bvadd (bvmul #b0111 x3) (bvmul #b0010 x5)))
           #b0100))

;; (2) 3x1+13x2+4x4+9x6 ≡ 10
(assert (= (bvadd (bvadd (bvmul #b0011 x1) (bvmul #b1101 x2))
                  (bvadd (bvmul #b0100 x4) (bvmul #b1001 x6)))
           #b1010))

;; (3) 7x1+9x2+5x3+12x7 ≡ 6
(assert (= (bvadd (bvadd (bvmul #b0111 x1) (bvmul #b1001 x2))
                  (bvadd (bvmul #b0101 x3) (bvmul #b1100 x7)))
           #b0110))

;; (4) 2x1+14x2+3x5+11x8 ≡ 8
(assert (= (bvadd (bvadd (bvmul #b0010 x1) (bvmul #b1110 x2))
                  (bvadd (bvmul #b0011 x5) (bvmul #b1011 x8)))
           #b1000))

;; (5) 6x1+10x2+1x4+13x6 ≡ 12
(assert (= (bvadd (bvadd (bvmul #b0110 x1) (bvmul #b1010 x2))
                  (bvadd (bvmul #b0001 x4) (bvmul #b1101 x6)))
           #b1100))

;; (6) 8x1+8x2+2x7+5x3 ≡ 14
(assert (= (bvadd (bvadd (bvmul #b1000 x1) (bvmul #b1000 x2))
                  (bvadd (bvmul #b0010 x7) (bvmul #b0101 x3)))
           #b1110))

;; (7) 4x1+12x2+6x5+3x8 ≡ 3
(assert (= (bvadd (bvadd (bvmul #b0100 x1) (bvmul #b1100 x2))
                  (bvadd (bvmul #b0110 x5) (bvmul #b0011 x8)))
           #b0011))

;; (8) 9x1+ 7x2 ≡ 0  <-- extra zero-sum equation
(assert (= (bvadd (bvmul #b1001 x1) (bvmul #b0111 x2))
           #b0000))

; x2 has to be equal to x1
(assert (distinct x2 x1))
(check-sat)
