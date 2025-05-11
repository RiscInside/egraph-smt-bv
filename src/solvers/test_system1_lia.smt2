(set-logic QF_LIA)

;; modulus 2^64
(define-fun M () Int
  18446744073709551616)

;; declare Int variables
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)

;; bounds 0 ≤ vi < 2^64
(assert (and (<= 0 v1) (< v1 M)))
(assert (and (<= 0 v2) (< v2 M)))
(assert (and (<= 0 v3) (< v3 M)))
(assert (and (<= 0 v4) (< v4 M)))

;; Equation 1: 12345678901234*v1 + 98765432109876*v2 + 45678901234567*v3 + 78901234567890 ≡ 0 (mod M)
(assert
  (= (mod
       (+ (* 12345678901234 v1)
          (* 98765432109876 v2)
          (* 45678901234567 v3)
          78901234567890)
     M)
     0))

;; Equation 2: 55555555555555*v1 + 77777777777777*v2 + 33333333333333*v4 + 11111111111111 ≡ 0 (mod M)
(assert
  (= (mod
       (+ (* 55555555555555 v1)
          (* 77777777777777 v2)
          (* 33333333333333 v4)
          11111111111111)
     M)
     0))

;; Equation 3: 99999999999999*v1 + 88888888888888*v3 + 66666666666666*v4 + 44444444444444 ≡ 0 (mod M)
(assert
  (= (mod
       (+ (* 99999999999999 v1)
          (* 88888888888888 v3)
          (* 66666666666666 v4)
          44444444444444)
     M)
     0))

;; Distinct check: v4 ≠ (12597058849815457749*v2 + 11030395062240253015) mod M
(assert
  (distinct
    v4
    (mod
      (+ (* 12597058849815457749 v2)
         11030395062240253015)
      M)))

(check-sat)
(exit)
