; Alive2 compiler optimization refinement query
; More info in "Alive2: Bounded Translation Validation for LLVM", PLDI'21.
(set-info :status unknown)
(declare-fun %x () (_ BitVec 32))
(declare-fun np_%x () Bool)
(declare-fun isundef_%x () (_ BitVec 1))
(assert
 (let ((?x22 (concat (_ bv0 26) ((_ extract 5 0) (bvmul %x (_ bv4294967295 32))))))
(let ((?x17 (concat (_ bv0 26) ((_ extract 5 0) (bvadd (_ bv63 32) %x)))))
(let ((?x19 (bvxor (_ bv63 32) ?x17)))
(let (($x26 (or (not np_%x) (= ?x19 ?x22))))
(let (($x34 (not $x26)))
(let (($x12 (= (_ bv0 1) isundef_%x)))
(and $x12 $x34))))))))
(check-sat)
