; Alive2 compiler optimization refinement query
; More info in "Alive2: Bounded Translation Validation for LLVM", PLDI'21.
(set-info :status unknown)
(declare-fun isundef_%x () (_ BitVec 1))
(declare-fun undef!1 () (_ BitVec 32))
(declare-fun np_%x () Bool)
(declare-fun %x () (_ BitVec 32))
(assert
 (let (($x57 (forall ((undef!0 (_ BitVec 32)) )(let (($x91 (= (bvnot (bvadd (_ bv63 6) ((_ extract 5 0) undef!0))) (bvmul (_ bv63 6) ((_ extract 5 0) undef!1)))))
(let (($x28 (not np_%x)))
(not (or $x28 $x91)))))
))
(let (($x13 (= (_ bv0 1) isundef_%x)))
(let (($x95 (forall ((undef!0 (_ BitVec 32)) )(let (($x28 (not np_%x)))
(let (($x51 (or $x28 (= (bvnot (bvadd (_ bv63 6) ((_ extract 5 0) %x))) (bvmul (_ bv63 6) ((_ extract 5 0) %x))))))
(not $x51))))
))
(or (and $x95 $x13) (and $x57 (= isundef_%x (_ bv1 1))))))))
(check-sat)
