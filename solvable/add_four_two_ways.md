## Prelude definitions

<details>
<summary>prelude.egg - essential types/rulesets needed for the solver to function</summary>

### Values (`V`)
`V` defines all SMT2LIB values. We choose to make values untyped as that
reduces rule duplication across types.

```egg
(sort V)
```

We aren't using any "datatype" declaration, as there could be many ways in
which values in `V` are introduced, some of which we may not even know about.

### Value lists/variadics (`VS`)
`VS` are used for functions accepting variable number of parameters.

```egg
(datatype VS (VSCons V VS) (VSNil))
```

### Desugaring ruleset (`desugar`)

Desugaring ruleset consists of rules for converting one set of primitives
into another. Converted primitives should never be matched against in other
rules.

Currently, evaluation rules for user-defined functions are a part of this
pass, which means that no patterns should be written against user-defined
functions.
```egg
(ruleset desugar)
```

There is a helper ruleset `post-desugar` used to cleanup desugared constracts
and remove them from the e-graph.

```egg
(ruleset post-desugar)
```

Notably, lists of values are removed in the post-desugaring pass.

```egg
(rule ((= l (VSCons v vs))) ((delete (VSCons v vs))) :ruleset post-desugar)
(rule ((= l (VSNil))) ((delete (VSNil))) :ruleset post-desugar)
```

### Saturating ruleset (`safe`)

`safe` ruleset contains rules that are always eventually saturating.

```egg
(ruleset safe)
```

This ruleset includes:
* Merge-only rules of any kind (e.g. associativity/commutativity)
* Constant folding of any kind with subsumption of the original node
* Cancellation rules (e.g. in `a + b = a` we rewrite `b` to 0 and remove `+`)

### Exploratory ruleset (`unsafe`)

`unsafe` ruleset contrains all other rules that we deem potentially useful.
These never executed to saturation

```egg
(ruleset unsafe)
```

### `ProvenUnsat`

`ProvenUnsat` is used to query the system for whether UNSAT status has been shown. Rules can use `(set (ProvenUnsat) true)` to report discovered inconsistency.

```egg
(function ProvenUnsat () bool :merge new)
(set (ProvenUnsat) false)
```

</details>
<details>
<summary>core_theory.egg - definitions from the SMT2LIB core theory</summary>

### "Boolean" relation

`(Boolean v)` holds when `v` is a value of SMT2LIB sort `Bool`

```egg
(relation Boolean (V))
```

### Core theory operators

We represent boolean constants as `B true` and `B false` instead of `True` and `False` to simplify folding operations.

```egg
(constructor B (bool) V)
(let tt (B true))
(let ff (B false))
```

Main core theory operations of fixed arity. Unrolling variadic applications of
binary boolean operators is handled in Rust lowering code.

```egg
(constructor Not (V) V)
(constructor Implies (V V) V)
(constructor And (V V) V)
(constructor Or (V V) V)
(constructor Xor (V V) V)
(constructor ITE (V V V) V)
```

We can derive `Boolean` from them.

```egg
(rule ((= e (Not e1))) ((Boolean e)) :ruleset safe)
(rule ((= e (Implies e1 e2))) ((Boolean e)) :ruleset safe)
(rule ((= e (And e1 e2))) ((Boolean e)) :ruleset safe)
(rule ((= e (Or e1 e2))) ((Boolean e)) :ruleset safe)
(rule ((= e (Xor e1 e2))) ((Boolean e)) :ruleset safe)
(rule ((= e (ITE c e1 e2)) (Boolean e1)) ((Boolean e)) :ruleset safe)
```

Variadic equality/disequality operators

```egg
(constructor AllEqual (VS) V :unextractable)
(constructor AllDistinct (VS) V :unextractable)
(rule ((= e (AllEqual vs))) ((delete (AllEqual vs))) :ruleset post-desugar)
(rule ((= e (AllDistinct vs))) ((delete (AllDistinct vs))) :ruleset post-desugar)
```

Binary equality operator `Equal` (and `AllEqual`/`AllDistinct` desugaring)

```egg
(constructor Equal (V V) V)
(rewrite (AllEqual (VSCons v (VSNil))) tt :subsume :ruleset desugar)
(rewrite (AllEqual (VSCons v1 (VSCons v2 vs)))
         (And (Equal v1 v2) (AllEqual (VSCons v2 vs))) :subsume :ruleset desugar)

(constructor AllDistinctFrom (V VS) V :unextractable)

(rewrite (AllDistinct (VSNil)) tt :subsume :ruleset desugar)
(rewrite (AllDistinct (VSCons v vs))
         (And (AllDistinctFrom v vs) (AllDistinct vs)) :subsume :ruleset desugar)
(rewrite (AllDistinctFrom v (VSNil)) tt :subsume :ruleset desugar)
(rewrite (AllDistinctFrom v (VSCons v1 vs))
          (And (Not (Equal v v1)) (AllDistinctFrom v vs)) :subsume :ruleset desugar)
```

</details>
<details>
<summary>bv_theory.egg - definitions from the SMT2LIB FixedSizeBitVectors theory</summary>

### Moving bits around

```egg
(constructor Concat (V V) V)
(constructor Extract (i64 i64 V) V)
(constructor Repeat (i64 V) V)
(constructor RotateRight (i64 V) V)
(constructor RotateLeft (i64 V) V)
(constructor ZeroExtend (i64 V) V)
(constructor SignExtend (i64 V) V)
```

Rust code lowers variadic `concat` operations to binary `Concat` calls.

### Unary bitvector operators

```egg
(constructor BvNot (V) V)
(constructor BvNeg (V) V)
```

### Binary bitvector operators

Some of these support left-associative chaining, but this is handled fully
by Rust code

#### Bitwise logical operators

```egg
(constructor BvAnd (V V) V)
(constructor BvOr (V V) V)
(constructor BvXor (V V) V)
(constructor BvNand (V V) V)
(constructor BvNor (V V) V)
(constructor BvXNor (V V) V)
```

#### Arithmetic operators

```egg
(constructor BvAdd (V V) V)
(constructor BvSub (V V) V)
(constructor BvMul (V V) V)
(constructor BvUDiv (V V) V)
(constructor BvURem (V V) V)
(constructor BvSDiv (V V) V)
(constructor BvSRem (V V) V)
(constructor BvSMod (V V) V)

(constructor BvShl (V V) V)
(constructor BvLShr (V V) V)
(constructor BvAShr (V V) V)
```

### Bitvector constants

Bitvector constant are stored as egglog big integers. This allows us to
support bitvectors of any (reasonable) width. We store width together with
the bitvector value.

```egg
(constructor BvConst (i64 BigInt) V)
```

### `Width` of bit-vectors

This function returns width of the bit-vector. Currently it is computed
bottom-up and returns a single i64 value, but it may be converted to return
a symbolic value in the future

```egg
(function Width (V) i64)
```

#### Propogation rules

We define width propogation rules for basic primitives. This mostly resemble
ones implemented in the Rust sort checker.

```egg
(rule ((= e (ITE c e1 e2)) (= w1 (Width e1))) ((set (Width e) w1)) :ruleset safe)

(rule ((= e (Concat lhs rhs)) (= lw (Width lhs)) (= rw (Width rhs)))
      ((set (Width e) (+ lw rw))) :ruleset safe)
(rule ((= e (Extract i j exp))) ((set (Width e) (+ (- i j) 1))) :ruleset safe)
(rule ((= e (Repeat n exp)) (= w (Width exp))) ((set (Width e) (* w n))) :ruleset safe)
(rule ((= e (RotateLeft _ exp)) (= w (Width exp))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (ZeroExtend n exp)) (= w (Width exp))) ((set (Width e) (+ w n))) :ruleset safe)
(rule ((= e (SignExtend n exp)) (= w (Width exp))) ((set (Width e) (+ w n))) :ruleset safe)

(rule ((= e (BvNot e1)) (= w (Width e))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvNeg e1)) (= w (Width e))) ((set (Width e) w)) :ruleset safe)

(rule ((= e (BvAnd e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvOr e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvXor e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvNand e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvNor e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvXNor e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)

(rule ((= e (BvAdd e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvSub e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvMul e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvUDiv e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvURem e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvSDiv e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvSRem e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvSMod e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvShl e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvLShr e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvAShr e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
```

</details>
<details>
<summary>fold.egg - Simple folding rules</summary>

#### Deriving UNSAT from boolean constant propagation

```egg
(rule ((= (B true) (B false))) ((set (ProvenUnsat) true)) :ruleset safe)
```

### Converting all boolean operators to AND and NOT

```egg
(rule ((= e (Or e1 e2)))
      ((union e (Not (And (Not e1) (Not e2))))
       (delete (Or e1 e2))) :ruleset desugar)
(rule ((= e (Xor e1 e2)))
      ((union e (Not (And (Not (And e1 (Not e2))) (Not (And (Not e1) e2)))))
       (delete (Xor e1 e2))) :ruleset desugar)
(rule ((= e (Implies e1 e2)))
      ((union e (Not (And e1 (Not e2))))
       (delete (Or e1 e2))) :ruleset desugar)
```

### Boolean operator folding rules

```egg
(rewrite (Not (B b)) (B (not b)) :subsume :ruleset safe)
(rewrite (Not (Not e)) e :subsume :ruleset safe)
(rule ((= (Not e) (B b))) ((subsume (Not e)) (union e (B (not b)))) :ruleset safe)
```

Note that we have `(and a b)` to `(and b a)` as a `birewrite` in
`prelude/algebraic.egg`, so we don't need to worry about duplicating patterns
for `And`.

```egg
(rewrite (And e1 tt) e1 :subsume :ruleset safe)
(rewrite (And e1 ff) ff :subsume :ruleset safe)

(rule ((= (And e1 e2) tt))
      ((subsume (And e1 e2)) (union e1 tt) (union e2 tt)) :ruleset safe)

(rewrite (And e e) e :subsume :ruleset safe)
(rewrite (And e1 (Not e1)) ff :subsume :ruleset safe)
```

### Equality rules

```egg
(rule ((= tt (Equal e1 e2))) ((union e1 e2)) :ruleset safe)
(rewrite (Equal e e) tt :ruleset safe)
(rewrite (Equal tt ff) ff :ruleset safe)
```

### Bitvector logical operator rules

These rules mostly resemble boolean equivalents above

```egg
(rewrite (BvNot (BvNot e)) e :subsume :ruleset safe)

(rule ((= e (BvOr e1 e2)))
      ((union e (BvNot (BvAnd (BvNot e1) (BvNot e2))))
       (delete (BvOr e1 e2))) :ruleset desugar)
(rule ((= e (BvXor e1 e2)))
      ((union e (BvNot (BvAnd (BvNot (BvAnd e1 (BvNot e2))) (BvNot (BvAnd (BvNot e1) e2)))))
       (delete (BvXor e1 e2))) :ruleset desugar)
(rule ((= e (BvNand e1 e2)))
      ((union e (BvNot (BvAnd e1 e2)))
       (delete (BvOr e1 e2))) :ruleset desugar)
(rule ((= e (BvNor e1 e2)))
      ((union e (BvAnd (BvNot e1) (BvNot e2)))
       (delete (BvNor e1 e2))) :ruleset desugar)
(rule ((= e (BvXNor e1 e2)))
      ((union e (BvAnd (BvNot (BvAnd e1 (BvNot e2))) (BvNot (BvAnd (BvNot e1) e2))))
       (delete (BvXNor e1 e2))) :ruleset desugar)

(rewrite (BvAnd e e) e :subsume :ruleset safe)
```

### Arithmetic folds

```egg
(rewrite (BvNeg (BvNeg e)) e :subsume :ruleset safe)
```

</details>
<details>
<summary>algebraic.egg - Various algebraic-like rules</summary>

### Converting subtraction to negation

```egg
(rewrite (BvSub a b) (BvAdd a (BvNeg b)) :subsume :ruleset desugar)
```

### Commutativity rules

```egg
(birewrite (And a b) (And b a) :ruleset safe)
(birewrite (BvAnd a b) (BvAnd b a) :ruleset safe)
(birewrite (BvAdd a b) (BvAdd b a) :ruleset safe)
(birewrite (BvMul a b) (BvMul b a) :ruleset safe)
```

### Explosive associativity rules

```egg
(birewrite (And a (And b c)) (And (And a b) c) :ruleset unsafe)
(birewrite (BvAdd a (BvAdd b c)) (BvAdd (BvAdd a b) c) :ruleset unsafe)
(birewrite (BvAnd a (BvAnd b c)) (BvAnd (BvAnd a b) c) :ruleset unsafe)
(birewrite (BvMul a (BvMul b c)) (BvMul (BvMul a b) c) :ruleset unsafe)
```

</details>

## Solving log

### Declaration of `a`

```egg
(constructor a () V :unextractable)
(rule ((= |res| (a)))
      ((set (Width |res|) 512))
        :ruleset safe :name "a-width")
```

### Declaration of `b`

```egg
(constructor b () V :unextractable)
(rule ((= |res| (b)))
      ((set (Width |res|) 512))
        :ruleset safe :name "b-width")
```

### Declaration of `c`

```egg
(constructor c () V :unextractable)
(rule ((= |res| (c)))
      ((set (Width |res|) 512))
        :ruleset safe :name "c-width")
```

### Declaration of `d`

```egg
(constructor d () V :unextractable)
(rule ((= |res| (d)))
      ((set (Width |res|) 512))
        :ruleset safe :name "d-width")
```

### Assertion #1 (`(distinct (bvadd a b c d) (bvadd d c a b))`)

```egg
(union (AllDistinct (VSCons (BvAdd (BvAdd (BvAdd (a) (b)) (c)) (d)) (VSCons (BvAdd (BvAdd (BvAdd (d) (c)) (a)) (b)) (VSNil)))) tt)

(run-schedule (seq (saturate (run desugar)) (saturate (run post-desugar))))
```

### Running `check-sat`

```egg
(run-schedule
    (repeat 10
        (saturate (run safe :until (= true (ProvenUnsat))))
        (repeat 5 (run unsafe :until (= true (ProvenUnsat))))))
```
Result: **UNSAT**
