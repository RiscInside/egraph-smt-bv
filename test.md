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

We also define custom constant shifts to simplify some rewrite rules.

```egg
(constructor BvShlC (V i64) V)
(constructor BvLShrC (V i64) V)
(constructor BvAShrC (V i64) V)
```

### Bitvector constants

We use two different types for small and large bitvectors

```egg
(constructor BvSmall (i64 SmallBitVec) V)
(constructor BvLarge (i64 BigInt) V)
```

We also define `(BvAll b w)` to represent all-zero/all-one bitvectors
of width `w` (`b = false` for all-zeros and `b = true` for all-ones).

```egg
(constructor BvAll (bool i64) V)
```

### `Width` of bit-vectors

This function returns width of the bit-vector. Currently it is computed
bottom-up and returns a single i64 value, but it may be converted to return
a symbolic value in the future

```egg
(function Width (V) i64 :no-merge)
```

#### Propagation rules

We define width propagation rules for basic primitives. This mostly resemble
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

(rule ((= e (BvSmall w v))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvLarge w v))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvAll b w))) ((set (Width e) w)) :ruleset safe)

(rule ((= e (BvShlC e1 c)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvLShrC e1 c)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
(rule ((= e (BvAShrC e1 c)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe)
```

#### Constant folding rules for bitvectors

```egg
(rewrite (BvNot (BvSmall w a)) (BvSmall w (not-sbv a w)) :subsume :ruleset safe)
(rewrite (BvNeg (BvSmall w a)) (BvSmall w (neg a w)) :subsume :ruleset safe)

(rewrite (BvAnd (BvSmall w a) (BvSmall _w b)) (BvSmall w (& a b w)) :subsume :ruleset safe)
(rewrite (BvOr (BvSmall w a) (BvSmall _w b)) (BvSmall w (| a b w)) :subsume :ruleset safe)
(rewrite (BvXor (BvSmall w a) (BvSmall _w b)) (BvSmall w (^ a b w)) :subsume :ruleset safe)

(rewrite (BvAdd (BvSmall w a) (BvSmall _w b)) (BvSmall w (+ a b w)) :subsume :ruleset safe)
(rewrite (BvSub (BvSmall w a) (BvSmall _w b)) (BvSmall w (- a b w)) :subsume :ruleset safe)
(rewrite (BvMul (BvSmall w a) (BvSmall _w b)) (BvSmall w (* a b w)) :subsume :ruleset safe)
(rewrite (BvUDiv (BvSmall w a) (BvSmall _w b)) (BvSmall w (/u a b w)) :subsume :ruleset safe)

(rewrite (BvShl (BvSmall w a) (BvSmall _w b)) (BvSmall w (<< a b w)) :subsume :ruleset safe)
(rewrite (BvLShr (BvSmall w a) (BvSmall _w b)) (BvSmall w (>> a b w)) :subsume :ruleset safe)

(rewrite (Concat (BvSmall w1 a) (BvSmall w2 b)) (BvSmall (+ w1 w2) (concat a b w2)) :subsume :ruleset safe)
(rewrite (Extract i j (BvSmall w a)) (BvSmall (- (+ i 1) j) (extract a i j)) :subsume :ruleset safe)
```
</details>
<details>
<summary>propositional.egg - Lifting booleans to propositions</summary>

### Deriving UNSAT from boolean constant propagation

```egg
(rule ((= (B true) (B false))) ((set (ProvenUnsat) true)) :ruleset safe)
```

Similar rule exists for bitvector constants.

```egg
(rule ((= (BvSmall w1 v1) (BvSmall w2 v2)) (!= v1 v2)) ((set (ProvenUnsat) true)) :ruleset safe)
(rule ((= (BvLarge w1 v1) (BvLarge w2 v2)) (!= v1 v2)) ((set (ProvenUnsat) true)) :ruleset safe)
```

### If-then-else constant folding

```egg
(rewrite (ITE tt a b) a :subsume :ruleset safe)
(rewrite (ITE ff a b) b :subsume :ruleset safe)
```

### Equality rules

```egg
(rule ((= tt (Equal e1 e2))) ((union e1 e2)) :ruleset safe)
(rewrite (Equal e e) tt :ruleset safe)
(rewrite (Equal tt ff) ff :ruleset safe)
```
</details>
<details>
<summary>bitwise.egg - simplifications of boolean/bitwise functions based on AND/NOT lowering (AIGs)</summary>

We define a set of rules inspired by AIGs simplifications as seen in
literature. We are not directly using And/Not constructors directly here
instead of defining separate AIG ones.

### Converting other boolean operators to and/not combinations and back

We have rules for lowering `Or`, `Xor`, and `Implies` to `Not` and `And`.
We choose to keep original e-nodes in the e-graph so that rewrite rules can
still produce those e-nodes when convinient. There is no subsumption either,
as aig simplification rules won't get any performance boost from subsuming
e-nodes from other tables.

```egg
(birewrite (Or e1 e2) (Not (And (Not e1) (Not e2))) :ruleset safe)
(rewrite (Xor e1 e2)
         (Not (And (Not (And e1 (Not e2))) (Not (And (Not e1) e2))))
         :ruleset safe)
(rewrite (Implies e1 e2) (Not (And e1 (Not e2))) :ruleset safe)
```

### Converting bitwise operators on bitvectors.

We can have similar rule on bitvectors (which are auto-derived). There are
a few other operators for bitvectors however for which there are no boolean
equivalents.

```egg
(rewrite (BvNand e1 e2) (Not (And e1 e2)) :ruleset safe)
(rewrite (BvNor e1 e2) (BvAnd (BvNot e1) (BvNot e2)) :ruleset safe)
(rewrite (BvXNor e1 e2) (BvAnd (BvNot (BvAnd e1 (BvNot e2)))
                        (BvNot (BvAnd (BvNot e1) e2))) :ruleset safe)
```

### `Not` folding

One rule implicit in AIGs is `Not` folding. These rules can safely be
subsuming.

```egg
(rewrite (Not (Not a)) a :subsume :ruleset safe)
```

We can propogate constants upwards through `Not`.

```egg
(rewrite (Not (B b)) (B (not b)) :subsume :ruleset safe)
(rule ((= (Not e) (B b))) ((subsume (Not e)) (union e (B (not b)))) :ruleset safe)
(rule ((= (BvNot e) (BvAll b w)) (= w (Width e))) ((subsume (BvNot e)) (union e (BvAll (not b) w))) :ruleset safe)
```

### Pushing constant booleans through And

```egg
(rule ((= tt (And a b))) ((union tt a) (union tt b)
      (subsume (And a b))) :ruleset safe)
(rule ((= (BvAll true w) (BvAnd a b)) (= w (Width a)))
      ((union (BvAnd a b) a) (union (BvAnd a b) b) (subsume (BvAnd a b)))
      :ruleset safe)
```

### `AIG` simplifications

These rewrite rules are taken from
[here](https://cca.informatik.uni-freiburg.de/biere/talks/Biere-GSSLBM06-talk.pdf).

#### O1 rules

Note that we already have commutativity, so we don't have to invert those
patterns.

```egg
(rewrite (And a tt) a :subsume :ruleset safe)
(rewrite (And a ff) ff :subsume :ruleset safe)
(rewrite (And a a) a :subsume :ruleset safe)
(rewrite (And a (Not a)) ff :subsume :ruleset safe)
```

#### O2 rules

Contradiction
```egg
(rewrite (And (And (Not a) b) a) ff :subsume :ruleset safe)
(rewrite (And (And a b) (Not a)) ff :subsume :ruleset safe)
(rewrite (And (And a b) (And (Not a) c)) ff :subsume :ruleset safe)
```
Subsumption
```egg
(rewrite (And (Not (And (Not a) b)) a) a :subsume :ruleset safe)
(rewrite (And (Not (And a b)) (Not a)) (Not a) :subsume :ruleset safe)
(rewrite (And (Not (And (Not a) b)) (And a c)) (And a c) :subsume :ruleset safe)
(rewrite (And (Not (And a b)) (And (Not a) c)) (And (Not a) c) :subsume :ruleset safe)
```
Idempotentence
```egg
(rewrite (And (And a b) a) (And a b) :subsume :ruleset safe)
(rewrite (And (Not (And a b)) (Not (And a (Not b)))) (Not a) :subsume :ruleset safe)
```

#### O3 rules

```egg
(rewrite (And (Not (And a b)) b) (And (Not a) b) :subsume :ruleset safe)
(rewrite (And (Not (And a b)) (And b c)) (And (Not a) (And b c)) :subsume :ruleset safe)
```

#### O4 rules

```egg
(rewrite (And (And a b) (And a d)) (And (And a b) d) :subsume :ruleset safe)
```

### Commutativity of `And`

```egg
(rewrite (And a b) (And b a) :ruleset safe)
```

Commutativity of `Or` is derivable.

### Associativity of `And` and `Or`

```egg
(birewrite (And (And a b) c) (And a (And b c)) :ruleset unsafe)
(birewrite (Or (Or a b) c) (Or a (Or b c)) :ruleset unsafe)
```

### Distributivity of `And` and `Or`

```egg
(rewrite (And a (Or b c)) (Or (And a b) (And a c)) :ruleset unsafe)
(rewrite (Or a (And b c)) (And (Or a b) (Or a c)) :ruleset unsafe)
```

### Lifting boolean AIG rules to bitwise bitvector operations
The rules after this point are generated automatically from boolean rules. See code for the generator in `src/log/preprocess/bv_from_bool_rules.rs`.

```egg
(rewrite (BvOr e1 e2) (BvNot (BvAnd (BvNot e1) (BvNot e2))) :ruleset safe)
(rewrite (BvNot (BvAnd (BvNot e1) (BvNot e2))) (BvOr e1 e2) :ruleset safe)
(rewrite (BvXor e1 e2) (BvNot (BvAnd (BvNot (BvAnd e1 (BvNot e2))) (BvNot (BvAnd (BvNot e1) e2)))) :ruleset safe)
(rewrite (BvNot (BvNot a)) a :subsume :ruleset safe)
(rule ((= |self| (BvNot (BvAll b |w|)))
       (= |w| (Width |self|)))
      ((union |self| (BvAll (not b) |w|))
       (subsume (BvNot (BvAll b |w|))))
        :ruleset safe )
(rule ((= |self| (BvAnd a (BvAll true |w|)))
       (= |w| (Width |self|)))
      ((union |self| a)
       (subsume (BvAnd a (BvAll true |w|))))
        :ruleset safe )
(rule ((= |self| (BvAnd a (BvAll false |w|)))
       (= |w| (Width |self|)))
      ((union |self| (BvAll false |w|))
       (subsume (BvAnd a (BvAll false |w|))))
        :ruleset safe )
(rewrite (BvAnd a a) a :subsume :ruleset safe)
(rule ((= |self| (BvAnd a (BvNot a)))
       (= |w| (Width |self|)))
      ((union |self| (BvAll false |w|))
       (subsume (BvAnd a (BvNot a))))
        :ruleset safe )
(rule ((= |self| (BvAnd (BvAnd (BvNot a) b) a))
       (= |w| (Width |self|)))
      ((union |self| (BvAll false |w|))
       (subsume (BvAnd (BvAnd (BvNot a) b) a)))
        :ruleset safe )
(rule ((= |self| (BvAnd (BvAnd a b) (BvNot a)))
       (= |w| (Width |self|)))
      ((union |self| (BvAll false |w|))
       (subsume (BvAnd (BvAnd a b) (BvNot a))))
        :ruleset safe )
(rule ((= |self| (BvAnd (BvAnd a b) (BvAnd (BvNot a) c)))
       (= |w| (Width |self|)))
      ((union |self| (BvAll false |w|))
       (subsume (BvAnd (BvAnd a b) (BvAnd (BvNot a) c))))
        :ruleset safe )
(rewrite (BvAnd (BvNot (BvAnd (BvNot a) b)) a) a :subsume :ruleset safe)
(rewrite (BvAnd (BvNot (BvAnd a b)) (BvNot a)) (BvNot a) :subsume :ruleset safe)
(rewrite (BvAnd (BvNot (BvAnd (BvNot a) b)) (BvAnd a c)) (BvAnd a c) :subsume :ruleset safe)
(rewrite (BvAnd (BvNot (BvAnd a b)) (BvAnd (BvNot a) c)) (BvAnd (BvNot a) c) :subsume :ruleset safe)
(rewrite (BvAnd (BvAnd a b) a) (BvAnd a b) :subsume :ruleset safe)
(rewrite (BvAnd (BvNot (BvAnd a b)) (BvNot (BvAnd a (BvNot b)))) (BvNot a) :subsume :ruleset safe)
(rewrite (BvAnd (BvNot (BvAnd a b)) b) (BvAnd (BvNot a) b) :subsume :ruleset safe)
(rewrite (BvAnd (BvNot (BvAnd a b)) (BvAnd b c)) (BvAnd (BvNot a) (BvAnd b c)) :subsume :ruleset safe)
(rewrite (BvAnd (BvAnd a b) (BvAnd a d)) (BvAnd (BvAnd a b) d) :subsume :ruleset safe)
(rewrite (BvAnd a b) (BvAnd b a) :ruleset safe)
(rewrite (BvAnd (BvAnd a b) c) (BvAnd a (BvAnd b c)) :ruleset unsafe)
(rewrite (BvAnd a (BvAnd b c)) (BvAnd (BvAnd a b) c) :ruleset unsafe)
(rewrite (BvOr (BvOr a b) c) (BvOr a (BvOr b c)) :ruleset unsafe)
(rewrite (BvOr a (BvOr b c)) (BvOr (BvOr a b) c) :ruleset unsafe)
(rewrite (BvAnd a (BvOr b c)) (BvOr (BvAnd a b) (BvAnd a c)) :ruleset unsafe)
(rewrite (BvOr a (BvAnd b c)) (BvAnd (BvOr a b) (BvOr a c)) :ruleset unsafe)
```

</details>
<details>
<summary>bpnf.egg - bit propogation normal form rules</summary>

These rules are based on Concat Normal Form and Bit Propogation Normal Form
papers. We try to identify things that are roughly similar.

### Reassociating concats

```egg
(rewrite (Concat a (Concat b c)) (Concat (Concat a b) c) :subsume :ruleset safe)
```

### Pushing extractions through concatenations

```egg
(rule ((= e (Extract i j (Concat a b))) (= bw (Width b)) (< i bw))
      ((subsume (Extract i j (Concat a b))) (union e (Extract i j b)))
      :ruleset safe)
(rule ((= e (Extract i j (Concat a b))) (= bw (Width b)) (>= j bw))
      ((subsume (Extract i j (Concat a b))) (union e (Extract (- i bw) (- j bw) a)))
      :ruleset safe)
(rule ((= e (Extract i j (Concat a b))) (= bw (Width b)) (>= i bw) (< j bw))
      ((subsume (Extract i j (Concat a b))) (union e (Concat (Extract (- i bw) 0 a) (Extract (- bw 1) j b))))
      :ruleset safe)
```

### Full width extractions

```egg
(rule ((= e (Extract w 0 i)) (= (+ w 1) (Width i))) ((delete (Extract w 0 i)) (union e i)) :ruleset safe)
```

### Concat of two adjacent extractions

```egg
(rule ((= e (Concat (Extract i j a) (Extract j k a))))
      ((union e (Extract i k a))
       (subsume (Concat (Extract i j a) (Extract j k a)))) :ruleset safe)
```

### Equality of two concats

Concat is injective if operands have the same biwidth.

```egg
(rule ((= (Concat a b) (Concat c d)) (= (Width a) (Width c))) ((union a c) (union b d)) :ruleset safe)
```

This is a more complicated version when a and b have different bitwidths.

```egg
(rule ((= (Concat a b) (Concat c d))
       (= aw (Width a)) (= bw (Width b))
       (= cw (Width c)) (= dw (Width d))
       (< bw dw)
      ) (
       (union b (Extract (- bw 1) 0 d))
       (union (Extract (- (- dw bw) 1) 0 a) (Extract (- dw 1) bw d))
       (union c (Extract (- aw 1) (- dw bw) a))
      ) :ruleset safe)
```
</details>
<details>
<summary>add.egg - addition, subtraction, and negation rules</summary>

### Commutativity

```egg
(rewrite (BvAdd a b) (BvAdd b a) :ruleset safe)
```

### Explosive associativity

```egg
(rewrite (BvAdd (BvAdd a b) c) (BvAdd a (BvAdd b c)) :ruleset unsafe)
```

### Converting subtraction to negation

```egg
(rewrite (BvSub a b) (BvAdd a (BvNeg b)) :subsume :ruleset safe)
```

### Double negation elimination

```egg
(rewrite (BvNeg (BvNeg a)) a :subsume :ruleset safe)
```

### Unfolding one step of `Add`

Pathological case when bitvector has width 1.

```egg
(rewrite (BvAdd a b) (BvXor a b) :subsume :when ((= (Width a) 1)) :ruleset safe)
```

The rule below does one half-adder step. It is highly explosive.

```egg
(rewrite (BvAdd a b) (BvAdd (BvXor a b) (BvShlC (BvAnd a b) 1)) :when ((> (Width a) 1)) :ruleset unsafe)
```
</details>
<details>
<summary>mul.egg - multiplication rules</summary>

### Commutativity

```egg
(rewrite (BvMul a b) (BvMul b a) :ruleset safe)
```

### Associativity

```egg
(birewrite (BvMul a (BvMul b c)) (BvMul (BvMul a b) c) :ruleset unsafe)
```
</details>

## Solving log

### Declaration of `a`

```egg
(constructor a () V :unextractable)
(rule ((= |res| (a )))
      ((set (Width |res|) 512))
        :ruleset safe :name "a-width")
```

### Declaration of `b`

```egg
(constructor b () V :unextractable)
(rule ((= |res| (b )))
      ((set (Width |res|) 512))
        :ruleset safe :name "b-width")
```

### Assertion #1 (`(distinct (bvadd (bvor a b) (bvand a b)) (bvadd a b))`)

```egg
(union (AllDistinct (VSCons (BvAdd (BvOr (a ) (b )) (BvAnd (a ) (b ))) (VSCons (BvAdd (a ) (b )) (VSNil )))) tt)

(run-schedule (seq (saturate (run desugar)) (saturate (run post-desugar))))
```

### Running `check-sat`

```egg
(run-schedule
    (repeat 30
        (saturate (run safe :until (= true (ProvenUnsat))))
        (run unsafe :until (= true (ProvenUnsat)))))
```
Result: **UNSAT**

<details>
<summary>Rewrite rule application statistics</summary>

#### Overall ruleset statistics

| Ruleset | Search time | Apply time | Rebuild time |
|---------|-------------|------------|--------------|
| `safe` | 188.403949ms | 8.458912ms | 10.484172ms
| `unsafe` | 3.282307ms | 375.747µs | 1.047149ms

#### Rewrite rules by number of applications
1) Rule `(rewrite (BvAnd a b) (BvAnd b a) :ruleset safe)` (220 applications)
2) Rule `(rule ((= e (BvAnd e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe )` (136 applications)
3) Rule `(rewrite (BvOr e1 e2) (BvNot (BvAnd (BvNot e1) (BvNot e2))) :ruleset safe)` (94 applications)
4) Rule `(rule ((= e (BvOr e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe )` (75 applications)
5) Rule `(rewrite (BvNot (BvAnd (BvNot e1) (BvNot e2))) (BvOr e1 e2) :ruleset safe)` (62 applications)

#### Top {} rules by search time
1) Rule `(rewrite (BvAnd (BvNot (BvAnd a b)) (BvNot (BvAnd a (BvNot b)))) (BvNot a) :subsume :ruleset safe)` (12.7536ms)
2) Rule `(rewrite (BvAnd (BvNot (BvAnd a b)) (BvAnd (BvNot a) c)) (BvAnd (BvNot a) c) :subsume :ruleset safe)` (10.537958ms)
3) Rule `(rule ((= |self| (BvAnd (BvAnd a b) (BvAnd (BvNot a) c))) (= |w| (Width |self|))) ((union |self| (BvAll false |w|)) (subsume (BvAnd (BvAnd a b) (BvAnd (BvNot a) c)))) :ruleset safe )` (9.833227ms)
4) Rule `(rewrite (BvAnd (BvNot (BvAnd (BvNot a) b)) (BvAnd a c)) (BvAnd a c) :subsume :ruleset safe)` (9.768259ms)
5) Rule `(rewrite (BvAnd (BvNot (BvAnd a b)) (BvAnd b c)) (BvAnd (BvNot a) (BvAnd b c)) :subsume :ruleset safe)` (9.088741ms)

#### Top rules by application time
1) Rule `(rewrite (BvOr e1 e2) (BvNot (BvAnd (BvNot e1) (BvNot e2))) :ruleset safe)` (508.416µs)
2) Rule `(rewrite (BvAnd a b) (BvAnd b a) :ruleset safe)` (439.661µs)
3) Rule `(rule ((= e (BvAnd e1 e2)) (= w (Width e1))) ((set (Width e) w)) :ruleset safe )` (273.682µs)
4) Rule `(rewrite (BvXor e1 e2) (BvNot (BvAnd (BvNot (BvAnd e1 (BvNot e2))) (BvNot (BvAnd (BvNot e1) e2)))) :ruleset safe)` (269.245µs)
5) Rule `(rewrite (BvAnd (BvNot (BvAnd a b)) (BvAnd b c)) (BvAnd (BvNot a) (BvAnd b c)) :subsume :ruleset safe)` (223.142µs)

</details>

