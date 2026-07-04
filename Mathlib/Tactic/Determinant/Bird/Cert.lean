/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.Determinant.Bird.Meta
public meta import Mathlib.Tactic.Ring

/-!

# Certificate-chain evaluator for `BirdDet.birdDet`

This file contains an evaulator that computes the ring tactic normal form of
`Mathlib.LinearAlgebra.Matrix.Determinant.Bird.birdDet` via iteratively
unfolding its definition, using the ring tactic for ring operations, and caching
intermediate certificates.

The structure `Cert rα` carries the proof certificate and the evaluator builds
larger certificates as `birdDet` is unfolded.

The entrypoint of the evaluator `certBirdDet` follows the two branches (n=0,
n=k+1) of the `birdDet` function:

```
certBirdDet (birdDet n A)
  n = 0:
    birdDet n A
      = 1 -- via BirdDet.birdDet_zero
      = ring normal form of 1 -- via certEval
  n = k + 1:
    birdDet n A
      = (-1)^k * iter n A k (get n A) 0 0 -- via BirdDet.birdDet_eq
      = ring normal form of the product -- certMul (certBirdSign k) (certIter k 0 0)
```

The `iter n A k (get n A) i j` function branches on k, (k=0, k=t+1) and
therefore the `certIter` function has two branches:

```
certIter k i j
  k = 0:
    iter n A 0 F i j = F i j -- via BirdDet.iter_zero
                     = ring normal form of A[i][j] -- via certEntry i j
  k = t + 1:
    iter n A (t + 1) F i j
      = -(sumFrom n (i + 1) fun k => iter n A t F k k) * get n A i j
          + sumFrom n (i + 1) fun k => iter n A t F i k * get n A k j
        -- via BirdDet.iter_succ
      = normal form of the first summand + normal form of the second summand
        -- via certAdd
                 (certMul (certNeg (certDiag t (i + 1))) (certEntry i j))
                 (certTail t i j (i + 1))
```

Then the `certDiag` and `certTail` functions certify the two kinds of `sumFrom`
expressions.

The evaulator also memoizes the `certIter`, `certDiag` and `certEntry` functions
to improve performance.

## Main definitions

- `certEntry` certifies `BirdDet.get`.
- `certSumFromStop` and `certSumFromStep` certifies `BirdDet.sumFrom_stop` and
  `BirdDet.sumFrom_step`.
- `certIter` certifies `BirdDet.iter_zero` and `BirdDet.iter_succ`.
- `certBirdDet` certifies `BirdDet.birdDet_zero` and `BirdDet.birdDet_eq`.
-/

public meta section

open Lean Meta Qq
open Mathlib.Tactic.Ring

variable {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}

namespace Mathlib.Tactic.Determinant

/-- The ring tactic normal-form value. -/
abbrev CertVal {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (e : Q($α)) :=
  Common.ExSum RatCoeff (commSemiringOfCommRing rα) e

/-- The ring tactic result carried by a certificate. -/
abbrev CertResult {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (subject : Q($α)) :=
  Common.Result (CertVal rα) subject

namespace Ctx

/-- Return an expression for the partially applied function `iter n A t (get n A)` -/
def iterP (ctx : Ctx rα) (t : ℕ) : Q(ℕ → ℕ → $α) :=
  let dim : Q(ℕ) := ctx.dimensionLit
  let A : Q(Array $α) := ctx.arrayExpr
  q(BirdDet.iter $dim $A $t (BirdDet.get $dim $A))

/-- Return an expression `sumFrom n lo f` -/
def sumFrom (ctx : Ctx rα) (lo : ℕ) (f : Q(ℕ → $α)) : Q($α) :=
  let dim : Q(ℕ) := ctx.dimensionLit
  q(BirdDet.sumFrom $dim $lo $f)

end Ctx

/-- A certificate that proves `subject = result.norm` via `result.proof` -/
structure Cert {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- The expression being certified. -/
  {subject : Q($α)}
  /-- The result of evaluating `subject` using the ring tactic. -/
  result : CertResult rα subject
  /-- `true` when `norm` is zero, used as a hint to the evaluator. -/
  isZero : Bool

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

/-- The ring tactic normal form of `c.subject` -/
def norm (c : Cert rα) : Q($α) :=
  c.result.expr

/-- The internal ring tactic representation of `c.norm` -/
def val (c : Cert rα) : CertVal rα c.norm :=
  c.result.val

/-- The proof that `c.subject = c.norm` -/
def proof (c : Cert rα) : Q($c.subject = $c.norm) :=
  c.result.proof

/-- Prepend an equality to an existing normalized certificate.

Given `c.proof : s.subject = c.norm` and `h : lhs = s.subject` return a
certificate with `proof : lhs = c.norm`.
-/
def chainProof {lhs rhs : Q($α)} (c : Cert rα) (h : Q($lhs = $rhs)) : Cert rα :=
  have : $rhs =Q $c.subject := ⟨⟩
  let hProof : Q($lhs = $c.subject) := h
  let proof : Q($lhs = $c.norm) := q(Eq.trans $hProof $c.proof)
  { c with
    subject := lhs
    result.proof := proof
  }

end Cert

/-- Cache certificates that are reused by the recursive Bird evaluator. -/
structure CertCache {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- Cache for entry certificates, keyed by matrix indices. -/
  entryCache : Std.HashMap (ℕ × ℕ) (Cert rα) := {}
  /-- Cache for `iter` certificates, keyed by recursion index and matrix indices. -/
  iterCache : Std.HashMap (ℕ × ℕ × ℕ) (Cert rα) := {}
  /-- Cache for diagonal-tail certificates, keyed by recursion index and lower bound. -/
  diagCache : Std.HashMap (ℕ × ℕ) (Cert rα) := {}

/-- The monad used by the certificate-chaining evaluator -/
abbrev CertM {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) :=
  StateT (CertCache rα) (ReaderT (Ctx rα) AtomM)

/-- Checks if `val` is zero according to the ring tactic -/
def isZeroVal {e : Q($α)} (val : CertVal rα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/-- Construct a `Cert rα` from a ring tactic result -/
def toCert {e : Q($α)} (res : Common.Result (CertVal rα) e) : Cert rα :=
  { result := res
    isZero := isZeroVal res.val }

/-- Build a zero certificate from a proof `lhs = 0`. -/
def zeroCertOfProof {lhs : Q($α)} (h : Q($lhs = 0)) : Cert rα where
  result.expr := q(0)
  result.val := .zero
  result.proof := h
  isZero := true

/-- If c.norm = 0, return a certificate with proof `x * c.subject = 0` without
recursively certifying `x`. -/
def zeroProdCert (x : Q($α)) (c : Cert rα) :
    MetaM (Cert rα) := do
  let zero : Q($α) := q(0)
  have : $c.norm =Q $zero := ⟨⟩
  let h : Q($x * $c.subject = $x * $zero) :=
    q(congrArg (fun y => $x * y) $c.proof)
  return zeroCertOfProof q(Eq.trans $h (mul_zero $x))

/-- Certify `e = norm` by evaluating `e` with the `ring` normalizer. -/
def certEval (e : Q($α)) : CertM rα (Cert rα) := do
  let ctx ← read
  let res ← Common.eval rcℕ ctx.rc ctx.cα e
  return toCert res

/-- Certify `a.subject + b.subject` from certificates for `a` and `b`. -/
def certAdd (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalAdd ctx.rc rcℕ a.val b.val
  let h : Q($a.subject + $b.subject = $a.norm + $b.norm) :=
    q(congr (congrArg (fun x y => x + y) $a.proof) $b.proof)
  return c.chainProof h

/-- Certify `a.subject * b.subject` from certificates for `a` and `b`. -/
def certMul (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalMul ctx.rc rcℕ a.val b.val
  let h : Q($a.subject * $b.subject = $a.norm * $b.norm) :=
    q(congr (congrArg (fun x y => x * y) $a.proof) $b.proof)
  return c.chainProof h

/-- Certify `-a.subject` from a certificate for `a`. -/
def certNeg (a : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalNeg ctx.rc rα a.val
  let h : Q(-$a.subject = -$a.norm) :=
    q(congrArg (fun x => -x) $a.proof)
  return c.chainProof h

/-- Certify the sign factor `(-1)^k` from `BirdDet.birdDet_eq`. -/
def certBirdSign (k : ℕ) : CertM rα (Cert rα) := do
  certEval q((-1 : $α) ^ $k)

/-- Certify one matrix entry lookup `BirdDet.get n A i j`. -/
def certEntry (i j : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr := A, arrayEntries, ..} := ctx
  let lhs : Q($α) := q(BirdDet.get $dimLit $A $i $j)
  -- The index of the matrix entry (i, j) in arrayEntries
  let idx := i * dim + j
  let entry := arrayEntries.getD idx q(0)
  let ce ← certEval entry
  have : $lhs =Q $entry := ⟨⟩
  let h : Q($lhs = $entry) := q(rfl)
  let cert := ce.chainProof h
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

/-- Certify the stop branch of `BirdDet.sumFrom`.

This corresponds to the `else 0` branch of:

```
sumFrom n lo f = if lo < n then f lo + sumFrom n (lo + 1) f else 0
```

Throws a meta-level error if called with `lo` such that `lo < ctx.dimension`.
-/
def certSumFromStop (lo : ℕ) (f : Q(ℕ → $α)) : CertM rα (Cert rα) := do
  let ctx ← read
  if lo < ctx.dimension then
    throwError "certSumFromStop called with {lo} such that {lo} < {ctx.dimension}"
  have dimLit : Q(ℕ) := ctx.dimensionLit
  let hNot : Q(¬ $lo < $dimLit) ← mkDecideProofQ q(¬ $lo < $dimLit)
  return zeroCertOfProof q(BirdDet.sumFrom_stop $dimLit $lo $f $hNot)

/-- Certify the step branch of `BirdDet.sumFrom`.

This corresponds to the `lo < n` branch of:

```
sumFrom n lo f = if lo < n then f lo + sumFrom n (lo + 1) f else 0
```

Throws a meta-level error if called with `lo` such that `¬ lo < ctx.dimension`.
-/
def certSumFromStep
    (lo : ℕ) (f : Q(ℕ → $α))
    (headCert tailCert : CertM rα (Cert rα)) : CertM rα (Cert rα) := do
  let ctx ← read
  unless lo < ctx.dimension do
    throwError "certSumFromStep called with {lo} such that ¬ {lo} < {ctx.dimension}"
  have dim : Q(ℕ) := ctx.dimensionLit
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let sumCert ← certAdd (← headCert) (← tailCert)
  return sumCert.chainProof q(BirdDet.sumFrom_step $dim $lo $f $hLt)

mutual

/-- Certify a `BirdDet.iter` call. -/
partial def certIter (t i j : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).iterCache[(t, i, j)]? then
    return c
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let cert ← match t with
    -- The t=0 branch of `BirdDet.iter`, unfold using `BirdDet.iter_zero`
    | 0 => do
      let ce ← certEntry i j
      let h := q(BirdDet.iter_zero $dimLit $A (BirdDet.get $dimLit $A) $i $j)
      pure (ce.chainProof h)
    -- The t=t+1 branch of `BirdDet.iter`, unfold using `BirdDet.iter_succ`
    | t' + 1 => do
      -- First summand in `BirdDet.iter_succ`:
      --   -(sumFrom n (i + 1) fun k => F_t k k) * get n A i j
      let diagSummand := q(fun k => $(ctx.iterP t') k k)
      let negDiagSum := q(-$(ctx.sumFrom (i + 1) diagSummand))
      let entryCert ← certEntry i j
      let diagProdCert ←
        -- If `get n A i j = 0` then we can skip computation of
        --  `-(sumFrom n (i + 1) fun k => F_t k k)`
        if entryCert.isZero then
          zeroProdCert negDiagSum entryCert
        else do
          let diagSumCert ← certDiag t' (i + 1)
          let negDiagSumCert ← certNeg diagSumCert
          certMul negDiagSumCert entryCert
      -- Second summand in `BirdDet.iter_succ`:
      --   sumFrom n (i + 1) fun k => F_t i k * get n A k j
      let tailSumCert ← certTail t' i j (i + 1)
      let rhsCert ← certAdd diagProdCert tailSumCert
      let h := q(BirdDet.iter_succ $dimLit $A $t' (BirdDet.get $dimLit $A) $i $j)
      pure (rhsCert.chainProof h)
  modify fun s => {s with iterCache := s.iterCache.insert (t, i, j) cert}
  return cert


/-- Certify the diagonal tail sum from `BirdDet.iter_succ`:

```
sumFrom n (i + 1) fun k => iter n A t F k k)
```
-/
partial def certDiag (t lo : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterP t) k k)
  let cert ←
    if lo < ctx.dimension
    then do
      let headCert := certIter t lo lo
      let tailCert := certDiag t (lo + 1)
      certSumFromStep
        lo
        diagonalSummand
        headCert
        tailCert
    else
      certSumFromStop lo diagonalSummand
  modify fun s => {s with diagCache := s.diagCache.insert (t, lo) cert}
  return cert

/-- Certify the upper-tail sum from `BirdDet.iter_succ`:

```
sumFrom n (i + 1) fun k => iter n A t F i k * get n A k j
```
-/
partial def certTail (t i j lo : ℕ) : CertM rα (Cert rα) := do
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let tailSummand :=
    q(fun k =>
      $(ctx.iterP t) $i k *
        BirdDet.get $dimLit $A k $j)
  if lo < ctx.dimension
  then do
    -- headCert certifies `iter n A t F i lo * get n A lo j`
    let headCert := do
      let entryCert ← certEntry lo j
      -- If `get n A lo j = 0` then we can skip computation of
      --  `iter n A t F i lo`
      if entryCert.isZero
      then
        zeroProdCert
          q($(ctx.iterP t) $i $lo)
          entryCert
      else do
        let iterCert ← certIter t i lo
        certMul iterCert entryCert
    let tailCert := certTail t i j (lo + 1)
    certSumFromStep
      lo
      tailSummand
      headCert
      tailCert
  else
    certSumFromStop lo tailSummand

end

/-- Certify a `BirdDet.birdDet n A` call. -/
def certBirdDet : CertM rα (Cert rα) := do
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr, ..} := ctx
  if dim == 0
  then
    let ce ← certEval q(1 : $α)
    have : $dimLit =Q 0 := ⟨⟩
    have A : Q(Array $α) := arrayExpr
    let h := q(BirdDet.birdDet_zero $A)
    return ce.chainProof h
  else
    -- The non-zero `BirdDet.birdDet_eq` branch matches `k + 1`
    -- so we set k := `ctx.dimension - 1`.
    let k := dim - 1
    let cs ← certBirdSign k
    let ci ← certIter k 0 0
    let cm ← certMul cs ci
    have kLit := mkNatLitQ k
    have : $dimLit =Q $kLit + 1 := ⟨⟩
    let hn : Q($dimLit = $kLit + 1) := q(rfl)
    let h := q(BirdDet.birdDet_eq $dimLit $kLit $arrayExpr $hn)
    return cm.chainProof h

end Mathlib.Tactic.Determinant

end
