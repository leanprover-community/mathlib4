/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Polynomial.Hex.IsolateRoots
public import Mathlib.Analysis.Polynomial.Hex.Squarefree
public import Mathlib.Tactic.Polynomial.Hex
public meta import HexRealRoots.Isolate
public meta import HexRealRoots.Refine
public meta import HexRealRoots.Cert
public meta import HexPolyZ.IntegerPolynomial
public meta import Mathlib.Tactic.Polynomial.Hex

/-!
# The `isolate_roots` term elaborator

The production front-end that automates the `x⁴ − 2` worked example: it runs the
executable real-root isolator at elaboration time and emits a single certified
`Hex.IsolatedRealRoots` term the caller can `obtain`, `have`, or feed to `grind`.

Every proof obligation the emitted term carries is a single
`decide` on literal data against the reified Sturm chain (the replay constructor
`IsolatedRealRoots.ofCert` from `Mathlib.Analysis.Polynomial.Hex.IsolateRoots`), or a
pointwise ring identity closed by `isolate_roots_bridge`. The kernel never re-runs
the search; it only replays the exposed count-check closure against the reified
chain.

## Squarefree-core transport (`aevalIff_radical`)

Non-squarefree input is isolated on its square-free core, then transported back
onto the original polynomial. The core is reified as a *literal* `ofCoeffs`
polynomial (so the emitted certificate `decide`s reduce), but a literal core
cannot be identified with `Hex.ZPoly.squareFreeCore f` by any kernel-checkable
proof — `squareFreeCore` is deliberately outside the kernel-reducible closure
(its rational-arithmetic helpers are unexposed), so neither `rfl` (not
definitionally equal) nor `decide` (reduction gets stuck) closes
`squareFreeCore f = coreLit`. Instead the elaborator emits a **divisibility
certificate** relating the two *literal* polynomials directly: reified cofactors
`a`, `b`, a scalar `t`, and an exponent so that `orig = core * a` and
`t · core ^ (k+1) = a * b`. `aevalIff_radical` turns these two pointwise ring
identities into the real-root equivalence, which `congrRoots` uses to carry the
core's isolation onto the original polynomial. This is fully sound and needs no
`squareFreeCore` reduction.
-/

public section
set_option backward.proofsInPublic true

open Polynomial

namespace HexRealRootsMathlib

/-! # The square-free-radical transport lemma -/

/-- **Radical root-equivalence from a divisibility certificate.** Given reified
integer polynomials `orig`, `core`, `a`, `b`, a nonzero integer scalar `t`, and
an exponent `k`, the two pointwise identities

* `orig = core * a` (so every root of `core` is a root of `orig`), and
* `t · core ^ (k+1) = a * b` (so every root of `a` is a root of `core`, since `t ≠ 0`
  and `ℝ` has no zero divisors),

pin the real roots of `orig` and `core` to the same set. Used by the elaborator to
transport a square-free-core isolation onto the original non-squarefree
polynomial without ever reducing `Hex.ZPoly.squareFreeCore`. -/
theorem aevalIff_radical {orig core a b : Hex.ZPoly} {t : ℤ} {k : ℕ} (ht : t ≠ 0)
    (h1 : ∀ x : ℝ, aeval x (HexPolyZMathlib.toPolynomial orig) =
      aeval x (HexPolyZMathlib.toPolynomial core) * aeval x (HexPolyZMathlib.toPolynomial a))
    (h2 : ∀ x : ℝ, (t : ℝ) * (aeval x (HexPolyZMathlib.toPolynomial core)) ^ (k + 1) =
      aeval x (HexPolyZMathlib.toPolynomial a) * aeval x (HexPolyZMathlib.toPolynomial b)) :
    ∀ x : ℝ, aeval x (HexPolyZMathlib.toPolynomial core) = 0 ↔
      aeval x (HexPolyZMathlib.toPolynomial orig) = 0 := by
  intro x
  constructor
  · intro hc
    rw [h1 x, hc, zero_mul]
  · intro ho
    rw [h1 x] at ho
    rcases mul_eq_zero.mp ho with hc | ha
    · exact hc
    · have hz : (t : ℝ) * (aeval x (HexPolyZMathlib.toPolynomial core)) ^ (k + 1) = 0 := by
        rw [h2 x, ha, zero_mul]
      have hck : (aeval x (HexPolyZMathlib.toPolynomial core)) ^ (k + 1) = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (Int.cast_ne_zero.mpr ht)
        · exact h
      exact pow_eq_zero_iff (Nat.succ_ne_zero k) |>.mp hck

/-- Reconcile two closed reified polynomial evaluations `aeval x (…) = aeval x (…)`
by expanding every `aeval`-of-`ofCoeffs` into its explicit coefficient sum and
pushing `aeval` through the user polynomial's `X / C / + / − / * / ^ / neg`
structure, then closing with `ring`. Deliberately avoids `mul_eq_zero`, so a
factored user polynomial (e.g. Wilkinson) does not collapse into a root
disjunction. -/
macro (name := aevalRingEq) "aeval_ring_eq" : tactic =>
  `(tactic|
    (simp only [HexRealRootsMathlib.aeval_toPolynomial_ofCoeffs]
     simp [Hex.DensePoly.coeff_ofCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
       Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_sub, map_mul, map_pow, map_neg,
       map_ofNat, map_one] <;> push_cast <;> ring))

/-- Prove `∀ x, aeval x P = 0 ↔ aeval x Q = 0` for reified/closed literal
polynomials by reducing to the underlying evaluation equality. -/
macro (name := aevalIffBridge) "aeval_iff_bridge" : tactic =>
  `(tactic| (intro x; refine Iff.of_eq (congrArg (· = 0) ?_); aeval_ring_eq))

/-- Bridge tactic for the reified product identities `aevalIff_radical` consumes. -/
macro (name := isolateRootsProd) "isolate_roots_prod" : tactic =>
  `(tactic| (intro x; aeval_ring_eq))

namespace IsolateRoots

open Lean Elab Meta Term

/-! # Elaboration-time evaluation shims -/

private meta unsafe def evalZPolyUnsafe (e : Expr) : MetaM (Except String Hex.ZPoly) :=
  try return .ok (← evalExpr Hex.ZPoly (mkConst ``Hex.ZPoly) e)
  catch ex => return .error (← ex.toMessageData.toString)

@[implemented_by evalZPolyUnsafe]
private meta opaque evalZPolyCore (e : Expr) : MetaM (Except String Hex.ZPoly)

/-- Evaluate a closed `Hex.ZPoly` expression to its runtime value at elaboration
time (compiled evaluation, not kernel reduction). -/
meta def evalZPoly (e : Expr) : MetaM Hex.ZPoly := do
  match ← evalZPolyCore e with
  | .ok f => return f
  | .error msg => throwError "isolate_roots: failed to evaluate the ZPoly{indentExpr e}\n{msg}"

/-- Evaluate a closed `Rat`-typed (or `ℚ`) expression to a `Rat` at elaboration
time (hoisted to `Mathlib.Tactic.Polynomial.Hex`). -/
meta def evalRat (e : Expr) : MetaM Rat :=
  Mathlib.Tactic.Polynomial.Hex.evalRat "isolate_roots" e

/-! # The integer-polynomial interpreter

The interpreter itself (`getNat`/`evalIntLit`/`evalCoeff`/`parsePoly`) is
hoisted to `Mathlib.Tactic.Polynomial.Hex`, shared with the
`factor_poly`/`irreducibility` `Polynomial ℤ` provider. -/

/-- Recursive interpreter from a `Polynomial R` expression to a `Hex.ZPoly`
value (hoisted to `Mathlib.Tactic.Polynomial.Hex`). `isRat` selects the `ℚ`-style
non-integer rejection. -/
meta def parsePoly (isRat : Bool) (fuel : Nat) (e : Expr) : MetaM Hex.ZPoly :=
  Mathlib.Tactic.Polynomial.Hex.parsePoly "isolate_roots" isRat fuel e

/-! # Exact integer-polynomial arithmetic (for the radical certificate) -/

/-- `base ^ k` for `Hex.ZPoly`, via the executable `Mul` (`csimp` to `mulImpl`). -/
meta def powZ (base : Hex.ZPoly) (k : Nat) : Hex.ZPoly := Id.run do
  let mut acc : Hex.ZPoly := Hex.DensePoly.C 1
  for _ in [0:k] do acc := acc * base
  return acc

/-- Exact long division of integer coefficient arrays (ascending degree),
returning the quotient coefficients when the division is exact, else `none`. -/
meta def divExactInt (num den : Array Int) : Option (Array Int) := Id.run do
  -- trim trailing zeros
  let trim (a : Array Int) : Array Int := Id.run do
    let mut a := a
    while a.size > 0 && a[a.size - 1]! == 0 do a := a.pop
    return a
  let num := trim num
  let den := trim den
  if den.size == 0 then return none
  let ld := den[den.size - 1]!
  if num.size < den.size then
    return if num.size == 0 then some #[0] else none
  let qdeg := num.size - den.size
  let mut rem := num
  let mut q : Array Int := Array.replicate (qdeg + 1) 0
  let mut i := qdeg
  let mut ok := true
  for _ in [0:qdeg + 1] do
    let hi := rem[i + den.size - 1]!
    if hi % ld != 0 then
      ok := false
    else
      let qc := hi / ld
      q := q.set! i qc
      for j in [0:den.size] do
        rem := rem.set! (i + j) (rem[i + j]! - qc * den[j]!)
    if i == 0 then pure () else i := i - 1
  if !ok then return none
  -- remainder must be zero
  for r in rem do
    if r != 0 then return none
  return some (trim q)

/-! # Backend run -/

/-- The certified isolation data extracted at elaboration time: a reified
polynomial (the square-free core, when a swap happened), its Sturm chain, and the
per-root dyadic endpoints. -/
structure IsoData where
  /-- The reified polynomial whose roots are isolated. -/
  poly : Hex.ZPoly
  /-- The executable Sturm chain used to certify the result. -/
  chain : Array Hex.ZPoly
  /-- One dyadic interval for each distinct real root. -/
  endpoints : Array (Dyadic × Dyadic)

/-- Run the compiled isolator on `f` (assumed square-free with a nonzero
constant Sturm tail), optionally refining every root to width `2 ^ (-widthK)`
through the cached-chain `refineToWithChain`. -/
meta def runBackend (f : Hex.ZPoly) (widthK : Option Int) : MetaM IsoData := do
  let some out := Hex.isolate? f
    | throwError "isolate_roots: internal error: the backend isolate? returned none on \
        square-free input (please report this as a bug)"
  let chain := Hex.ZPoly.sturmChain f
  let isos := out.isolations
  let refined := match widthK with
    | some k => isos.map (fun iso : Hex.RealRootIsolation f =>
        Hex.RealRootIsolation.refineToWithChain chain rfl iso k)
    | none => isos
  let endpoints := refined.map
    (fun iso : Hex.RealRootIsolation f => (iso.interval.lower, iso.interval.upper))
  return { poly := f, chain, endpoints }

/-! # Reification helpers (term syntax) -/

/-- Term syntax for an `Int` literal. -/
meta def intStx (c : Int) : MetaM (TSyntax `term) := do
  let numLit := Syntax.mkNumLit (toString c.natAbs)
  if c < 0 then `((-$numLit : Int)) else `(($numLit : Int))

/-- Term syntax for a `Nat` literal. -/
meta def natStx (n : Nat) : TSyntax `term := Syntax.mkNumLit (toString n)

/-- Term syntax for a reified `Hex.ZPoly` as `Hex.DensePoly.ofCoeffs #[…]`. -/
meta def zpolyStx (f : Hex.ZPoly) : MetaM (TSyntax `term) := do
  let elems ← f.toArray.mapM intStx
  `(Hex.DensePoly.ofCoeffs #[$elems,*])

/-- Term syntax for a `Dyadic` endpoint as `Dyadic.ofInt m` or
`Dyadic.ofInt m >>> (s : Int)` (the denominator is a power of two). -/
meta def dyadicStx (d : Dyadic) : MetaM (TSyntax `term) := do
  let q := d.toRat
  let mStx ← intStx q.num
  if q.den == 1 then
    `(Dyadic.ofInt $mStx)
  else
    let s := q.den.log2
    let sStx ← intStx (Int.ofNat s)
    `(Dyadic.ofInt $mStx >>> ($sStx : Int))

/-! # Emission -/

/-- Emit the replay term `IsolatedRealRoots.ofCert` for `d.poly` (a square-free
polynomial), stated over `HexPolyZMathlib.toPolynomial d.poly`. Every field is a
`decide` on literals against the reified chain. -/
meta def emitOfCert (d : IsoData) : MetaM (TSyntax `term) := do
  let fStx ← zpolyStx d.poly
  let chainStxs ← d.chain.mapM zpolyStx
  let chainStx ← `((#[$chainStxs,*] : Array Hex.ZPoly))
  let nLit := natStx d.endpoints.size
  let isoStxs ← d.endpoints.mapM fun (lower, upper) => do
    let loStx ← dyadicStx lower
    let hiStx ← dyadicStx upper
    `(term| (⟨⟨$loStx, $hiStx, by decide⟩,
        HexRealRootsMathlib.RealRootIsolation.count_one_of_cert (chain := $chainStx)
          (by decide) _ (by decide)⟩ : Hex.RealRootIsolation $fStx))
  -- Present the intervals as pretty rational literals (`m` or `m / 2^k`), so
  -- the `intervals` field is definitionally a `#v[…]` literal and user-side
  -- extraction is `show … from rfl`. Each endpoint identity is stated over ℝ
  -- against the literal `iso` argument itself (`Dyadic.toReal` of the reified
  -- dyadic — pure structure/literal reductions in the user module), and
  -- discharged through the dyadic `toReal` cast lemmas: no `Rat`
  -- normalization anywhere near the kernel.
  let ratStx (d : Dyadic) : MetaM (TSyntax `term) := do
    let q := d.toRat
    let mStx ← intStx q.num
    if q.den == 1 then `(($mStx : ℚ)) else
      let sStx := natStx q.den.log2
      `((($mStx : ℚ) / 2 ^ ($sStx : ℕ) : ℚ))
  let endpointPf (d : Dyadic) : MetaM (TSyntax `term) := do
    let dStx ← dyadicStx d
    let qStx ← ratStx d
    `((by
        simp only [HexRealRootsMathlib.toReal_ofInt,
          HexRealRootsMathlib.toReal_ofInt_shiftRight]
        push_cast
        norm_num :
      (($qStx : ℝ) = HexRealRootsMathlib.Dyadic.toReal $dStx)))
  let pairStxs ← d.endpoints.mapM fun (lower, upper) => do
    let loQ ← ratStx lower
    let hiQ ← ratStx upper
    `(term| ($loQ, $hiQ))
  let pairPfs ← d.endpoints.mapM fun (lower, upper) => do
    let loPf ← endpointPf lower
    let hiPf ← endpointPf upper
    `(term| ⟨$loPf, $hiPf⟩)
  `(Hex.IsolatedRealRoots.ofCertPretty (chain := $chainStx)
      (iso := (⟨#[$isoStxs,*], rfl⟩ : Vector (Hex.RealRootIsolation $fStx) $nLit))
      (w := (⟨#[$pairStxs,*], rfl⟩ : Vector (ℚ × ℚ) $nLit))
      (hsize := by decide) (hsf := by decide) (hcert := by decide)
      (hordered := by decide) (hcomplete := by decide)
      (hw := by intro i; fin_cases i <;> first $[| exact $pairPfs]*))

/-! # Width target -/

/-- Convert a positive rational width `q` to the bit target `k = max 0 ⌈log₂ q⁻¹⌉`
in exact integer arithmetic: the least `k ≥ 0` with `2 ^ (-k) ≤ q`. Widths above
`1` give `k = 0` (they never coarsen the natural intervals). Targets finer than
`2 ^ (-4096)` are rejected as pathological. -/
meta def widthTarget (q : Rat) : MetaM Int := do
  let inv := q⁻¹
  let mut k : Nat := 0
  let mut pw : Rat := 1
  while pw < inv do
    if k ≥ 4096 then
      throwError "isolate_roots: pathological width (finer than 2^-4096); the isolation \
        would be astronomically large. Refine the result manually if you truly need this."
    k := k + 1
    pw := pw * 2
  return Int.ofNat k

/-! # The square-free-radical divisibility certificate -/

/-- Trimmed coefficient array (drop trailing zeros). -/
private meta def trimArr (a : Array Int) : Array Int := Id.run do
  let mut a := a
  while a.size > 0 && a[a.size - 1]! == 0 do a := a.pop
  return a

/-- Compute the divisibility certificate `(a, b, t, k)` witnessing that `orig`
and `core` share their real roots: `orig = core * a` and `t · core ^ (k+1) = a * b`
with `t ≠ 0`, all as integer-polynomial identities. Throws the internal
certificate-mismatch error if the executable decomposition does not reassemble
(a bug). -/
meta def radicalCert (orig core : Hex.ZPoly) :
    MetaM (Hex.ZPoly × Hex.ZPoly × Int × Nat) := do
  let msg := "isolate_roots: internal certificate mismatch in the square-free-core \
     transport (please report this as a bug)"
  let some aC := divExactInt orig.toArray core.toArray | throwError msg
  let a := Hex.DensePoly.ofCoeffs aC
  let rep := Hex.ZPoly.primitivePart a
  let repArr := rep.toArray
  let aArr := a.toArray
  if repArr.size == 0 || aArr.size == 0 then throwError msg
  let t := aArr[aArr.size - 1]! / repArr[repArr.size - 1]!
  let mut found : Option (Hex.ZPoly × Nat) := none
  for ee in [1:orig.size + 2] do
    if found.isNone then
      match divExactInt (powZ core ee).toArray repArr with
      | some bC => found := some (Hex.DensePoly.ofCoeffs bC, ee)
      | none => pure ()
  let some (b, e) := found | throwError msg
  -- sanity: core * a = orig, t • rep = a, rep * b = core ^ e
  if trimArr (core * a).toArray != trimArr orig.toArray then throwError msg
  if trimArr (Hex.DensePoly.scale t rep).toArray != trimArr aArr then throwError msg
  if trimArr (rep * b).toArray != trimArr (powZ core e).toArray then throwError msg
  if t == 0 then throwError msg
  return (a, b, t, e - 1)

/-! # The driver -/

/-- Emit `coreTerm : IsolatedRealRoots (toPolynomial fLit) n` for the reflected
integer polynomial `f` (the reflection of the user's input), classifying it as
zero / nonzero constant / square-free / non-squarefree and routing accordingly. -/
meta def emitIsolation (f : Hex.ZPoly) (widthK : Option Int) : MetaM (TSyntax `term) := do
  let fStx ← zpolyStx f
  if f.size == 0 then
    throwError "isolate_roots: the zero polynomial (every real number is a root, \
      so there is no finite isolation)"
  else if f.size == 1 then
    -- nonzero constant: no real roots, via the landed `IsolatedRealRoots.constant`
    -- transported onto `toPolynomial fLit`.
    let cStx ← intStx (f.coeff 0)
    `(Hex.IsolatedRealRoots.congrRoots (Q := HexPolyZMathlib.toPolynomial $fStx)
        (by aeval_iff_bridge)
        (Hex.IsolatedRealRoots.constant (c := ($cStx : Int))
          (by simp only [eq_intCast, ne_eq, Int.cast_eq_zero]; decide)))
  else if Hex.ZPoly.hasSquarefreeSturmChain f then
    let d ← runBackend f widthK
    emitOfCert d
  else
    -- non-squarefree: isolate the square-free core, transport by the radical cert
    let core := Hex.ZPoly.squareFreeCore f
    let d ← runBackend core widthK
    let coreCert ← emitOfCert d
    let coreStx ← zpolyStx core
    let (a, b, t, k) ← radicalCert f core
    let aStx ← zpolyStx a
    let bStx ← zpolyStx b
    let tStx ← intStx t
    let kStx := natStx k
    `(Hex.IsolatedRealRoots.congrRoots
        (HexRealRootsMathlib.aevalIff_radical (orig := $fStx) (core := $coreStx)
          (a := $aStx) (b := $bStx) (t := $tStx) (k := $kStx)
          (by decide) (by isolate_roots_prod) (by isolate_roots_prod))
        $coreCert)

/-- Shared driver for the `isolate_roots` term elaborator. -/
meta def elabIsolate (widthStx : Option (TSyntax `term)) (pStx : TSyntax `term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  -- width
  let widthK ← match widthStx with
    | none => pure none
    | some w => do
      let wE ← elabTermEnsuringType w (some (mkConst ``Rat))
      Term.synthesizeSyntheticMVarsNoPostponing
      let wE ← instantiateMVars wE
      if wE.hasFVar || wE.hasExprMVar then
        throwError "isolate_roots: the width must be a closed rational \
          (no free variables or metavariables){indentExpr wE}"
      let q ← evalRat wE
      if q ≤ 0 then throwError "isolate_roots: the width must be strictly positive"
      pure (some (← widthTarget q))
  -- When the expected type is `IsolatedRealRoots (P : Polynomial R) n`, the
  -- coefficient ring `R` pins the argument's type, so `isolate_roots (X^4 - 2)`
  -- elaborates without a type ascription. A `ZPoly` argument cannot take a
  -- `Polynomial R` expected type, so this is a hint with a fallback, not a
  -- requirement.
  let expectedPolyTy? : Option Expr ← do
    match expectedType? with
    | none => pure none
    | some et =>
      let et ← whnfR (← instantiateMVars et)
      let args := et.getAppArgs
      if et.getAppFn.isConstOf ``Hex.IsolatedRealRoots && args.size ≥ 5 then
        -- the type of the expected `P` argument is `Polynomial R`, the hint we want
        pure (some (← inferType args[3]!))
      else pure none
  -- polynomial: elaborate and dispatch on its type. A `ZPoly` argument and a
  -- type-ascribed polynomial both elaborate with no expected type; only a bare
  -- `X^4 - 2` needs the expected `Polynomial R` to pin its ring, so that hint is
  -- a fallback used exactly when the unhinted elaboration fails or stays
  -- ambiguous.
  let s ← saveState
  let pE ←
    try
      let e ← elabTerm pStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasExprMVar then throwError "isolate_roots: ambiguous argument"
      pure e
    catch _ =>
      s.restore (restoreInfo := true)
      match expectedPolyTy? with
      | some pt => elabTermEnsuringType pStx (some pt)
      | none => elabTerm pStx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let pE ← instantiateMVars pE
  if pE.hasFVar || pE.hasExprMVar then
    throwError "isolate_roots: the polynomial must be a closed term \
      (no free variables or metavariables){indentExpr pE}"
  let ty ← whnfR (← inferType pE)
  let tyFn := ty.getAppFn
  let tyArgs := ty.getAppArgs
  let isZPoly := tyFn.isConstOf ``Hex.DensePoly && tyArgs.size ≥ 1 && tyArgs[0]!.isConstOf ``Int
  let isPoly := tyFn.isConstOf ``Polynomial
  let (f, isPolyInput) ←
    if isZPoly then
      pure (← evalZPoly pE, false)
    else if isPoly then do
      let R := tyArgs[0]!
      unless R.isConstOf ``Int || R.isConstOf ``Rat || R.isConstOf ``Real do
        throwError "isolate_roots: unsupported coefficient ring{indentExpr R}\n\
          expected `Polynomial ℤ`, `Polynomial ℚ`, or `Polynomial ℝ` \
          (with integer coefficients)"
      let isRatRing := R.isConstOf ``Rat
      pure (← parsePoly isRatRing 8 pE, true)
    else
      throwError "isolate_roots: expected a closed `Hex.ZPoly` or `Polynomial ℤ/ℚ/ℝ` \
        term, but the argument has type{indentExpr ty}"
  let coreTerm ← emitIsolation f widthK
  let term ←
    if isPolyInput then
      `(Hex.IsolatedRealRoots.congrRoots (Q := $pStx) (by aeval_iff_bridge) $coreTerm)
    else
      -- Certify the DTO: restate over the USER'S term. The transport
      -- hypothesis closes by `rfl` exactly when the supplied term is
      -- definitionally the evaluated polynomial, so a faulty evaluation
      -- fails elaboration rather than silently changing the theorem's
      -- subject. Irreducible inputs fail with a clear message.
      `(Hex.IsolatedRealRoots.congrRoots
          (Q := HexPolyZMathlib.toPolynomial $pStx)
          (by first
            | exact fun x => Iff.rfl
            | fail "isolate_roots: cannot certify that the evaluated \
                polynomial is definitionally the supplied term (is the \
                definition irreducible?)")
          $coreTerm)
  Term.elabTermEnsuringType term expectedType?

/-! # Syntax -/

/-- `isolate_roots p` / `isolate_roots (width := x) p`. The `atomic` lookahead on
`"(" "width" ":="` lets a parenthesised polynomial argument (e.g.
`(X^4 - 2 : Polynomial ℝ)`) parse as the polynomial rather than the width group. -/
syntax (name := isolateRoots) "isolate_roots"
  (atomic("(" "width" ":=") term ")")? term : term

/-- Elaborate `isolate_roots`, run the compiled search, and emit a replay term
whose certificate obligations are checked by Lean. -/
@[term_elab isolateRoots]
meta def elabIsolateRoots : TermElab := fun stx expectedType? => do
  match stx with
  | `(isolate_roots (width := $wt:term) $p:term) => elabIsolate (some wt) p expectedType?
  | `(isolate_roots $p:term) => elabIsolate none p expectedType?
  | _ => throwUnsupportedSyntax

end IsolateRoots

end HexRealRootsMathlib
