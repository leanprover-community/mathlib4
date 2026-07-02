/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# `poly_dvd_cert`: divisibility of `Polynomial K` by **symbolic certificate**

A `polyrith`/`linarith`-style tactic: search for the quotient uncertified, then check it certified.

For `p q : Polynomial K` over any field `K` (coefficients may be concrete *or* symbolic), it:

1. parses `p`, `q` into dense vectors of coefficient **expressions** (elements of `K`);
2. runs **pseudo-division in `MetaM`** — plain compiled Lean, like `norm_num`'s arithmetic, so it
   never enters the proof term and adds **no axiom**, in particular **no `native_decide`** —
   producing
   a quotient `Q` and the scale `d ^ δ` (`d` = leading coefficient of `p`, `δ = deg q - deg p + 1`)
   with the universal identity `d ^ δ • q = p * Q + (remainder)`;
3. closes the goal with `(IsUnit (C (d ^ δ))).dvd_mul_left.mp ⟨Q, by simp only [map_…]; ring⟩`, i.e.
   verifies `C (d ^ δ) * q = p * Q` by `ring` and cancels the leading-coefficient unit.

The kernel never divides. Because pseudo-division scales by powers of `d`, the certified identity is
**division-free**, so plain `ring` checks it over the (commutative) coefficient ring. The only field
input is that `d ^ δ` is a unit, i.e. `d ≠ 0`; this side goal is discharged automatically when it is
a nonzero numeral or follows from a hypothesis, and otherwise is **left for the user** (e.g. a
symbolic
non-monic divisor needs its leading coefficient `≠ 0`). Monic divisors need nothing — they even work
over any commutative ring.
-/

open Lean Elab Tactic Meta

namespace Polynomial.DvdCert

/-- Read a `ℕ` literal `Expr` (a raw `Nat` literal or one wrapped in `OfNat.ofNat`). -/
private def natLit? (e : Expr) : Option ℕ :=
  let raw (x : Expr) : Option ℕ := match x with
    | .lit (.natVal m) => some m
    | _ => none
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, lit, _]) => raw lit
  | _ => raw e

/-- Is `e` the numeral `n` (raw literal or via `OfNat`)? -/
private def isNatLit (n : ℕ) (e : Expr) : Bool := natLit? e == some n

/-! ### Smart constructors for coefficient (`K`-valued) expressions, with `0`/`1` peephole -/

private def kMul (a b : Expr) : MetaM Expr := do
  if isNatLit 0 a then return a
  if isNatLit 0 b then return b
  if isNatLit 1 a then return b
  if isNatLit 1 b then return a
  mkAppM ``HMul.hMul #[a, b]

private def kAdd (a b : Expr) : MetaM Expr := do
  if isNatLit 0 a then return b
  if isNatLit 0 b then return a
  mkAppM ``HAdd.hAdd #[a, b]

private def kSub (a b : Expr) : MetaM Expr := do
  if isNatLit 0 b then return a
  if isNatLit 0 a then return (← mkAppM ``Neg.neg #[b])
  mkAppM ``HSub.hSub #[a, b]

private def kNeg (a : Expr) : MetaM Expr := do
  if isNatLit 0 a then return a
  mkAppM ``Neg.neg #[a]

/-! ### Dense polynomial arithmetic over coefficient expressions
(index `i` ↦ coefficient of `Xⁱ`) -/

/-- Pointwise combine, padding the shorter vector with the zero expression `z`. -/
private def kZip (op : Expr → Expr → MetaM Expr) (z : Expr) (a b : Array Expr) :
    MetaM (Array Expr) := do
  let n := max a.size b.size
  let mut r := (List.replicate n z).toArray
  for i in [0:n] do
    r := r.set! i (← op (a.getD i z) (b.getD i z))
  return r

private def kConv (z : Expr) (a b : Array Expr) : MetaM (Array Expr) := do
  if a.isEmpty || b.isEmpty then return #[]
  let mut r := (List.replicate (a.size + b.size - 1) z).toArray
  for i in [0:a.size] do
    for j in [0:b.size] do
      r := r.set! (i + j) (← kAdd r[i + j]! (← kMul a[i]! b[j]!))
  return r

private def kPow (z one : Expr) (a : Array Expr) : ℕ → MetaM (Array Expr)
  | 0 => pure #[one]
  | n + 1 => do kConv z a (← kPow z one a n)

/-- Drop trailing zero coefficients. -/
private partial def trimZeros (a : Array Expr) : Array Expr :=
  if 0 < a.size then
    if isNatLit 0 a[a.size - 1]! then trimZeros a.pop else a
  else a

/-- Parse a `Polynomial K` expression into a dense vector of coefficient expressions in `K`
(`z`, `one` are the expressions `(0 : K)`, `(1 : K)`). -/
private partial def toCoeffs (K z one : Expr) (e : Expr) : MetaM (Array Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => kZip kAdd z (← toCoeffs K z one a) (← toCoeffs K z one b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => kZip kSub z (← toCoeffs K z one a) (← toCoeffs K z one b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => kConv z (← toCoeffs K z one a) (← toCoeffs K z one b)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some n := natLit? k | throwError "poly_dvd_cert: non-literal exponent {k}"
      kPow z one (← toCoeffs K z one a) n
  | (``Neg.neg, #[_, _, a]) => (← toCoeffs K z one a).mapM kNeg
  | (``Polynomial.X, _) => pure #[z, one]
  | (``DFunLike.coe, #[_, _, _, _, f, c]) =>
      match f.getAppFnArgs with
      | (``Polynomial.C, _) => pure #[c]                            -- `C c`  ↦  constant `c`
      | (``algebraMap, _) => pure #[c]                              -- `algebraMap _ _ c`  ↦  `c`
      | (``Polynomial.monomial, #[_, _, n]) =>                     -- `monomial k c` ↦ `c * X ^ k`
          let some k := natLit? n | throwError "poly_dvd_cert: non-literal monomial degree {n}"
          pure ((List.replicate k z).toArray.push c)
      | _ => throwError "poly_dvd_cert: cannot parse {e}"
  | (``OfNat.ofNat, #[_, lit, _]) => pure #[← mkAppOptM ``OfNat.ofNat #[some K, some lit, none]]
  | (``Nat.cast, #[_, _, n]) => pure #[← mkAppOptM ``Nat.cast #[some K, none, some n]]
  | (``Int.cast, #[_, _, n]) => pure #[← mkAppOptM ``Int.cast #[some K, none, some n]]
  | _ => throwError "poly_dvd_cert: cannot parse polynomial {e}"

/-- Pseudo-division `d ^ δ • q = p * Q + R` over the coefficient ring (no division): returns the
quotient vector `Q`, where `dp = deg p`, `dq = deg q`, `d = lc p`, `δ = dq - dp + 1`. -/
private def pseudoQuotient (z : Expr) (pc qc : Array Expr) (dp dq : ℕ) (d : Expr) :
    MetaM (Array Expr) := do
  let δ := dq - dp + 1
  let mut Q := (List.replicate δ z).toArray
  let mut R := qc
  for k in [0:δ] do
    let w := dq - k
    let lc := R[w]!
    let shift := w - dp
    Q ← Q.mapM (kMul d)
    Q := Q.set! shift (← kAdd Q[shift]! lc)
    R ← R.mapM (kMul d)
    for i in [0:dp + 1] do
      R := R.set! (i + shift) (← kSub R[i + shift]! (← kMul lc pc[i]!))
  return Q

/-- Prove `p ∣ q` for `p q : Polynomial K` (any field `K`) by searching for the quotient with
`MetaM` pseudo-division and certifying the division-free identity `C (lc p ^ δ) * q = p * Q` with
`ring`, then cancelling the leading-coefficient unit. Axiom-free; never `native_decide`. -/
elab "poly_dvd_cert" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← g.getType)
  let (``Dvd.dvd, #[ty, _, p, q]) := tgt.getAppFnArgs
    | throwError "poly_dvd_cert: goal is not `p ∣ q`"
  let (``Polynomial, #[K, _]) := ty.getAppFnArgs
    | throwError "poly_dvd_cert: not a divisibility of polynomials"
  let z ← mkAppOptM ``OfNat.ofNat #[some K, some (mkRawNatLit 0), none]
  let one ← mkAppOptM ``OfNat.ofNat #[some K, some (mkRawNatLit 1), none]
  let pc := trimZeros (← toCoeffs K z one p)
  let qc := trimZeros (← toCoeffs K z one q)
  if pc.isEmpty then throwError "poly_dvd_cert: divisor is the zero polynomial"
  let dp := pc.size - 1
  let d := pc[dp]!
  -- Build the quotient `Q`. `scale = none` ⇒ a division-free witness `q = p * Q` (monic divisor, or
  -- `deg q < deg p`), which works over *any commutative ring*. `scale = some (lc p ^ δ)` ⇒ the
  -- denominator-cleared identity, needing the leading coefficient to be a unit (a field).
  let (Q, scale) ←
    if qc.isEmpty || qc.size - 1 < dp then
      pure (#[], none)                     -- `deg q < deg p`: quotient `0`, witness `q = p * 0`
    else
      let dq := qc.size - 1
      let Q ← pseudoQuotient z pc qc dp dq d
      if isNatLit 1 d then pure (Q, none)  -- monic: `d ^ δ = 1`, no scaling needed
      else pure (Q, some (← mkAppM ``HPow.hPow #[d, mkNatLit (dq - dp + 1)]))
  -- reflect `Q` back to a `Polynomial K` term `∑ C (Qᵢ) * X ^ i`
  let CHom ← mkAppOptM ``Polynomial.C #[some K, none]
  let xPoly ← mkAppOptM ``Polynomial.X #[some K, none]
  let mut terms : Array Expr := #[]
  for i in [0:Q.size] do
    if isNatLit 0 Q[i]! then continue
    let cc ← mkAppM ``DFunLike.coe #[CHom, Q[i]!]
    let term ← if i == 0 then pure cc
      else mkAppM ``HMul.hMul #[cc, ← mkAppM ``HPow.hPow #[xPoly, mkNatLit i]]
    terms := terms.push term
  let Qexpr ← if terms.isEmpty then mkAppOptM ``OfNat.ofNat #[some ty, some (mkRawNatLit 0), none]
    else terms[1:].foldlM (fun a b => mkAppM ``HAdd.hAdd #[a, b]) terms[0]!
  let Qstx ← Term.exprToSyntax Qexpr
  -- the `ring` check that the reflected witness is correct, after pushing `C` to atoms/numerals;
  -- a failure here means the computed quotient does not check out, i.e. `p` does not divide `q`.
  let runCert : TacticM Unit := do
    try
      evalTactic (← `(tactic| case hcert =>
        set_option linter.unusedSimpArgs false in
          (simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_one, map_zero, map_ofNat,
            map_natCast, map_intCast]; ring)))
    catch _ =>
      throwError "poly_dvd_cert: `{p}` does not divide `{q}` (the certificate identity failed)"
  match scale with
  | none =>
    -- division-free: `p ∣ q` via the witness `⟨Q, (q = p * Q)⟩`
    evalTactic (← `(tactic| refine ⟨$Qstx, ?hcert⟩))
    runCert
  | some scaleExpr =>
    -- denominator-cleared: cancel the unit `C (lc p ^ δ)`, then check `C (lc p ^ δ) * q = p * Q`
    let scaleStx ← Term.exprToSyntax scaleExpr
    let Kstx ← Term.exprToSyntax K
    evalTactic (← `(tactic|
      refine (?hunit : IsUnit (Polynomial.C $scaleStx : Polynomial $Kstx)).dvd_mul_left.mp
        ⟨$Qstx, ?hcert⟩))
    runCert
    -- discharge `IsUnit (C (lc ^ δ))`: reduce to `IsUnit lc`, then try units valid over any
    -- comm ring
    -- (a hypothesis, `±1`) and finally the field route `lc ≠ 0`; leave a clean residual otherwise.
    evalTactic (← `(tactic| case hunit =>
      apply Polynomial.isUnit_C.mpr
      apply IsUnit.pow
      first
        | assumption
        | exact isUnit_one
        | exact isUnit_one.neg
        | (rw [isUnit_iff_ne_zero]
           first | assumption | (apply pow_ne_zero <;> assumption) | norm_num | skip)
        | skip))

attribute [nolint defsWithUnderscore] tacticPoly_dvd_cert

end Polynomial.DvdCert
