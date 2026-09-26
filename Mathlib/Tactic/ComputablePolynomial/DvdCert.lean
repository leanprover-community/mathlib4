/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Util.Qq

/-!
# `poly_dvd_cert`: divisibility of `Polynomial K` by **symbolic certificate**

A `polyrith`/`linarith`-style tactic: search for the quotient uncertified, then check it certified.

For `p q : Polynomial K` over any field `K` (coefficients may be concrete *or* symbolic), it:

1. parses `p`, `q` into dense vectors of coefficient **expressions** (elements of `K`);
2. runs **pseudo-division as plain compiled Lean**, like `norm_num`'s arithmetic, so it
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
over any commutative ring, and over a commutative semiring with subtraction such as `ℕ` (where the
certificate is still checked by `ring`, so a wrong quotient from truncated subtraction is rejected
rather than believed).
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace Polynomial.DvdCert

variable {u : Level} {K : Q(Type u)}

/-! ### Smart constructors for coefficient (`K`-valued) expressions, with `0`/`1` peephole

`cs`, `sub` and `neg` are the coefficient ring's instances, resolved once per `poly_dvd_cert`
call so that nothing is searched for inside the pseudo-division loops. `neg` is `none` over a
semiring that has no negation, such as `ℕ`. -/

private def kMul (cs : Q(CommSemiring $K)) (a b : Q($K)) : Q($K) :=
  if a.nat? == some 0 then a
  else if b.nat? == some 0 then b
  else if a.nat? == some 1 then b
  else if b.nat? == some 1 then a
  else q($a * $b)

private def kAdd (cs : Q(CommSemiring $K)) (a b : Q($K)) : Q($K) :=
  if a.nat? == some 0 then b
  else if b.nat? == some 0 then a
  else q($a + $b)

private def kSub (sub : Q(Sub $K)) (neg : Option Q(Neg $K)) (a b : Q($K)) : Q($K) :=
  if b.nat? == some 0 then a
  else if a.nat? == some 0 then
    match neg with
    | some _nK => q(-$b)
    | none => q($a - $b)
  else q($a - $b)

private def kNeg (nK : Q(Neg $K)) (a : Q($K)) : Q($K) :=
  if a.nat? == some 0 then a
  else q(-$a)

/-! ### Dense polynomial arithmetic over coefficient expressions
(index `i` ↦ coefficient of `Xⁱ`) -/

/-- Pointwise combine, padding the shorter vector with the zero expression `z`. -/
private def kZip (op : Q($K) → Q($K) → Q($K)) (z : Q($K)) (a b : Array Q($K)) :
    Array Q($K) := Id.run do
  let n := max a.size b.size
  let mut r := (List.replicate n z).toArray
  for i in [0:n] do
    r := r.set! i (op (a.getD i z) (b.getD i z))
  return r

private def kConv (cs : Q(CommSemiring $K)) (a b : Array Q($K)) : Array Q($K) := Id.run do
  if a.isEmpty || b.isEmpty then return #[]
  let mut r := (List.replicate (a.size + b.size - 1) (q(0) : Q($K))).toArray
  for i in [0:a.size] do
    for j in [0:b.size] do
      r := r.set! (i + j) (kAdd cs r[i + j]! (kMul cs a[i]! b[j]!))
  return r

private def kPow (cs : Q(CommSemiring $K)) (a : Array Q($K)) : ℕ → Array Q($K)
  | 0 => #[q(1)]
  | n + 1 => kConv cs a (kPow cs a n)

/-- Drop trailing zero coefficients. -/
private partial def trimZeros (a : Array Q($K)) : Array Q($K) :=
  if 0 < a.size then
    if a[a.size - 1]!.nat? == some 0 then trimZeros a.pop else a
  else a

/-- Parse a `Polynomial K` expression into a dense vector of coefficient expressions in `K`. -/
private partial def toCoeffs (cs : Q(CommSemiring $K)) (sub : Q(Sub $K))
    (neg : Option Q(Neg $K)) (e : Expr) : MetaM (Array Q($K)) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return kZip (kAdd cs) q(0) (← toCoeffs cs sub neg a) (← toCoeffs cs sub neg b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return kZip (kSub sub neg) q(0) (← toCoeffs cs sub neg a) (← toCoeffs cs sub neg b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return kConv cs (← toCoeffs cs sub neg a) (← toCoeffs cs sub neg b)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some n := k.nat? | throwError "poly_dvd_cert: non-literal exponent {k}"
      return kPow cs (← toCoeffs cs sub neg a) n
  | (``Neg.neg, #[_, _, a]) =>
      let some nK := neg | throwError "poly_dvd_cert: `{K}` has no negation"
      return (← toCoeffs cs sub neg a).map (kNeg nK)
  | (``Polynomial.X, _) => pure #[q(0), q(1)]
  | (``DFunLike.coe, #[_, _, _, _, f, c]) =>
      match f.getAppFnArgs with
      | (``Polynomial.C, _) => pure #[c]                            -- `C c`  ↦  constant `c`
      | (``algebraMap, _) => pure #[c]                              -- `algebraMap _ _ c`  ↦  `c`
      | (``Polynomial.monomial, #[_, _, n]) =>                     -- `monomial k c` ↦ `c * X ^ k`
          let some k := n.nat? | throwError "poly_dvd_cert: non-literal monomial degree {n}"
          pure ((List.replicate k (q(0) : Q($K))).toArray.push c)
      | _ => throwError "poly_dvd_cert: cannot parse {e}"
  | (``OfNat.ofNat, #[_, lit, _]) => pure #[← mkAppOptM ``OfNat.ofNat #[some K, some lit, none]]
  | (``Nat.cast, #[_, _, n]) => pure #[← mkAppOptM ``Nat.cast #[some K, none, some n]]
  | (``Int.cast, #[_, _, n]) => pure #[← mkAppOptM ``Int.cast #[some K, none, some n]]
  | _ => throwError "poly_dvd_cert: cannot parse polynomial {e}"

/-- Pseudo-division `lc p ^ δ • q = p * Q + R` over the coefficient ring (no division): returns
the quotient vector `Q`, where `δ = deg q - deg p + 1`. Expects `pc`, `qc` trimmed and `pc`
nonempty. -/
private def pseudoQuotient (cs : Q(CommSemiring $K)) (sub : Q(Sub $K))
    (neg : Option Q(Neg $K)) (pc qc : Array Q($K)) : Array Q($K) := Id.run do
  let dp := pc.size - 1
  let dq := qc.size - 1
  let d := pc[dp]!
  let δ := dq - dp + 1
  let mut quot := (List.replicate δ (q(0) : Q($K))).toArray
  let mut R := qc
  for k in [0:δ] do
    let w := dq - k
    let lc := R[w]!
    let shift := w - dp
    quot := quot.map (kMul cs d)
    quot := quot.set! shift (kAdd cs quot[shift]! lc)
    R := R.map (kMul cs d)
    for i in [0:dp + 1] do
      R := R.set! (i + shift) (kSub sub neg R[i + shift]! (kMul cs lc pc[i]!))
  return quot

/-- Prove `p ∣ q` for `p q : Polynomial K` (any field `K`) by searching for the quotient with
pseudo-division and certifying the division-free identity `C (lc p ^ δ) * q = p * Q` with
`ring`, then cancelling the leading-coefficient unit. Axiom-free; never `native_decide`. -/
elab "poly_dvd_cert" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← g.getType)
  let (``Dvd.dvd, #[ty, _, p, q]) := tgt.getAppFnArgs
    | throwError "poly_dvd_cert: goal is not `p ∣ q`"
  let (``Polynomial, #[KE, _]) := ty.getAppFnArgs
    | throwError "poly_dvd_cert: not a divisibility of polynomials"
  let .sort (.succ u) ← whnf (← inferType KE) | throwError "poly_dvd_cert: `{KE}` is not a type"
  have K : Q(Type u) := KE
  have cs : Q(CommSemiring $K) := ← synthInstanceQ q(CommSemiring $K)
  let some sub ← synthInstanceQ? q(Sub $K)
    | throwError "poly_dvd_cert: `{K}` has no subtraction, so pseudo-division is unavailable"
  let neg ← synthInstanceQ? q(Neg $K)
  let pc := trimZeros (← toCoeffs cs sub neg p)
  let qc := trimZeros (← toCoeffs cs sub neg q)
  if pc.isEmpty then throwError "poly_dvd_cert: divisor is the zero polynomial"
  let dp := pc.size - 1
  let d := pc[dp]!
  -- Build the quotient. `scale = none` ⇒ a division-free witness `q = p * Q` (monic divisor, or
  -- `deg q < deg p`), which works over *any commutative ring*. `scale = some (lc p ^ δ)` ⇒ the
  -- denominator-cleared identity, needing the leading coefficient to be a unit (a field).
  let (quot, scale) : Array Q($K) × Option Q($K) :=
    if qc.isEmpty || qc.size - 1 < dp then
      (#[], none)                            -- `deg q < deg p`: quotient `0`, witness `q = p * 0`
    else
      let dq := qc.size - 1
      let quot := pseudoQuotient cs sub neg pc qc
      if d.nat? == some 1 then (quot, none)      -- monic: `d ^ δ = 1`, no scaling needed
      else
        have δ : Q(ℕ) := mkNatLit (dq - dp + 1)
        (quot, some q($d ^ $δ))
  -- reflect the quotient back to a `Polynomial K` term `∑ C (Qᵢ) * X ^ i`
  let mut terms : Array Q(Polynomial $K) := #[]
  for i in [0:quot.size] do
    if quot[i]!.nat? == some 0 then continue
    have c : Q($K) := quot[i]!
    terms := terms.push <| if i == 0 then q(Polynomial.C ($c)) else
      have n : Q(ℕ) := mkNatLit i
      q(Polynomial.C ($c) * Polynomial.X ^ $n)
  let Qexpr : Q(Polynomial $K) :=
    if terms.isEmpty then q(0) else terms[1:].foldl (fun a b => q($a + $b)) terms[0]!
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
