/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.RealRootCount.Lemmas
public import Mathlib.Tactic.Polynomial.Basic
public meta import Mathlib.Tactic.NormNum.Core
public meta import Mathlib.Tactic.Polynomial.Basic
public meta import Mathlib.Tactic.RealRootCount.Lemmas
public meta import Mathlib.Util.Qq

/-!
# `real_root_count`

The `norm_root_count` simproc rewrites `Fintype.card (f.rootSet ℝ)` to the number of distinct real
roots of an explicit polynomial `f` over `ℤ`, `ℚ` or `ℝ` with rational coefficients, and the
`real_root_count` tactic proves `Fintype.card (f.rootSet ℝ) = n`.
-/

public meta section

namespace Mathlib.Tactic.RealRootCount

open Lean Meta Elab Term Qq CoeffList

/-- The value of a closed numeral expression, by `norm_num`. -/
def ratOf (e : Expr) : MetaM ℚ := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let some q := (← Mathlib.Meta.NormNum.derive (u := u) (α := α) e).toRat |
    throwError "real_root_count: expected a rational number, got{indentExpr e}"
  return q

/-- `(c, k)` for a monomial `c * X ^ k` of the normal form produced by `polynomial_nf`. -/
def monomialOf (t : Expr) : MetaM (ℚ × Nat) := do
  let deg? (x : Expr) : MetaM (Option Nat) := do
    match_expr x with
    | Polynomial.X _ _ => return some 1
    | HPow.hPow _ _ _ _ b k =>
      let_expr Polynomial.X _ _ := b | return none
      return some (← ratOf k).num.toNat
    | _ => return none
  let coeff (c : Expr) : MetaM ℚ := do
    let_expr DFunLike.coe _ _ _ _ f a := c | ratOf c
    let_expr Polynomial.C _ _ := f | ratOf c
    ratOf a
  let t := t.consumeMData
  match_expr t with
  | HMul.hMul _ _ _ _ c x => if let some k ← deg? x then return (← coeff c, k)
  | _ => pure ()
  if let some k ← deg? t then return (1, k)
  return (← coeff t, 0)

/-- The summands of a sum. -/
partial def summands (e : Expr) : List Expr :=
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => summands a ++ summands b
  | _ => [e]

/-- Parse a polynomial expression into its list of coefficients using `Polynomial` normal form. -/
def parsePoly (e : Expr) : MetaM (List ℚ) := do
  let s ← IO.mkRef {}
  let r ← AtomM.recurse s ({} : RingNF.Config).toConfig true Polynomial.evalExprPoly
    (Polynomial.cleanup {}) e
  let err (t : Expr) : MetaM Unit :=
    throwError "real_root_count: cannot read{indentExpr t}\nin a polynomial with rational \
      coefficients"
  for a in (← s.get).atoms do
    unless a.isAppOf ``Polynomial.X do err a
  let mut coeffs : Array ℚ := #[]
  for t in summands r.expr do
    let (c, k) ← try monomialOf t catch _ => do err t; pure (0, 0)
    if coeffs.size ≤ k then coeffs := coeffs ++ Array.replicate (k + 1 - coeffs.size) 0
    coeffs := coeffs.set! k (coeffs[k]! + c)
  return trim coeffs.toList

/-- Division with remainder; `divMod p [] = ([], p)`, as for `EuclideanDomain` on `K[X]`. -/
def divMod (p q : List ℚ) : List ℚ × List ℚ := Id.run do
  let q := trim q
  if q.isEmpty then return ([], trim p)
  let mut r := trim p
  let mut quo : List ℚ := []
  for _ in [0:p.length + 1] do
    if r.length < q.length then break
    let m := List.replicate (r.length - q.length) 0 ++ [lead r / lead q]
    quo := add quo m
    r := trim (add r (neg (mul m q)))
  return (trim quo, r)

/-- The quotients of the Sturm sequence of `l` and its derivative. -/
def sturm (l : List ℚ) : List (List ℚ) := Id.run do
  let mut s := l
  let mut t := derivative l
  let mut ds := #[]
  if t.isEmpty then return []
  for _ in [0:l.length + 2] do
    let (d, r) := divMod (neg s) t
    ds := ds.push d
    if r.isEmpty then break
    s := t
    t := r
  return ds.toList

/-- A power of two `B` with `|cᵢ| ≤ (B - 1) * |cₙ|` for every coefficient: Cauchy's bound. -/
def rootBound (l : List ℚ) : ℚ := Id.run do
  let c := |lead l|
  let m := l.dropLast.foldl (fun m x => max m (|x| / c)) 0
  let mut b : ℚ := 1
  while b < 1 + m do b := 2 * b
  return b

/-! ### Building the proof -/

/-- Simp lemmas turning `f.map (algebraMap R ℝ)` and `toReal l` into polynomial expressions. -/
def mapLemmas : List Name :=
  [``Polynomial.ofCoeffList_cons, ``Polynomial.ofCoeffList_nil, ``Polynomial.map_add,
    ``Polynomial.map_sub, ``Polynomial.map_neg, ``Polynomial.map_mul, ``Polynomial.map_pow,
    ``Polynomial.map_X, ``Polynomial.map_C, ``Polynomial.map_ofNat, ``Polynomial.map_one,
    ``Polynomial.map_zero, ``Polynomial.map_natCast, ``Polynomial.map_intCast,
    ``Algebra.algebraMap_self, ``Polynomial.map_id, ``eq_ratCast, ``eq_intCast]

/-- A proof of `a = b` for polynomial expressions: both sides are simplified with `mapLemmas` and
then put in normal form by the `polynomial` normaliser. -/
def provePolyEq (a b : Expr) : MetaM Expr := do
  let thms ← mapLemmas.foldlM (·.addConst ·) (← ({} : SimpTheorems).addDeclToUnfold ``toReal)
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let methods := Simp.mkDefaultMethodsCore {}
  let (ra, _) ← Simp.main a ctx (methods := methods)
  let (rb, _) ← Simp.main b ctx (methods := methods)
  AtomM.run .reducible do
    let ra ← ra.mkEqTrans (← Polynomial.evalExprPoly ra.expr)
    let rb ← rb.mkEqTrans (← Polynomial.evalExprPoly rb.expr)
    unless ← isDefEq ra.expr rb.expr do
      throwError "real_root_count: could not match the polynomial with its coefficients"
    mkEqTrans (← ra.getProof) (← mkEqSymm (← rb.getProof))

/-- For `e = Fintype.card (f.rootSet ℝ)`, the number `n` of distinct real roots of `f` and a proof
of `e = n`. -/
def proveCardRootSet (e : Expr) : MetaM (Q(ℕ) × Expr) := do
  let err := m!"real_root_count: expected `Fintype.card (f.rootSet ℝ)`"
  let_expr Fintype.card α _ := e | throwError err
  let_expr Set.Elem _ s := α | throwError err
  let_expr Polynomial.rootSet R _ f S _ _ inst := s | throwError err
  unless ← isDefEq S q(ℝ) do throwError err
  let l ← parsePoly f
  if l.isEmpty then throwError "real_root_count: expected a nonzero polynomial"
  let ds := sturm l
  let b := rootBound l
  let L := chain l (derivative l) ds
  let n := variations L (-b) - variations L b
  unless checkSturm l (derivative l) ds do
    throwError "real_root_count: the computed Sturm sequence does not check"
  unless checkBound l b do throwError "real_root_count: the computed root bound does not check"
  have lE : Q(List ℚ) := toExpr l
  have dsE : Q(List (List ℚ)) := toExpr ds
  have bE : Q(ℚ) := toExpr b
  have nE : Q(ℕ) := mkNatLit n
  -- one kernel check per field of the certificate
  let h₁ ← mkDecideProofQ q(checkSturm $lE (CoeffList.derivative $lE) $dsE = true)
  let h₂ ← mkDecideProofQ q((0 : ℚ) < $bE)
  let h₃ ← mkDecideProofQ q(checkBound $lE $bE = true)
  let h₄ ← mkDecideProofQ q(variations (chain $lE (CoeffList.derivative $lE) $dsE) (-$bE) =
    variations (chain $lE (CoeffList.derivative $lE) $dsE) $bE + $nE)
  have cert : Q(Polynomial.RootCountCert (toReal $lE)
      (List.map toReal (chain $lE (CoeffList.derivative $lE) $dsE)) ($bE : ℝ) $nE) :=
    q(⟨sturmSeq_of_check $h₁, Rat.cast_pos.mpr $h₂, abs_lt_of_checkBound $h₃,
      variations_of_check $h₄⟩)
  let φ ← mkAppOptM ``algebraMap #[R, q(ℝ), none, none, inst]
  let hf ← provePolyEq (← mkAppM ``Polynomial.map #[φ, f]) q(toReal $lE)
  return (nE, ← mkAppM ``Polynomial.RootCountCert.card_rootSet #[hf, cert])

end Mathlib.Tactic.RealRootCount

open Lean Meta Mathlib.Tactic.RealRootCount

/-- `norm_root_count` rewrites `Fintype.card (f.rootSet ℝ)` to the number of distinct real roots of
an explicit polynomial `f` with rational coefficients. -/
simproc_decl norm_root_count (Fintype.card _) := fun e => do
  try
    let (n, pf) ← proveCardRootSet e
    return .done { expr := n, proof? := some pf }
  catch _ => return .continue

/-- `real_root_count` proves `Fintype.card (f.rootSet ℝ) = n` for an explicit polynomial `f`
with rational coefficients, by computing its Sturm sequence and having the kernel check it. The
count is of distinct real roots. -/
elab (name := realRootCount) "real_root_count" : tactic =>
  Elab.Tactic.liftMetaFinishingTactic fun goal => do
    let target ← instantiateMVars (← whnfR (← goal.getType))
    let_expr Eq _ lhs rhs := target |
      throwError "real_root_count: expected a goal `Fintype.card (f.rootSet ℝ) = n`"
    let (n, pf) ← proveCardRootSet lhs
    unless ← isDefEq n rhs do
      throwError "real_root_count: the polynomial has {n} distinct real roots, not {rhs}"
    goal.assign pf
