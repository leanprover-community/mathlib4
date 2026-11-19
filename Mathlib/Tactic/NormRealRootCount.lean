/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.NormNum.Core
public meta import Mathlib.Tactic.Polynomial.Basic
public meta import Mathlib.Tactic.RealRootCount.Core
public meta import Mathlib.Util.Qq
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.RealRootCount.Reflection

/-!
# `eval_real_root_count`

The `norm_real_root_count` simproc rewrites `Fintype.card (f.rootSet ℝ)` to the number of distinct
real roots of `f`, for an explicit polynomial `f` over `ℤ`, `ℚ` or `ℝ` with rational coefficients.

The `eval_real_root_count` tactic evaluates the root counts in the goal with this simproc.

## Implementation notes

To count the roots of `f`, the tactic:

1. reads the coefficients of `f` (`coeffsOf`)
2. computes their Sturm sequence, with a certificate for it, in untrusted code
   (`SturmCertificate.fromCoeffList`)
3. proves that the certificate is for `f`, with the `polynomial` tactic (`proveEq`)
4. has the kernel check the certificate and count the roots, by evaluating `realRootCount?`
-/

meta section

namespace Mathlib.Tactic.RealRootCount

open Lean Meta Elab Qq

deriving instance ToExpr for SturmStep
deriving instance ToExpr for SturmCertificate

/-- The value of a closed rational numeral `e`, by `norm_num`. -/
def ratOf (e : Expr) : MetaM ℚ := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let some q := (← observing? (Mathlib.Meta.NormNum.derive (u := u) (α := α) e)).bind (·.toRat)
    | throwError "cannot read{indentExpr e}\nas a rational number"
  return q

/-- Parse the coefficients of a polynomial expression constant term first. -/
partial def coeffsOf (e : Expr) : MetaM (List ℚ) := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ p q => return coeffAddSmul 1 (← coeffsOf p) (← coeffsOf q)
  | HSub.hSub _ _ _ _ p q =>
    return coeffAddSmul 1 (← coeffsOf p) (coeffAddSmul (-1) (← coeffsOf q) [])
  | Neg.neg _ _ p => return coeffAddSmul (-1) (← coeffsOf p) []
  | HMul.hMul _ _ _ _ p q => return coeffMul (← coeffsOf p) (← coeffsOf q)
  | HPow.hPow _ _ _ _ p k =>
    return (List.replicate (← ratOf k).num.toNat (← coeffsOf p)).foldl coeffMul [1]
  | Polynomial.X _ _ => return [0, 1]
  | DFunLike.coe _ _ _ _ f c => return [← ratOf (if f.isAppOf ``Polynomial.C then c else e)]
  | _ => return [← ratOf e]

/-- Prove the goal `k * f = (ofCoeffList s).map (Int.castRingHom R)` for an explicit polynomial `f`
over `R` and the coefficient list `s` of `k * f`. -/
def proveEq (goal : Q(Prop)) : MetaM Expr := do
  let g ← mkFreshExprMVar goal
  try
    let thms ← [``map_ofCoeffList_cons, ``map_ofCoeffList_nil].foldlM (·.addConst ·)
      (← NormCast.pushCastExt.getTheorems)
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    if let (some g', _) ← simpTarget g.mvarId! ctx then AtomM.run .reducible (Polynomial.proveEq g')
  catch _ => throwError "could not match the polynomial with its coefficients"
  instantiateMVars g

/-- Compute `k > 0` and the Sturm certificate `d` of `k • f`, for an explicit nonzero polynomial `f`
over `R`, and construct a proof that `d.s` is the coefficient list of `k • f`. -/
def certificateOf {u : Level} {R : Q(Type u)} (_ : Q(CommRing $R)) (f : Q(Polynomial $R)) :
    MetaM (SturmCertificate × ((kE : Q(ℕ)) × (dE : Q(SturmCertificate)) × Q(($kE : Polynomial $R) *
      $f = (Polynomial.ofCoeffList ($dE).s).map (Int.castRingHom $R)))) := do
  let p ← try coeffsOf f catch _ => throwError
    "could not parse{indentExpr f}\nas an explicit polynomial with rational coefficients"
  -- the coefficients `p` of `f`, without trailing zeros
  let p := (p.reverse.dropWhile (· == 0)).reverse
  if p.isEmpty then throwError "expected a nonzero polynomial"
  let (k, d) := SturmCertificate.fromCoeffList p
  have kE : Q(ℕ) := toExpr k
  have sE : Q(List ℤ) := toExpr d.s
  return ⟨d, kE, toExpr d, ← proveEq
    q(($kE : Polynomial $R) * $f = (Polynomial.ofCoeffList $sE).map (Int.castRingHom $R))⟩

/-- For an input expression `e = Fintype.card (f.rootSet ℝ)` compute the number `n` of distinct real
roots of `f` and construct a proof of `e = n`. -/
def proveCardRootSet (e : Expr) : MetaM (Q(ℕ) × Expr) := do
  let err := m!"expected `Fintype.card (f.rootSet ℝ)`"
  let_expr Fintype.card α inst := e | throwError err
  let_expr Set.Elem _ s := α | throwError err
  let_expr Polynomial.rootSet R iR f S _ _ iA := s | throwError err
  unless ← isDefEq S q(ℝ) do throwError err
  let ⟨_, R⟩ ← getLevelQ' R
  have iR : Q(CommRing $R) := iR
  have : Q(Algebra $R ℝ) := iA
  have f : Q(Polynomial $R) := f
  have : Q(Fintype (Polynomial.rootSet $f ℝ)) := inst
  let ⟨d, _, dE, hf⟩ ← certificateOf iR f
  let some n := realRootCount? d
    | throwError "the computed Sturm sequence is invalid"
  have nE : Q(ℕ) := toExpr n
  -- the kernel checks `h` by evaluating `realRootCount?`
  have h : Q(realRootCount? $dE = some $nE) := (q(Eq.refl (some $nE)) : Expr)
  return (nE, q(card_rootSet_of_realRootCount? $hf $h))

end Mathlib.Tactic.RealRootCount

end

public meta section

open Lean Meta Mathlib.Tactic.RealRootCount

initialize registerTraceClass `Tactic.evalRealRootCount

/-- The `norm_real_root_count` simproc evaluates `Fintype.card (f.rootSet ℝ)`, the number of
distinct real roots of an explicit polynomial `f` over `ℤ`, `ℚ` or `ℝ` with rational coefficients.
Terms that it cannot evaluate are skipped. -/
simproc_decl norm_real_root_count (Fintype.card (Polynomial.rootSet _ ℝ)) := fun e => do
  try
    let (n, pf) ← proveCardRootSet e
    return .done { expr := n, proof? := some pf }
  catch ex =>
    trace[Tactic.evalRealRootCount] "{ex.toMessageData}"
    return .continue

/--
`eval_real_root_count` evaluates `Fintype.card (f.rootSet ℝ)`, the number of distinct real roots of
an explicit polynomial `f` over `ℤ`, `ℚ` or `ℝ` with rational coefficients.

Examples:

```lean
example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by
  eval_real_root_count

-- a repeated root is counted once
example : Fintype.card (((X - 1) ^ 2 * (X + 2) : ℤ[X]).rootSet ℝ) = 2 := by
  eval_real_root_count
```

Terms skipped can be viewed by using `set_option trace.Tactic.evalRealRootCount true`.
-/
elab (name := evalRealRootCount) "eval_real_root_count" : tactic => do
  try
    Elab.Tactic.evalTactic (← `(tactic| simp only [norm_real_root_count]))
  catch _ =>
    throwError "`eval_real_root_count` made no progress.\n\
      Additional information may be available using \
      `set_option trace.Tactic.evalRealRootCount true`."
  Elab.Tactic.evalTactic (← `(tactic| try lia))
