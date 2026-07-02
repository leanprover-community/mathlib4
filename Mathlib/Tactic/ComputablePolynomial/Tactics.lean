/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.Reflect

/-!
# Axiom-free evaluation tactic for univariate `Polynomial R`

Adds, all **axiom-free** (kernel `decide +kernel`, no `native_decide`):
* `poly_eval` — proves `Polynomial.eval a p = v` (hence `IsRoot`) by evaluating on a
  kernel-reducible coefficient list;
* `poly_dvd` — proves `p ∣ q` by **kernel-reducible long division** (`SparsePoly.Kernel.divMod`,
  fuel-structural so the kernel reduces it), deciding the remainder is `0`. Cleanest over a field.
-/

open Lean Elab Tactic Meta

namespace SparsePoly

variable {R : Type} [CommRing R] [DecidableEq R]

/-! ### Computable univariate evaluation -/

/-- Evaluate a coefficient list at `x`: `∑ (i,a), a·xⁱ`. -/
def evalCore (x : R) : List (ℕ × R) → R
  | [] => 0
  | (i, a) :: t => a * x ^ i + evalCore x t

/-- Evaluate a polynomial at `x`. -/
def eval (x : R) (p : SparsePoly R) : R := evalCore x p.coeffs

omit [DecidableEq R] in
theorem evalCore_eq (x : R) : ∀ l, evalCore x l = Polynomial.eval x (toPolyCore l)
  | [] => by simp [evalCore, toPolyCore]
  | (i, a) :: t => by
    simp only [evalCore, toPolyCore, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, evalCore_eq x t]

omit [DecidableEq R] in
/-- **Correctness of evaluation**: agrees with Mathlib's `Polynomial.eval`. -/
theorem eval_eq (x : R) (p : SparsePoly R) : eval x p = Polynomial.eval x (toPoly p) :=
  evalCore_eq x p.coeffs

omit [DecidableEq R] in
/-- Soundness for the **axiom-free** `poly_eval`: evaluate on a kernel-reducible coefficient list
`l` (with `toPolyCore l = p`) directly via `evalCore`. -/
theorem eval_of_core {p : Polynomial R} (l : List (ℕ × R)) (a v : R)
    (h1 : toPolyCore l = p) (h2 : evalCore a l = v) : Polynomial.eval a p = v := by
  rw [← h1, ← evalCore_eq]; exact h2

end SparsePoly

/-! ### The tactic -/

/-- Reify `e : Polynomial R` to a **kernel-reducible** coefficient list with a proof
`toPolyCore _ = e` (reuses the kernel reify/bridge from `Reflect`). -/
def SparsePoly.Reflect.reflectKWithProof (R e : Expr) : MetaM (Expr × Expr) := do
  let l ← SparsePoly.Kernel.reifyK R e
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``SparsePoly.toPolyCore #[l]) e)
  let (res, _) ← simpGoal m.mvarId! (← SparsePoly.Kernel.bridgeSimpK)
  if let some (_, m2) := res then m2.refl
  return (l, ← instantiateMVars m)

/-- Prove `Polynomial.eval a p = v` (or `IsRoot p a`, i.e. `… = 0`) by computing the value, **axiom-
free**: it evaluates on a kernel-reducible coefficient list with kernel `decide +kernel`. -/
elab "poly_eval" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, v) := (← whnfR (← g.getType)).eq?
    | throwError "poly_eval: goal is not `Polynomial.eval a p = v`"
  let (``Polynomial.eval, #[R, _, a, p]) := lhs.getAppFnArgs
    | throwError "poly_eval: goal LHS is not `Polynomial.eval a p`"
  let (l, hl) ← SparsePoly.Reflect.reflectKWithProof R p
  let pf ← mkAppM ``SparsePoly.eval_of_core #[l, a, v, hl]
  let coreTy := (← inferType pf).bindingDomain!
  let m ← mkFreshExprSyntheticOpaqueMVar coreTy
  g.assign (.app pf m)
  replaceMainGoal [m.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- Prove `p ∣ q` for `p q : Polynomial R` by kernel-reducible long division (`divMod`): reflect
both sides, then `decide +kernel` that the remainder is `0` — **axiom-free**. -/
elab "poly_dvd" : tactic => withMainContext do
  let g ← getMainGoal
  let (``Dvd.dvd, #[ty, _, p, q]) := (← whnfR (← g.getType)).getAppFnArgs
    | throwError "poly_dvd: goal is not `p ∣ q`"
  let (``Polynomial, #[R, _]) := ty.getAppFnArgs
    | throwError "poly_dvd: not a divisibility of Polynomials"
  let (l_p, h_p) ← SparsePoly.Reflect.reflectKWithProof R p
  let (l_q, h_q) ← SparsePoly.Reflect.reflectKWithProof R q
  let pf ← mkAppM ``SparsePoly.Kernel.dvd_of_divMod #[l_p, l_q, h_p, h_q]
  let coreTy := (← inferType pf).bindingDomain!
  let m ← mkFreshExprSyntheticOpaqueMVar coreTy
  g.assign (.app pf m)
  replaceMainGoal [m.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

attribute [nolint defsWithUnderscore] tacticPoly_eval tacticPoly_dvd
