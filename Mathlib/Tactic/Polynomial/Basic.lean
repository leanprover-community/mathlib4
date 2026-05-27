/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Polynomial.Core

/-!
# Polynomial
An extensible tactic for proving equality of polynomial expressions implemented using `algebra`.
To add support for a new polynomial-like type, one needs to do three things:
* Implement a polynomial extension that lets `polynomial` infer the base ring from the algebraic
  type. For example:
```
@[polynomial_infer_base]
def polynomialInferBase : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure
```
* Tag any preprocessing lemmas with @[polynomial_pre]. This would include a lemma saying that
`C = algebraMap _ _` so that `algebra` knows how to normalize it.
* Tag any postprocessing lemmas with @[polynomial_post], so that `polynomial_nf` produces a pretty
expression.
-/

open Lean Mathlib.Tactic Mathlib.Tactic.Algebra Parser.Tactic Elab Meta Qq

public meta section

namespace Mathlib.Tactic.Polynomial

/-- Infer base ring for `Polynomial R` -/
@[polynomial_infer_base]
def polynomialInferBase : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure

section Lemmas

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

attribute [polynomial_post] mul_one Algebra.smul_def Polynomial.algebraMap_eq

@[polynomial_pre]
theorem monomial_eq_smul (a : R) (n : ℕ) : Polynomial.monomial n a = a • (.X ^ n) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.smul_eq_C_mul]

-- polynomial_pre contains a lemma sending C -> algebraMap, so C is not simp normal form.
@[polynomial_pre]
theorem map_algebraMap (r : R) :
    Polynomial.map (algebraMap R A) (algebraMap R (Polynomial R) r) =
    algebraMap A (Polynomial A) (algebraMap R A r) := by
  simp

end Lemmas

open Mathlib.Meta AtomM

attribute [polynomial_pre] Polynomial.C_eq_algebraMap
  Polynomial.monomial_eq_smul Polynomial.map_add Polynomial.map_mul Polynomial.map_pow
  Polynomial.map_X Polynomial.map_natCast Polynomial.map_intCast

/- TODO: we don't currently have a good way to normalize monomials of MvPolynomials. These are
indexed by finsupps, making it difficult to turn into the appropriate normal form. -/
/-- Run the `polynomial_pre` simpset to turn nonstandard spellings of `algebraMap` such as
`Polynomial.C` into `algebraMap` -/
def preprocess (mvarId : MVarId) : MetaM MVarId := do
  let preThms ← polynomialPreExt.getTheorems
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[preThms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in polynomial tactic: preprocessing should not close goals"
  return r

open Tactic

/-- `polynomial` solves equalities of `Polynomial`s and similar types.

Given a goal which is an equality in `Polynomial R` with a commutative ring `R`, `polynomial`
expands out the brackets on both sides of the equation and combines the coefficients of equal
monomials. It then closes the goal if both sides contain the same terms and fails otherwise.
Examples:

```
example (a : ℚ) : (X + C a) * (X - C a) = X^2 + C (a^2) := by polynomial
```

The `polynomial` tactic can be extended to work with algebras other than `Polynomial`, as long as
the base ring can be inferred from the structure of the type.
-/
elab (name := polynomial) "polynomial" tk:"!"? : tactic =>
  withMainContext do
    let g ← getMainGoal
    let some (α, _, _) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "polynomial failed: not an equality"
    let mut β : Expr := default
    try
      β ← Polynomial.inferBase α
    catch _ =>
      throwError "polynomial failed: not an equality of (mv)polynomials"
    let g ← Algebra.preprocess (← Polynomial.preprocess g)
    AtomM.run (if tk.isSome then .default else .reducible)
      (Algebra.proveEq (some (← getLevelQ' β)) g)

/-- A cleanup routine, which simplifies normalized expressions to a more human-friendly format.
This is the `algebra_nf` cleanup routine with a little extra work to turn scalar multiplication
into `(MV)Polynomial.C` -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let r ← cleanupSMul cfg r
    let thms : SimpTheorems ← polynomialPostExt.getTheorems
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Normalize a polynomial expression into standard form. Used by `polynomial_nf`. -/
def evalExprPoly (e : Expr) : AtomM Simp.Result := do
  let ⟨_, α, e⟩ ← inferTypeQ e
  let mut R : Expr := default
  try R ← inferBase α
  catch _ => throwError "not a polynomial"
  let ⟨_, R'⟩ ← getLevelQ' R
  evalExpr R' e

/-- Simplification tactic for polynomials over commutative (semi)rings, which rewrites all
polynomial expressions into normal form.

See also:
* `polynomial` for proving equality of polynomials without producing side goals.
* `match_coefficients` for creating side goals equating matching coefficients. -/
elab (name := polynomialNF) "polynomial_nf" tk:"!"? loc:(location)?  : tactic => withMainContext do
  liftMetaTactic' Polynomial.preprocess
  liftMetaTactic' Algebra.preprocess
  let mut cfg := {}
  -- if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) (evalExprPoly) (cleanup cfg)
  transformAtLocation (m ·) "polynomial_nf" loc cfg.ifUnchanged false

end Mathlib.Tactic.Polynomial

end
