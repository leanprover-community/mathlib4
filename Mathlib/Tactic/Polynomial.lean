/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Polynomial.Core
import Mathlib.Tactic.Algebra

/-!
# Polynomial

An extensible tactic for proving equality of polynomial expressions implemented using `algebra`.

To add support for a new polynomial-like type, one needs to do three things:

* Implment a polynomial extension that lets `polynomial` infer the base ring from the algebraic
  type. For example:
```
@[polynomial Polynomial _]
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

namespace Mathlib.Tactic.Polynomial

section extension

end extension

/-- Infer base ring for `Polynomial R` -/
@[infer_polynomial_base Polynomial _]
def polynomialInferBase : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure

/-- Infer base ring for `MvPolynomial _ R` -/
@[infer_polynomial_base MvPolynomial _ _]
def mvPolynomialInferBaseImpl : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | MvPolynomial _ R _ => pure R
  | _ => failure

section Lemmas
variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[polynomial_post]
theorem _root_.Polynomial.algebraMap_eq_C : algebraMap R _ = Polynomial.C := rfl

@[polynomial_post]
theorem _root_.MvPolynomial.algebraMap_eq_C :
    algebraMap R (MvPolynomial σ R) = MvPolynomial.C := rfl

@[polynomial_pre]
theorem _root_.MvPolynomial.C_eq_algebraMap :
    MvPolynomial.C = algebraMap R (MvPolynomial σ R) := rfl

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
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  let preThms ← polynomialPreExt.getTheorems
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[preThms, thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in polynomial tactic: preprocessing should not close goals"
  return r

open Tactic

/-- Prove equality of polynomials allowing for variables in the exponent.

`example (a : ℚ) : (X + C a) * (X - C a) = X^2 + C (a^2) := by polynomial`

See also:
* `polynomial_nf` for normalizing polynomial expressions into sum-of-monomial form.
* `match_coefficients` for creating side goals equating matching coefficients. -/
elab (name := polynomial) "polynomial":tactic =>
  withMainContext do
    let g ← preprocess (← getMainGoal)
    let some (α, _, _) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "polynomial failed: not an equality"
    let mut β : Expr := default
    try
      β ← Polynomial.inferBase α
    catch _ =>
      throwError "polynomial failed: not an equality of (mv)polynomials"
    AtomM.run .default (Algebra.proveEq (some (← inferLevelQ β)) g)

/-- Prove equality of polynomials by normalizing both sides and equating matching coefficients as
side goals.

```
example (a b : ℚ) : (X + C 1) * (X - C 1) = X^2 + C a * X + C b := by
  match_coefficients
  /- ⊢ 0 = a
     ⊢ -1 = b -/
```

See also:
* `polynomial` for proving equality of polynomials without producing side goals.
* `polynomial_nf` for normalizing polynomial expressions into sum-of-monomial form. -/
elab (name := matchCoeffients) "match_coefficients" :tactic =>
  Tactic.liftMetaTactic fun g ↦ do
    let some (α, _, _) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "match_coefficients failed: not an equality"
    let mut β : Expr := default
    try
      β ← inferBase α
    catch _ => throwError "match_coefficients failed: not an equality of (mv)polynomials"
    let goals ← matchScalarsAux (some (← inferLevelQ β)) (← preprocess g)
    /- TODO: What if the base ring is `Polynomial _`? We would have rewritten `C` into `_ • 1` and
    should really turn it back to `C`. Maybe we just rung the polynomial cleanup routine instead?-/
    goals.mapM (applySimp (RingNF.cleanup {}))

/-- Normalize a polynomial expression into standard form. Used by `polynomial_nf`. -/
def evalExprPoly (e : Expr) : AtomM Simp.Result := do
  let ⟨_, α, e⟩ ← inferTypeQ e
  let mut R : Expr := default
  try R ← inferBase α
  --TODO : better error message that explains that the tactic can be extended?
  catch _ => throwError "not a polynomial"
  let ⟨_, R'⟩ ← inferLevelQ R
  Algebra.evalExpr R' e

/- We need `mul_one` even though `algebra` already has it, because `a • 1` -> `C a * 1` introduces
new ones. -/
attribute [polynomial_post] mul_one Algebra.smul_def Polynomial.algebraMap_eq_C

/-- A cleanup routine, which simplifies normalized expressions to a more human-friendly format.
This is the `algebra_nf` cleanup routine with a little extra work to turn scalar multiplication
into `(MV)Polynomial.C` -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let r ← Algebra.cleanup cfg r
    let thms : SimpTheorems ← polynomialPostExt.getTheorems
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Simplification tactic for polynomials over commutative (semi)rings, which rewrites all
polynomial expressions into normal form.

See also:
* `polynomial` for proving equality of polynomials without producing side goals.
* `match_coefficients` for creating side goals equating matching coefficients. -/
elab (name := polynomialNF) "polynomial_nf" tk:"!"? loc:(location)?  : tactic => do
  liftMetaTactic' preprocess
  let mut cfg := {}
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (evalExprPoly) (cleanup cfg)
  transformAtLocation (m ·) "polynomial_nf" loc cfg.failIfUnchanged false

end Mathlib.Tactic.Polynomial
