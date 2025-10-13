/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.Algebra

-- For the ring instance in testing.
import Mathlib.Algebra.MvPolynomial.CommRing

set_option linter.all false

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List Mathlib.Tactic.Module Mathlib.Tactic.Algebra
open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq
open Mathlib.Meta AtomM

namespace Mathlib.Tactic.Polynomial

section Lemmas
variable {σ R : Type*} [CommSemiring R]

theorem Polynomial.C_eq_smul_one (a : R) : Polynomial.C a = a • (1 :  Polynomial R) := by
  rw [← Polynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one]

theorem Polynomial.monomial_eq_smul (a : R) (n : ℕ) : Polynomial.monomial n a = a • (.X ^ n) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.smul_eq_C_mul]
end Lemmas


open Mathlib.Meta AtomM

-- idea : insert algebraMap and run push_cast
-- but oh no, this gives Algebra.cast not Nat.cast. Need extra simp lemmas for Nat.cast, Int.cast?
example {x y : ℕ} : algebraMap ℕ ℤ (x * (y+1) : ℕ) = x*y + x := by
  push_cast
  ring_nf
  rfl

-- TODO: figure out what to do with Polynomial.map
/- TODO: we don't currently have a good way to normalize monomials of MvPolynomials. These are
indexed by finsupps, making it difficult to turn into the appropriate normal form. -/
def preprocess (mvarId : MVarId) : MetaM MVarId := do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  let simps : Array Name := #[``Algebra.algebraMap_eq_smul_one,
    ``Polynomial.C_eq_smul_one, ``Polynomial.monomial_eq_smul,
    ``Polynomial.map_add, ``Polynomial.map_mul, ``Polynomial.map_pow,
    ``Polynomial.map_C, ``Polynomial.map_X, ``Polynomial.map_natCast,
    ``MvPolynomial.C_eq_smul_one, ]
  for thm in simps do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in polynomial tactic: preprocessing should not close goals"
  return r

open Tactic

/-- Infer the ring `R` in an expression of the form `Polynomial R` or `MvPolynomial R` -/
def inferBase (e : Expr) : Option Expr :=
  match_expr e with
  | Polynomial R _ => some R
  | MvPolynomial _ R _ => some R
  | _ => none

elab (name := polynomial) "polynomial":tactic =>
  withMainContext do
    let g ← preprocess (← getMainGoal)
    let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "polynomial failed: not an equality"
    let some β := inferBase α | throwError "polynomial failed: not an equality of (mv)polynomials"
    AtomM.run .default (Algebra.proveEq (some (← inferLevelQ β)) g)

elab (name := matchCoeffients) "match_coefficients" :tactic =>
  Tactic.liftMetaTactic fun g ↦ do
    let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "polynomial failed: not an equality"
    let some β := inferBase α | throwError "polynomial failed: not an equality of (mv)polynomials"
    let goals ← matchScalarsAux (some (← inferLevelQ β)) (← preprocess g)
    /- TODO: What if the base ring is `Polynomial _`? We would have rewritten `C` into `_ • 1` and
    should really turn it back to `C`. Maybe we just rung the polynomial cleanup routine instead?-/
    goals.mapM (runSimp (RingNF.cleanup {}))

def evalExprPoly (e : Expr) : AtomM Simp.Result := do
  let ⟨u, α, e⟩ ← inferTypeQ e
  let some R := inferBase α | throwError "not a polynomial"
  let ⟨v, R⟩ ← inferLevelQ R
  Algebra.evalExpr R e

/-- A cleanup routine, which simplifies normalized expressions to a more human-friendly format.
This is the `algebra_nf` cleanup routine with a little extra work to turn scalar multiplication
into `(MV)Polynomial.C` -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let r ← Algebra.cleanup cfg r
    let thms : SimpTheorems := {}
      /- The following theorems are polynomial specific. -/
    let thms ← [ ``mul_one,
    ``Polynomial.smul_eq_C_mul, ``MvPolynomial.smul_eq_C_mul,  ``Polynomial.map_add,
    ``Polynomial.map_smul].foldlM (·.addConst ·) thms
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

elab (name := polynomialNF) "polynomial_nf" tk:"!"? loc:(location)?  : tactic => do
  liftMetaTactic' preprocess
  let mut cfg := {}
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (evalExprPoly) (cleanup cfg)
  transformAtLocation (m ·) "polynomial_nf" loc cfg.failIfUnchanged false


end Mathlib.Tactic.Polynomial
