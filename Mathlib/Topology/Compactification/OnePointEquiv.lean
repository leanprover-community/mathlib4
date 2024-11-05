/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Compactification.OnePoint

/-!
# One-point compactification and projectivization

We construct a set-theoretic equivalence between
`OnePoint K` and the projectivization `ℙ K (K × K)` for an arbitrary division ring `K`.

TODO: Add the extension of this equivalence to a homeomorphism in the case `K = ℝ`,
where `OnePoint ℝ` gets the topology of one-point compactification.


## Main definitions and results

* `OnePoint.equivProjectivization` : the equivalence `OnePoint K ≃ ℙ K (K × K)`.

## Tags

one-point extension, projectivization
-/

open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization

namespace OnePoint
variable (K : Type*) [DivisionRing K] [DecidableEq K]

/-- The one-point compactification of a division ring `K` is equivalent to
 the projectivivization `ℙ K (K × K)`. -/
def equivProjectivization :
    OnePoint K ≃ ℙ K (K × K) where
  toFun p := Option.elim p (mk K (1, 0) (by simp)) (fun t ↦ mk K (t, 1) (by simp))
  invFun p := by
    refine Projectivization.lift
      (fun u : {v : K × K // v ≠ 0} ↦ if u.1.2 ≠ 0 then ((u.1.2)⁻¹ * u.1.1) else ∞) ?_ p
    rintro ⟨-, hv⟩ ⟨⟨x, y⟩, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hv
    by_cases h₀ : y = 0 <;> simp [h₀, ht, mul_assoc]
  left_inv p := by cases p <;> simp [OnePoint.infty, OnePoint.some]
  right_inv p := by
    induction' p using ind with p hp
    obtain ⟨x, y⟩ := p
    by_cases h₀ : y = 0 <;>
    simp only [Option.elim, ne_eq, ite_not, h₀, Projectivization.lift_mk, reduceIte]
    · have h₀' : x ≠ 0 := by aesop
      simp only [mk_eq_mk_iff, Prod.smul_mk, smul_zero, Prod.mk.injEq, and_true]
      exact ⟨Units.mk0 _ (inv_ne_zero h₀'), by simp [h₀']⟩
    · simp only [mk_eq_mk_iff, Prod.smul_mk, Prod.mk.injEq]
      exact ⟨Units.mk0 _ (inv_ne_zero h₀), by simp [h₀]⟩

@[simp]
lemma equivProjectivization_apply_infinity :
    equivProjectivization K ∞ = mk K ⟨1, 0⟩ (by simp) :=
  rfl

@[simp]
lemma equivProjectivization_apply_coe (t : K) :
    equivProjectivization K t = mk K ⟨t, 1⟩ (by simp) :=
  rfl

@[simp]
lemma equivProjectivization_symm_apply_mk (x y : K) (h : (x, y) ≠ 0) :
    (equivProjectivization K).symm (mk K ⟨x, y⟩ h) = if y = 0 then ∞ else y⁻¹ * x := by
  simp [equivProjectivization]

end OnePoint
