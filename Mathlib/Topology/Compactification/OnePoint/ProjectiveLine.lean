/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
import Mathlib.LinearAlgebra.Projectivization.GLAction
import Mathlib.Topology.Compactification.OnePoint.Basic

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

open Projectivization Matrix

namespace OnePoint

section DivisionRing

variable (K : Type*) [DivisionRing K] [DecidableEq K]

/-- The one-point compactification of a division ring `K` is equivalent to
the projectivivization `ℙ K (K × K)`. -/
def equivProjectivization :
    OnePoint K ≃ ℙ K (K × K) where
  toFun p := p.elim (mk K (1, 0) (by simp)) (fun t ↦ mk K (t, 1) (by simp))
  invFun p := by
    refine Projectivization.lift
      (fun u : {v : K × K // v ≠ 0} ↦ if u.1.2 = 0 then ∞ else ((u.1.2)⁻¹ * u.1.1)) ?_ p
    rintro ⟨-, hv⟩ ⟨⟨x, y⟩, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hv
    by_cases h₀ : y = 0 <;> simp [h₀, ht, mul_assoc]
  left_inv p := by cases p <;> simp
  right_inv p := by
    induction p using ind with | h p hp =>
    obtain ⟨x, y⟩ := p
    by_cases h₀ : y = 0 <;> simp only [mk_eq_mk_iff', h₀, Projectivization.lift_mk, if_true,
      if_false, OnePoint.elim_infty, OnePoint.elim_some, Prod.smul_mk, Prod.mk.injEq, smul_eq_mul,
      mul_zero, and_true]
    · use x⁻¹
      simp_all
    · exact ⟨y⁻¹, rfl, inv_mul_cancel₀ h₀⟩

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

end DivisionRing

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- For a field `K`, the group `GL(2, K)` acts on `OnePoint K`. -/
instance instGLAction : MulAction (GL (Fin 2) K) (OnePoint K) :=
  (equivProjectivization K).mulAction (GL (Fin 2) K)

lemma smul_infty_def (g : GL (Fin 2) K) :
    g • ∞ = (equivProjectivization K).symm (.mk K (g 0 0, g 1 0) (fun h ↦ by
      simpa [det_fin_two, Prod.mk_eq_zero.mp h] using g.det_ne_zero)) := by
  simp [Equiv.smul_def, MulAction.compHom_smul_def, Projectivization.smul_mk, mulVec_eq_sum,
    Units.smul_def]

@[simp]
lemma smul_infty_eq_ite (g : GL (Fin 2) K) :
    (g • ∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0 := by
  by_cases h : g 1 0 = 0 <;>
  simp [h, div_eq_inv_mul, smul_infty_def]

lemma smul_infty_eq_iff (g : GL (Fin 2) K) :
    g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0 := by
  simp

lemma smul_some_eq_ite (g : GL (Fin 2) K) (k : K) :
    g • (k : OnePoint K) =
      if g 1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1) := by
  simp [Equiv.smul_def, MulAction.compHom_smul_def, Projectivization.smul_mk, mulVec_eq_sum,
    div_eq_inv_mul, mul_comm, Units.smul_def]

end Field

end OnePoint
