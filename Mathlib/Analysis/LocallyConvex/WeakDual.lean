/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Data.Finsupp.Order
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicitly give a neighborhood basis in terms of the family of seminorms
`fun x => ‖B x y‖` for `y : F`.

## Main definitions

* `LinearMap.toSeminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `fun x => ‖f x‖`.
* `LinearMap.toSeminormFamily`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
  `F → Seminorm 𝕜 E`.

## Main statements

* `LinearMap.hasBasis_weakBilin`: the seminorm balls of `B.toSeminormFamily` form a
  neighborhood basis of `0` in the weak topology.
* `LinearMap.toSeminormFamily.withSeminorms`: the topology of a weak space is induced by the
  family of seminorms `B.toSeminormFamily`.
* `WeakBilin.locallyConvexSpace`: a space endowed with a weak topology is locally convex.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]
* [Rudin, *Functional Analysis*][rudin1991]

## Tags

weak dual, seminorm
-/


variable {𝕜 E F : Type*}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` by
`fun x => ‖f x‖` -/
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f

theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl

@[simp]
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl

theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]

theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

/-- Construct a family of seminorms from a bilinear form. -/
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm

@[simp]
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl

theorem functional_mem_span_iff {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Finset F) (f : E →ₗ[𝕜] 𝕜) :
    f ∈ Submodule.span 𝕜 (Set.range (B.flip ∘ Subtype.val : s → E →ₗ[𝕜] 𝕜)) ↔
    ∃ γ, ∀ (x : E), ‖f x‖ ≤ γ * ((s.sup B.toSeminormFamily) x) := by
  constructor
  · intro h
    rw [← Set.image_univ, Finsupp.mem_span_image_iff_linearCombination] at h
    obtain ⟨l, hl1, hl2⟩ := h
    use (l.sum fun i d ↦ ‖d‖)
    intro x
    rw [← hl2, Finsupp.linearCombination_apply, finsupp_sum_apply,
      (Finsupp.sum_mul ((s.sup B.toSeminormFamily) x) l)]
    have e4' (i : s) : (B.toSeminormFamily i) x ≤ (s.sup B.toSeminormFamily) x :=
      Seminorm.le_finset_sup_apply (Finset.coe_mem i)
    have e4 (d : 𝕜) (i : s) :
        ‖d * ((B.flip ∘ Subtype.val) i) x‖ ≤ ‖d‖ * ((s.sup B.toSeminormFamily) x) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (e4' i) (norm_nonneg d)
    have e6 : (l.sum fun i d ↦ ‖d * ((B.flip ∘ Subtype.val) i) x‖) ≤
        (l.sum fun i d ↦ (‖d‖ * ((s.sup B.toSeminormFamily) x))) :=
      Finsupp.sum_le_sum (α := 𝕜) (β := ℝ) (fun i _ => e4 (l i) i)
    apply le_trans (norm_sum_le _ _)
    exact (le_trans e6 (Preorder.le_refl (l.sum fun i d ↦ ‖d‖ * (s.sup B.toSeminormFamily) x)))
  · intro ⟨γ, hγ⟩
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    rw [mem_ker, ← norm_le_zero_iff]
    convert (hγ x)
    rw [Submodule.mem_iInf, Subtype.forall] at hx
    have e1 : (s.sup B.toSeminormFamily) x = 0 := by
      rw [le_antisymm_iff]
      constructor
      · apply Seminorm.finset_sup_apply_le (Preorder.le_refl 0)
        intro i his
        rw [toSeminormFamily_apply, norm_le_zero_iff]
        exact hx _ his
      · exact apply_nonneg (s.sup B.toSeminormFamily) x
    simp_all only [mul_zero]

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  let e : F ≃ (Σ _ : F, Fin 1) := .symm <| .sigmaUnique _ _
  have : Nonempty (Σ _ : F, Fin 1) := e.symm.nonempty
  withSeminorms_induced (withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜 𝕜))
    (LinearMap.ltoFun 𝕜 F 𝕜 ∘ₗ B : (WeakBilin B) →ₗ[𝕜] (F → 𝕜)) |>.congr_equiv e

theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basisSets _root_.id :=
  LinearMap.weakBilin_withSeminorms B |>.hasBasis

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

instance WeakBilin.locallyConvexSpace {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} :
    LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex
