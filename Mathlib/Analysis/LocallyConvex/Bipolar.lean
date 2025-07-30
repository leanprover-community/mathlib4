/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!

# Bipolar Theorem

## Main definitions

- `LinearMap.rightDualEquiv`: When `B` is right-separating, `F` is linearly equivalent to the
  topological dual of `E` with the weak topology.
- `LinearMap.leftDualEquiv`: When `B` is left-separating, `E` is linearly equivalent to the
  topological dual of `F` with the weak topology.

## Main statements

- `LinearMap.flip_polar_polar_eq`: The Bipolar Theorem: The bipolar of a set coincides with its
  closed absolutely convex hull.

## References

* [Conway, *A course in functional analysis*][conway1990]

## Tags

bipolar
-/

variable {𝕜 E F : Type*}

namespace LinearMap

section NormedField

variable {𝕜 E F : Type*}
variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 𝕜]

theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F →ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_closedBall _ _).linear_preimage (B i)⟩

end NormedField

variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

open TopologicalSpace in
lemma top_eq : induced (fun x y => B x y) Pi.topologicalSpace =
  ⨅ i, induced (B.flip i) inferInstance := induced_to_pi fun x y ↦ (B x) y

open TopologicalSpace in
open Topology in
lemma dualEmbedding_isSurjective : Function.Surjective (WeakBilin.eval B) := by
  intro f₁
  have c1 : Continuous[⨅ i, induced (B.flip i) inferInstance, inferInstance] f₁ := by
    convert f₁.2
    rw [← top_eq]
    rfl
  have test5 :
    ↑f₁ ∈ Submodule.span 𝕜 (Set.range (ContinuousLinearMap.toLinearMap₂
        (WeakBilin.eval B))) := by
      rw [LinearMap.mem_span_iff_continuous _]
      exact c1
  --obtain ⟨s, hs⟩ := test5
  rw [← Set.image_univ, Finsupp.mem_span_image_iff_linearCombination] at test5
  obtain ⟨l, _, hl2⟩ := test5
  use Finsupp.linearCombination 𝕜 (id (M :=F) (R := 𝕜)) l
  rw [←ContinuousLinearMap.coe_inj, ← hl2, WeakBilin.eval, coe_mk, AddHom.coe_mk]
  simp only
  rw [ContinuousLinearMap.toLinearMap₂, ContinuousLinearMap.coeLMₛₗ,
    Finsupp.linearCombination_apply]
    --, Finsupp.linearCombination_apply,
  rw [map_finsuppSum]
  simp
  aesop

lemma dualEmbedding_isInjective_of_separatingRight (hr : B.SeparatingRight) :
    Function.Injective (WeakBilin.eval B) := (injective_iff_map_eq_zero _).mpr (fun f hf =>
    (separatingRight_iff_linear_flip_nontrivial.mp hr) f (ContinuousLinearMap.coe_inj.mpr hf))

/-- When `B` is right-separating, `F` is linearly equivalent to the topological dual of `E` with the
weak topology. -/
noncomputable def rightDualEquiv (hr : B.SeparatingRight) : F ≃ₗ[𝕜] (WeakBilin B) →L[𝕜] 𝕜 :=
  LinearEquiv.ofBijective (WeakBilin.eval B)
    ⟨dualEmbedding_isInjective_of_separatingRight B hr, dualEmbedding_isSurjective B⟩

/-- When `B` is left-separating, `E` is linearly equivalent to the topological dual of `F` with the
weak topology. -/
noncomputable def leftDualEquiv (hl : B.SeparatingLeft) : E ≃ₗ[𝕜] (WeakBilin B.flip) →L[𝕜] 𝕜 :=
  rightDualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

variable [Module ℝ E]
variable [IsScalarTower ℝ 𝕜 E]

/- The Bipolar Theorem: The bipolar of a set coincides with its closed absolutely convex hull. -/
open scoped ComplexConjugate
theorem flip_polar_polar_eq {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] :
    B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  apply le_antisymm
  · simp only [Set.le_eq_subset]
    rw [← Set.compl_subset_compl]
    intro x hx
    obtain ⟨f, ⟨u, ⟨hf₁, hf₂⟩⟩⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakBilin B)
        absConvex_convexClosedHull.2 isClosed_closedAbsConvexHull hx
    have e3 : RCLike.re (f 0) < u :=
      (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
    rw [map_zero, map_zero] at e3
    let g := (1/u : ℝ) • f
    have fg : g = (1/u : ℝ) • f := rfl
    have fg2 : u • g = f := by
      rw [fg, one_div, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ (ne_of_lt e3).symm, one_smul]
    have hg₁ : ∀ a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s, RCLike.re (g a) < 1 :=
        fun _ ha => by
      rw [fg, ContinuousLinearMap.coe_smul', Pi.smul_apply, RCLike.smul_re, one_div,
        ← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp e3).2.symm)]
      exact mul_lt_mul_of_pos_left ((hf₁ _) ha) (inv_pos_of_pos e3)
    obtain ⟨f₀, hf₀⟩ := B.dualEmbedding_isSurjective g
    have hg₃ : f₀ ∈ (B.polar (E := WeakBilin B) s) := by
      simp [← hf₀, WeakBilin.eval] at hg₁
      intro x₂ hx₂
      let l := conj (B x₂ f₀) / ‖B x₂ f₀‖
      have lnorm : ‖l‖ ≤ 1 := by
        rw [norm_div, RCLike.norm_conj, norm_algebraMap', norm_norm]
        exact div_self_le_one _
      have i1 : RCLike.re ((B.flip f₀) (l • x₂)) < 1 := hg₁ _
        (balanced_iff_smul_mem.mp absConvex_convexClosedHull.1 lnorm
          (subset_closedAbsConvexHull hx₂))
      rw [CompatibleSMul.map_smul, smul_eq_mul, mul_comm, ← mul_div_assoc, LinearMap.flip_apply,
        RCLike.mul_conj, sq, mul_self_div_self, RCLike.ofReal_re] at i1
      exact le_of_lt i1
    have one_lt_x_f₀ : 1 < RCLike.re (B x f₀) := by
      rw [← one_lt_inv_mul₀ e3] at hf₂
      suffices u⁻¹ * RCLike.re (f x) = RCLike.re ((B x) f₀) by exact lt_of_lt_of_eq hf₂ this
      rw [← RCLike.re_ofReal_mul]
      congr
      simp [map_inv₀, ← fg2, ← hf₀, WeakBilin.eval]
      rw [← smul_eq_mul, ← smul_assoc]
      norm_cast
      have unz : u ≠ 0 := (ne_of_lt e3).symm
      aesop
    by_contra hc
    rw [Set.mem_compl_iff, not_not] at hc
    exact ((lt_iff_le_not_ge.mp one_lt_x_f₀).2)
      (Preorder.le_trans (RCLike.re ((B x) f₀)) ‖(B x) f₀‖ 1
        (RCLike.re_le_norm ((B x) f₀)) (hc f₀ hg₃))
  · exact closedAbsConvexHull_min (subset_bipolar B s) (polar_AbsConvex _) (polar_isClosed B.flip _)


end LinearMap
