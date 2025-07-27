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


## References

* [Conway, *A course in functional analysis*][conway1990]

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


-- `RCLike 𝕜` and `IsScalarTower ℝ 𝕜 E` needed for `RCLike.geometric_hahn_banach_closed_point`
variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

-- c.f. LinearMap.continuous_of_locally_bounded
lemma isBounded_of_Continuous (f : WeakBilin B →L[𝕜] 𝕜) :
    Seminorm.IsBounded B.toSeminormFamily (fun _ : Fin 1 => normSeminorm 𝕜 𝕜) f.toLinearMap := by
  obtain ⟨s,C, hC1, hC2⟩ :=
    Seminorm.bound_of_continuous B.weakBilin_withSeminorms
      f.toSeminorm (continuous_norm.comp f.continuous)
  rw [Seminorm.IsBounded, forall_const]
  exact ⟨s, ⟨C, hC2⟩⟩

/-
See
- Conway V Theorem 1.3 on p108
     - III 2.1 on p68 - continuous iff cont at 0 iff cont at a point iff scalar bound
     - III 5.3 on p54 - a linear funtional is continuous iff the kernel is closed (a iff d in 3.1)
     - Mathlib/Analysis/Normed/Group/Hom.lean:theorem isClosed_ker
- Bourbaki TVS II.43
- Rudin Theorem 3.10
-/
lemma dualEmbedding_isSurjective : Function.Surjective (WeakBilin.eval B) := by
  intro f₁
  have test5 : ∃ (s₁ : Finset F),
    ↑f₁ ∈ Submodule.span 𝕜 (Set.range (ContinuousLinearMap.toLinearMap₁₂
      (WeakBilin.eval B) ∘ Subtype.val : s₁ → WeakBilin B →ₗ[𝕜] 𝕜)) := by
    obtain ⟨s,hS⟩ := isBounded_of_Continuous B f₁ (Fin.last 0)
    exact ⟨s, functional_mem_span_iff.mpr hS⟩
  obtain ⟨s, hs⟩ := test5
  rw [← Set.image_univ, Finsupp.mem_span_image_iff_linearCombination] at hs
  obtain ⟨l, _, hl2⟩ := hs
  use Finsupp.linearCombination 𝕜 Subtype.val l
  rw [←ContinuousLinearMap.coe_inj, ← hl2, WeakBilin.eval, coe_mk, AddHom.coe_mk]
  simp only
  rw [ContinuousLinearMap.toLinearMap₁₂, ContinuousLinearMap.coeLMₛₗ,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
  simp

lemma dualEmbedding_isInjective_of_separatingRight (hr : B.SeparatingRight) :
    Function.Injective (WeakBilin.eval B) := (injective_iff_map_eq_zero _).mpr (fun f hf =>
    (separatingRight_iff_linear_flip_nontrivial.mp hr) f (ContinuousLinearMap.coe_inj.mpr hf))

/-- When `B` is right-separating, `F` is linearly equivalent to the topological dual of `E` with the
weak topology. -/
noncomputable def dualEquiv (hr : B.SeparatingRight) : F ≃ₗ[𝕜] (WeakBilin B) →L[𝕜] 𝕜 :=
  LinearEquiv.ofBijective (WeakBilin.eval B)
    ⟨dualEmbedding_isInjective_of_separatingRight B hr, dualEmbedding_isSurjective B⟩

/-- When `B` is left-separating, `E` is linearly equivalent to the topological dual of `F` with the
weak topology. -/
noncomputable def strictEquiv2 (hl : B.SeparatingLeft) : E ≃ₗ[𝕜] (WeakBilin B.flip) →L[𝕜] 𝕜 :=
  dualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

variable [Module ℝ E]
variable [IsScalarTower ℝ 𝕜 E]

-- Conway p127
open scoped ComplexConjugate
theorem Bipolar {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] :
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
    have hg₁ : ∀ a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s, RCLike.re (g a) < 1 :=
        fun _ ha => by
      rw [fg, ContinuousLinearMap.coe_smul', Pi.smul_apply, RCLike.smul_re, one_div,
        ← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp e3).2.symm)]
      exact mul_lt_mul_of_pos_left ((hf₁ _) ha) (inv_pos_of_pos e3)
    obtain ⟨f₀, hf₀⟩ := B.dualEmbedding_isSurjective g
    have hg₃ : f₀ ∈ (B.polar (E := WeakBilin B) s) := by
      rw [← hf₀] at hg₁
      simp [WeakBilin.eval] at hg₁
      rw [polar_mem_iff]
      intro x₂ hx₂
      let l := conj (B x₂ f₀) / ‖B x₂ f₀‖
      have lnorm : ‖l‖ ≤ 1 := by
        unfold l
        rw [norm_div]
        rw [RCLike.norm_conj]
        simp only [norm_algebraMap', norm_norm]
        exact div_self_le_one _
      have i1 : RCLike.re ((B.flip f₀) (l • x₂)) < 1 := by
        apply hg₁
        apply balanced_iff_smul_mem.mp
        have s1 : AbsConvex 𝕜 ((closedAbsConvexHull (E := WeakBilin B) 𝕜) s) := by exact
          absConvex_convexClosedHull
        apply s1.1
        exact lnorm
        apply subset_closedAbsConvexHull hx₂
      rw [CompatibleSMul.map_smul] at i1
      rw [smul_eq_mul] at i1
      simp only [l] at i1
      rw [mul_comm] at i1
      rw [← mul_div_assoc] at i1
      rw [LinearMap.flip_apply] at i1
      rw [RCLike.mul_conj] at i1
      rw [sq] at i1
      simp at i1
      exact le_of_lt i1
    have fg2 : u • g = f := by
      rw [fg]
      simp only [one_div]
      rw [← smul_assoc]
      rw [smul_eq_mul]
      rw [mul_inv_cancel₀, one_smul]
      exact Ne.symm (ne_of_lt e3)
    have one_lt_x_f₀ : 1 < RCLike.re (B x f₀) := by
      rw [← one_lt_inv_mul₀ e3] at hf₂
      suffices u⁻¹ * RCLike.re (f x) = RCLike.re ((B x) f₀) by exact lt_of_lt_of_eq hf₂ this
      rw [← RCLike.re_ofReal_mul]
      congr
      simp
      rw [← fg2]
      rw [← hf₀]
      simp [WeakBilin.eval]
      rw [← smul_eq_mul]
      rw [← smul_assoc]
      suffices u • ((algebraMap ℝ 𝕜) u)⁻¹ = 1 by
        rw [this]
        rw [one_smul]
        rfl
      norm_cast
      rw [smul_eq_mul]
      have unz : u ≠ 0 := by exact Ne.symm (ne_of_lt e3)
      exact CommGroupWithZero.mul_inv_cancel u unz
    by_contra hc
    simp at hc
    have hc₁ : ‖B x f₀‖ ≤ 1 := by
      exact hc f₀ hg₃
    have hc₂ : RCLike.re (B x f₀) ≤ ‖B x f₀‖ := by
      exact RCLike.re_le_norm ((B x) f₀)
    have hc₃ : RCLike.re (B x f₀) ≤ 1 := by
      exact Preorder.le_trans (RCLike.re ((B x) f₀)) ‖(B x) f₀‖ 1 hc₂ (hc f₀ hg₃)
    rw [lt_iff_le_not_ge] at one_lt_x_f₀
    have hc₄ : ¬RCLike.re ((B x) f₀) ≤ 1 := by
      exact one_lt_x_f₀.2
    exact hc₄ hc₃
  · exact closedAbsConvexHull_min (subset_bipolar B s) (polar_AbsConvex _) (polar_isClosed B.flip _)


end LinearMap
