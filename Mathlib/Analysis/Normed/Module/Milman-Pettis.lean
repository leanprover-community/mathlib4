/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.Dual

open scoped Topology NNReal

section opNorm

namespace ContinuousLinearMap

variable {𝕜 𝕜' E F : Type*}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [DenselyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NontriviallyNormedField 𝕜']
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜' F] {σ₁₂ : 𝕜 →+* 𝕜'} [RingHomIsometric σ₁₂]

theorem exists_nnorm_eq_one_lt_apply_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < ‖f x‖ := by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNorm f hr
  obtain rfl | hx0 := eq_zero_or_norm_pos x
  · simp only [map_zero, norm_zero] at hr
    exact (not_lt_of_ge r.2 hr).elim
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖⁻¹ * ‖f x‖ by simpa [norm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖ := by simpa
    _ < ‖x‖⁻¹ * ‖f x‖ := by
      gcongr; exact lt_of_le_of_lt r.2 hr

theorem exists_nnorm_eq_one_lt_apply_of_lt_opNorm' [Nontrivial E]
    (f : E →SL[σ₁₂] F) {r : ℝ} (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · obtain ⟨y, hy⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
    refine ⟨algebraMap ℝ 𝕜 ‖y‖⁻¹ • y, ?_, lt_of_lt_of_le hr₀ <| norm_nonneg _⟩
    calc ‖algebraMap ℝ 𝕜 ‖y‖⁻¹ • y‖ = ‖algebraMap ℝ 𝕜 ‖y‖⁻¹‖ * ‖y‖ := by rw [norm_smul]
                                  _ = ‖y‖⁻¹ * ‖y‖ := by simp_all [norm_inv]
                                  _ = 1 := by rw [inv_mul_cancel₀]; rwa [norm_ne_zero_iff]
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNorm f hr
  obtain rfl | hx0 := eq_zero_or_norm_pos x
  · simp only [map_zero, norm_zero] at hr
    exact (hr₀ hr).elim
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖⁻¹ * ‖f x‖ by simpa [norm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖ := by simpa
    _ < ‖x‖⁻¹ * ‖f x‖ := by
      gcongr; exact lt_of_le_of_lt (le_of_not_gt hr₀) hr

instance [Nontrivial E] : Nontrivial (StrongDual 𝕜 E) := sorry

end ContinuousLinearMap

end opNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Metric NormedSpace Function ContinuousLinearMap Pointwise

local notation3 "E**" => StrongDual ℝ (StrongDual ℝ E)

/- Goldstine lemma (see Brezis, Chapter § 3.5, Lemma 3.4) says that the unit ball in the double
dual of a Banach space (**FAE: I suspect completeness is not needed) ** is the closure, with respect
to the weak topology `σ(E**, E*)` induced by the canonical pairing `E** × E* → ℝ`, of the image of
the unit ball in  `E`. Observe that, for any topological `𝕜`-module `M`, `strongDualPairing 𝕜 M` is
the pairing whose *first* variable is in `M*` and the second is in `M`. -/
lemma goldstine : closure (X := (WeakBilin (strongDualPairing ℝ (StrongDual ℝ E))))
  (inclusionInDoubleDual ℝ E '' (closedBall 0 1)) = closedBall (0 : E**) 1 := by sorry

lemma surjective_iff_ball_le_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) : Surjective f ↔ ∃ s : Set F, ∃ ρ > 0, sphere 0 ρ ≤ Set.range f := by
  refine ⟨fun _ ↦ ⟨Set.univ, 1, by simp_all⟩, fun ⟨s, ρ, ρ_pos, sphere_le⟩ z ↦ ?_⟩
  by_cases hz : z = 0
  · exact ⟨0, by simp_all⟩
  set α := ‖z‖ with hα_def
  have hα : α ≠ 0 := by
    rwa [norm_ne_zero_iff]
  set y := (ρ * α⁻¹) • z with hy_def
  have hy : y ∈ sphere 0 ρ := by
    simp
    calc ‖y‖ = ‖(ρ * α⁻¹) • z‖  := by rw [hy_def]
           _ = |ρ * α⁻¹| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
           _ = |ρ * α⁻¹| * |α| := by simp [hα_def]
           _ = ρ := by
            simpa [← abs_mul, mul_assoc, inv_mul_cancel₀ hα] using le_of_lt ρ_pos
  obtain ⟨x, hx⟩ := sphere_le hy
  use (ρ⁻¹ * α) • x
  rw [map_smul, hx, hy_def, ← smul_assoc, smul_eq_mul, show (ρ⁻¹ * α * (ρ * α⁻¹)) = 1 by grind,
    one_smul]

lemma exists_sub_one_lt [Nontrivial E] {ξ : E**} {δ : ℝ} (hδ : 0 < δ) (h : ‖ξ‖ = 1) :
    ∃ φ : StrongDual ℝ E, ‖φ‖ = 1 ∧ |ξ φ - 1| < δ := by
  obtain ⟨φ, hφ_eq, hφ_lt⟩ := exists_nnorm_eq_one_lt_apply_of_lt_opNorm'
    (f := ξ) (r := 1 - δ) (by grind)
  replace hφ_lt : 1 - δ < |ξ φ| := by rwa [Real.norm_eq_abs] at hφ_lt
  wlog h_pos : 0 ≤ ξ φ generalizing φ
  · exact this (-φ) (by rw [opNorm_neg, hφ_eq]) (by simpa)
      (by simpa only [map_neg, Left.nonneg_neg_iff] using le_of_not_ge h_pos)
  have : ξ φ ≤ 1 := by
    apply le_of_abs_le
    grw [← Real.norm_eq_abs, le_opNorm ξ φ, h, hφ_eq, one_mul]
  refine ⟨φ, hφ_eq, ?_⟩
  rw [← abs_neg, neg_sub]
  rw [abs_eq_self.mpr (by grind)] at ⊢ hφ_lt
  rwa [sub_lt_comm]

set_option linter.style.commandStart false

example (A : Type*) [TopologicalSpace A] (s : Set A) (a : A) :
    a ∈ closure s ↔ ∀ t, s ⊆ t ∧ IsClosed t → a ∈ t := by
  dsimp [closure]
  aesop

/- Milman-Pettis theorem: every uniformly convex Banach (**FAE: Complete Needed?**) space is\
reflexive. For the time being, we state this property as the surjectivity of
`inclusionInDoubleDual`,
but it must be proven that for normed space this is equivalent to `includionInDoubleDual` being
a homeomorphism. -/
theorem surjective_of_uniformConvexSpace [UniformConvexSpace E] :
    Surjective (inclusionInDoubleDual ℝ E) := by
  by_cases hE : ¬ Nontrivial E
  · rw [not_nontrivial_iff_subsingleton] at hE
    apply surjective_to_subsingleton
  simp at hE
  let 𝒰₁ := ((inclusionInDoubleDual ℝ E) '' (closedBall 0 1)) -- image in `E**` of the unit ball in `E`
  let X := WeakBilin <| strongDualPairing ℝ (StrongDual ℝ E) -- `E**` with the weak topology
  let 𝒯 : TopologicalSpace X := inferInstance -- the weak topology on `E**`: can use IsOpen[T] **FAE: Choose!**
  rw [surjective_iff_ball_le_range]
  refine ⟨sphere 0 1, _, zero_lt_one, ?_⟩
  intro ξ hξ
  have hξ_norm : ‖ξ‖ = 1 := by rwa [← mem_sphere_zero_iff_norm]
  have hξ_mem {V : Set _} (hV_mem : ξ ∈ V) (hV : IsOpen[𝒯] V) : ξ ∈ closure[𝒯] (V ∩ 𝒰₁) := by
    apply hV.inter_closure <| Set.mem_inter hV_mem _
    rw [goldstine]
    apply sphere_subset_closedBall hξ
  set ε := infDist ξ 𝒰₁ with ε_def
  by_cases ε_pos : 0 = ε
  · sorry
  replace ε_pos : 0 < ε := lt_of_le_of_ne infDist_nonneg ε_pos
  obtain ⟨δ, hδ_pos, hδ_dist⟩ := exists_forall_closed_ball_dist_add_le_two_sub E ε_pos
  obtain ⟨φ, hφ_norm, hφ_lt⟩ := exists_sub_one_lt (half_pos hδ_pos) hξ_norm
  set V := {x : E** | |x φ - 1| < δ/2} with hV_def
  have hV_dist {x x' : E**} (hx : x ∈ V ∩ 𝒰₁) (hx' : x' ∈ V ∩ 𝒰₁) : ‖x - x'‖ < ε/2 := sorry
  have hV_open : IsOpen[𝒯] V := by
    rw [hV_def]
    convert @Continuous.isOpen_preimage (X := X) (Y := ℝ) _ _ (fun x : E** ↦ |x φ - 1|)
      (s := ball 0 (δ / 2)) _ isOpen_ball
    · ext
      simp_all only [mem_sphere_iff_norm, sub_zero, Set.mem_inter_iff, Set.mem_setOf_eq,
        dist_zero_right, and_imp, Set.mem_preimage, mem_ball, Real.norm_eq_abs, abs_abs]
    · exact Continuous.comp (X := X) (f := fun x : E** ↦ x φ) (g := fun (x : ℝ) ↦ |x - 1|)
        (by fun_prop) <| WeakBilin.eval_continuous (strongDualPairing ℝ (StrongDual ℝ E)) _
  obtain ⟨y, hy⟩ : (V ∩ 𝒰₁).Nonempty := by
    rw [← closure_nonempty_iff (X := X)]
    exact ⟨ξ, hξ_mem hφ_lt hV_open⟩
  have subset : V ∩ 𝒰₁ ⊆ ({y} + closedBall 0 (ε/2) : (Set E**)) := sorry
  have clSub : IsClosed[𝒯] ({y} + closedBall 0 (ε/2) : (Set E**)) := sorry
  have trueEnd : infDist ξ (V ∩ 𝒰₁) ≤ ε/2 := by -- migliorare rimpiazzando` V∩𝒰₁` con 𝒰₁
    apply (infDist_le_dist_of_mem hy).trans
    specialize hξ_mem hφ_lt hV_open
    apply hξ_mem
    simp
    constructor
    · convert clSub
      simp only [singleton_add_closedBall, add_zero]
      rfl
    · convert subset
      simp
      rfl
  have := (ε_def.symm ▸ infDist_le_infDist_of_subset Set.inter_subset_right ⟨y, hy⟩).trans trueEnd
  exact not_lt_of_ge this (half_lt_self ε_pos)|>.elim
