/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

This file concerns the partial derivatives of a bivariate function.

## Main results

- `hasStrictFDerivAt_uncurry_coprod`: establishing strict differentiability of the uncurried
  function in the product space, this requires validity of the mean value theorem in both underlying
  spaces.
-/

open scoped Convex Topology
open Asymptotics Metric

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 F]

/-- If a bivariate function has partial derivatives $f_1$ and $f_2$ in a neighbourhood of a point
$(x_1,x_2)$, continuous at that point, then it is strictly differentiable there with derivative
$(\xi_1,\xi_2)\mapsto f_1(x_1,x_2)\cdot\xi_1 + f_2(x_1,x_2)\cdot\xi_2$. -/
theorem hasStrictFDerivAt_uncurry_coprod [IsRCLikeNormedField 𝕜]
    [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} (cf₁ : ContinuousAt ↿f₁ (x₁, x₂))
    (df₁ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f · y.2) (↿f₁ y) y.1)
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousAt ↿f₂ (x₁, x₂))
    (df₂ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f y.1 ·) (↿f₂ y) y.2) :
    HasStrictFDerivAt ↿f ((f₁ x₁ x₂).coprod (f₂ x₁ x₂)) (x₁, x₂) := by
  rw [hasStrictFDerivAt_iff_isLittleO]
  calc
    fun (y, z) => f y.1 y.2 - f z.1 z.2 - ((f₁ x₁ x₂).coprod (f₂ x₁ x₂)) (y - z)
    _ = fun (y, z) => (f y.1 z.2 - f z.1 z.2 - f₁ x₁ x₂ (y.1 - z.1))
          + (f y.1 y.2 - f y.1 z.2 - f₂ x₁ x₂ (y.2 - z.2)) := by
      ext
      dsimp only [ContinuousLinearMap.coprod_apply]
      abel
    _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] fun (y, z) => y - z := by
      simp_rw [continuousAt_iff', dist_eq_norm] at cf₁ cf₂
      apply IsLittleO.add
      · calc
          fun (y, z) => f y.1 z.2 - f z.1 z.2 - f₁ x₁ x₂ (y.1 - z.1)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.1 - z.1 : _ → E₁) := by
            simp_rw [isLittleO_iff, eventually_nhds_iff_ball]
            intro ε hε
            obtain ⟨δ, hδ, hf₁⟩ := eventually_nhds_iff_ball.mp ((cf₁ ε hε).and df₁)
            use δ, hδ
            simp_rw [← ball_prod_same] at ⊢ hf₁
            intro (y, z) ⟨hy, hz⟩
            exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun u => f u z.2)
              (fun u hu => (hf₁ (u, z.2) ⟨hu, hz.2⟩).2.hasFDerivWithinAt)
              (fun u hu => (hf₁ (u, z.2) ⟨hu, hz.2⟩).1.le)
              (convex_ball x₁ δ) hz.1 hy.1
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]
      · calc
          fun (y, z) => f y.1 y.2 - f y.1 z.2 - f₂ x₁ x₂ (y.2 - z.2)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.2 - z.2 : _ → E₂) := by
            simp_rw [isLittleO_iff, eventually_nhds_iff_ball]
            intro ε hε
            obtain ⟨δ, hδ, hf₂⟩ := eventually_nhds_iff_ball.mp ((cf₂ ε hε).and df₂)
            use δ, hδ
            simp_rw [← ball_prod_same] at ⊢ hf₂
            intro (y, z) ⟨hy, hz⟩
            exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
              (fun v hv => (hf₂ (y.1, v) ⟨hy.1, hv⟩).2.hasFDerivWithinAt)
              (fun v hv => (hf₂ (y.1, v) ⟨hy.1, hv⟩).1.le)
              (convex_ball x₂ δ) hz.2 hy.2
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]

theorem hasFDerivWithinAt_uncurry_of_continuousWithinAt_snd
    [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₂] {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {s₁ : Set E₁} {s₂ : Set E₂} (seg : ∀ᶠ y₂ in 𝓝[s₂] x₂, [x₂ -[ℝ] y₂] ⊆ s₂)
    {f₁x : E₁ →L[𝕜] F} (df₁x : HasFDerivWithinAt (f · x₂) f₁x s₁ x₁)
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousWithinAt ↿f₂ (s₁ ×ˢ s₂) (x₁, x₂))
    (df₂ : ∀ᶠ y in 𝓝[s₁ ×ˢ s₂] (x₁, x₂), HasFDerivWithinAt (f y.1 ·) (f₂ y.1 y.2) s₂ y.2) :
    HasFDerivWithinAt ↿f (f₁x.coprod (f₂ x₁ x₂)) (s₁ ×ˢ s₂) (x₁, x₂) := by
  rw [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO, nhdsWithin_prod_eq]
  calc
    fun y => ↿f y - f x₁ x₂ - (f₁x.coprod (f₂ x₁ x₂)) (y.1 - x₁, y.2 - x₂)
    _ = fun y => f y.1 x₂ - f x₁ x₂ - f₁x (y.1 - x₁) + (↿f y - f y.1 x₂ - f₂ x₁ x₂ (y.2 - x₂)) := by
      ext
      rw [ContinuousLinearMap.coprod_apply]
      abel
    _ =o[𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂] fun y => (y.1 - x₁, y.2 - x₂) := by
      apply IsLittleO.add
      · calc
          _ = (fun y₁ => f y₁ x₂ - f x₁ x₂ - f₁x (y₁ - x₁)) ∘ Prod.fst := by
            rw [Function.comp_def]
          _ =o[𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂] ((fun y₁ => y₁ - x₁) ∘ Prod.fst) := by
            apply IsLittleO.comp_fst
            rwa [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO] at df₁x
          _ =O[𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂] fun y => (y.1 - x₁, y.2 - x₂) := by
            apply isBigO_of_le
            simp
      · calc
          fun y => ↿f y - f y.1 x₂ - f₂ x₁ x₂ (y.2 - x₂)
          _ =o[𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂] fun y => y.2 - x₂ := by
            rw [isLittleO_iff]
            intro ε hε
            have hf₂ := (continuousWithinAt_iff'.mp cf₂ ε hε).and df₂
            rw [Filter.eventually_iff, mem_nhdsWithin_iff] at hf₂
            obtain ⟨δ, hδ, hf₂⟩ := hf₂
            apply (seg.prod_inr (𝓝[s₁] x₁)).mp
            rw [← nhdsWithin_prod_eq, Filter.eventually_iff, mem_nhdsWithin_iff]
            use δ, hδ
            intro (y₁, y₂) hy hs₂
            rw [← ball_prod_same, Set.prod_inter_prod] at hy hf₂
            simp_rw [Set.subset_setOf, dist_eq_norm] at hf₂
            have hb₂ := convex_iff_segment_subset.mp (convex_ball x₂ δ) (mem_ball_self hδ) hy.2.1
            exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
              (fun z hz => (hf₂ (y₁, z) ⟨hy.1, hb₂ hz, hs₂ hz⟩).2.mono hs₂)
              (fun z hz => (hf₂ (y₁, z) ⟨hy.1, hb₂ hz, hs₂ hz⟩).1.le)
              (convex_segment x₂ y₂) (left_mem_segment ℝ x₂ y₂) (right_mem_segment ℝ x₂ y₂)
          _ =O[𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂] fun y => (y.1 - x₁, y.2 - x₂) := by
            apply isBigO_of_le
            simp
