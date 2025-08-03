/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

This file concerns the partial derivatives of a bivariate function.

## Main statements

- `hasStrictFDerivAt_uncurry_coprod`: establishing strict differentiability of the uncurried
  function in the product space, this requires validity of the mean value theorem in the domain of
  each argument.
-/

open Asymptotics Filter
open scoped Convex Topology

section aux

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {s : Set E} {t : Set F} {ξ : E} {x : F} {y z : E → F}

theorem eventually_segment {r : E → F → Prop}
    (hy : Tendsto y (𝓝[s] ξ) (𝓝 x)) (hz : Tendsto z (𝓝[s] ξ) (𝓝 x))
    (seg : ∀ᶠ χ in 𝓝[s] ξ, [z χ -[ℝ] y χ] ⊆ t) (hr : ∀ᶠ p in 𝓝[s ×ˢ t] (ξ, x), r p.1 p.2) :
    ∀ᶠ χ in 𝓝[s] ξ, ∀ v ∈ [z χ -[ℝ] y χ], r χ v := by
  rw [nhdsWithin_prod_eq, eventually_prod_iff] at hr
  obtain ⟨p, hp, q, hq, hr⟩ := hr
  rw [eventually_iff, Metric.mem_nhdsWithin_iff] at hq
  obtain ⟨δ, hδ, hq⟩ := hq
  rw [Metric.tendsto_nhds] at hy hz
  filter_upwards [hp, hy δ hδ, hz δ hδ, seg] with χ hp hy hz seg
  have := convex_iff_segment_subset.mp (convex_ball x δ) hz hy
  exact fun v hv => hr hp <| hq ⟨this hv, seg hv⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

theorem isLittleO_sub_sub_fderiv {f : E → F → G} {f' : E → F → F →L[𝕜] G}
    (hy : Tendsto y (𝓝[s] ξ) (𝓝 x)) (hz : Tendsto z (𝓝[s] ξ) (𝓝 x))
    (seg : ∀ᶠ χ in 𝓝[s] ξ, [z χ -[ℝ] y χ] ⊆ t) (cf' : ContinuousWithinAt ↿f' (s ×ˢ t) (ξ, x))
    (df' : ∀ᶠ p in 𝓝[s ×ˢ t] (ξ, x), HasFDerivWithinAt (f p.1) (f' p.1 p.2) t p.2) :
    (fun χ => f χ (y χ) - f χ (z χ) - f' ξ x (y χ - z χ)) =o[𝓝[s] ξ] (fun χ => y χ - z χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace cf' : ∀ᶠ χ in 𝓝[s] ξ, ∀ v ∈ [z χ -[ℝ] y χ], dist (f' χ v) (f' ξ x) < ε := by
    rw [Metric.continuousWithinAt_iff'] at cf'
    exact eventually_segment hy hz seg (cf' ε hε)
  replace df' : ∀ᶠ χ in 𝓝[s] ξ, ∀ v ∈ [z χ -[ℝ] y χ], HasFDerivWithinAt (f χ) (f' χ v) t v :=
    eventually_segment hy hz seg df'
  filter_upwards [seg, cf', df'] with χ seg cf' df'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun v hv => (df' v hv).mono seg) (fun v hv => (cf' v hv).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

end aux

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 F]

/-- If a bivariate function $f$ has partial derivatives $f_1$ and $f_2$ in a neighbourhood of a
point $(x_1,x_2)$ and if they are continuous at that point then $f$ is strictly differentiable there
with derivative $(h_1,h_2)\mapsto f_1(x_1,x_2)\cdot h_1 + f_2(x_1,x_2)\cdot h_2$. -/
theorem hasStrictFDerivAt_uncurry_coprod [IsRCLikeNormedField 𝕜]
    [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} (cf₁ : ContinuousAt ↿f₁ (x₁, x₂))
    (df₁ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f · y.2) (↿f₁ y) y.1)
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousAt ↿f₂ (x₁, x₂))
    (df₂ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f y.1 ·) (↿f₂ y) y.2) :
    HasStrictFDerivAt ↿f ((f₁ x₁ x₂).coprod (f₂ x₁ x₂)) (x₁, x₂) := by
  unfold ContinuousAt at cf₁ cf₂
  rw [nhds_prod_eq] at cf₁ cf₂ df₁ df₂
  rw [hasStrictFDerivAt_iff_isLittleO]
  calc
    fun (y, z) => f y.1 y.2 - f z.1 z.2 - ((f₁ x₁ x₂).coprod (f₂ x₁ x₂)) (y - z)
    _ = fun (y, z) => (f y.1 z.2 - f z.1 z.2 - f₁ x₁ x₂ (y.1 - z.1))
          + (f y.1 y.2 - f y.1 z.2 - f₂ x₁ x₂ (y.2 - z.2)) := by
      ext
      dsimp only [ContinuousLinearMap.coprod_apply]
      abel
    _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] fun (y, z) => y - z := by
      apply IsLittleO.add
      · calc
          fun (y, z) => f y.1 z.2 - f z.1 z.2 - f₁ x₁ x₂ (y.1 - z.1)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.1 - z.1 : _ → E₁) := by
            rw [← nhdsWithin_univ]
            have := tendsto_snd.prodMk <| tendsto_snd.comp <| tendsto_snd.comp <|
              tendsto_fst (f := (𝓝 x₁ ×ˢ 𝓝 x₂) ×ˢ (𝓝 x₁ ×ˢ 𝓝 x₂)) (g := 𝓝 x₁)
            apply isLittleO_sub_sub_fderiv (E := (E₁ × E₂) × (E₁ × E₂))
              (t := Set.univ) (f := fun (y, z) u => f u z.2) (f' := fun (y, z) u => f₁ u z.2)
            · simpa [nhds_prod_eq] using tendsto_fst.comp tendsto_fst
            · simpa [nhds_prod_eq] using tendsto_fst.comp tendsto_snd
            · simp
            · simpa [continuousWithinAt_univ, ContinuousAt, nhds_prod_eq] using cf₁.comp this
            · simpa [nhds_prod_eq] using this.eventually df₁
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]
      · calc
          fun (y, z) => f y.1 y.2 - f y.1 z.2 - f₂ x₁ x₂ (y.2 - z.2)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.2 - z.2 : _ → E₂) := by
            rw [← nhdsWithin_univ]
            have := (tendsto_fst.comp <| tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := (𝓝 x₁ ×ˢ 𝓝 x₂) ×ˢ (𝓝 x₁ ×ˢ 𝓝 x₂)) (g := 𝓝 x₂)
            apply isLittleO_sub_sub_fderiv (E := (E₁ × E₂) × (E₁ × E₂))
              (t := Set.univ) (f := fun (y, z) v => f y.1 v) (f' := fun (y, z) v => f₂ y.1 v)
            · simpa [nhds_prod_eq] using tendsto_snd.comp tendsto_fst
            · simpa [nhds_prod_eq] using tendsto_snd.comp tendsto_snd
            · simp
            · simpa [continuousWithinAt_univ, ContinuousAt, nhds_prod_eq] using cf₂.comp this
            · simpa [nhds_prod_eq] using this.eventually df₂
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]

theorem hasFDerivWithinAt_uncurry_coprod_of_continuousWithinAt_snd
    [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₂] {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {s₁ : Set E₁} {s₂ : Set E₂} (seg : ∀ᶠ v in 𝓝[s₂] x₂, [x₂ -[ℝ] v] ⊆ s₂)
    {f₁x : E₁ →L[𝕜] F} (df₁x : HasFDerivWithinAt (f · x₂) f₁x s₁ x₁)
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousWithinAt ↿f₂ (s₁ ×ˢ s₂) (x₁, x₂))
    (df₂ : ∀ᶠ y in 𝓝[s₁ ×ˢ s₂] (x₁, x₂), HasFDerivWithinAt (f y.1 ·) (f₂ y.1 y.2) s₂ y.2) :
    HasFDerivWithinAt ↿f (f₁x.coprod (f₂ x₁ x₂)) (s₁ ×ˢ s₂) (x₁, x₂) := by
  unfold ContinuousWithinAt at cf₂
  rw [nhdsWithin_prod_eq] at cf₂ df₂
  rw [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO]
  calc
    fun y => ↿f y - f x₁ x₂ - (f₁x.coprod (f₂ x₁ x₂)) (y.1 - x₁, y.2 - x₂)
    _ = fun y => f y.1 x₂ - f x₁ x₂ - f₁x (y.1 - x₁) + (↿f y - f y.1 x₂ - f₂ x₁ x₂ (y.2 - x₂)) := by
      ext
      rw [ContinuousLinearMap.coprod_apply]
      abel
    _ =o[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] fun y => (y.1 - x₁, y.2 - x₂) := by
      apply IsLittleO.add
      · calc
          _ = (fun y₁ => f y₁ x₂ - f x₁ x₂ - f₁x (y₁ - x₁)) ∘ Prod.fst := by
            rw [Function.comp_def]
          _ =o[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] ((fun y₁ => y₁ - x₁) ∘ Prod.fst) := by
            rw [nhdsWithin_prod_eq]
            apply IsLittleO.comp_fst
            rwa [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO] at df₁x
          _ =O[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] fun y => (y.1 - x₁, y.2 - x₂) := by
            simp [isBigO_of_le]
      · calc
          fun y => f y.1 y.2 - f y.1 x₂ - f₂ x₁ x₂ (y.2 - x₂)
          _ =o[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] fun y => y.2 - x₂ := by
            have := (tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := 𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂) (g := 𝓝[s₂] x₂)
            apply isLittleO_sub_sub_fderiv (E := E₁ × E₂) (f' := fun y v => f₂ y.1 v)
            · simpa [nhdsWithin_prod_eq] using tendsto_nhds_of_tendsto_nhdsWithin tendsto_snd
            · exact tendsto_const_nhds
            · simpa [nhdsWithin_prod_eq] using seg.prod_inr _
            · simpa [ContinuousWithinAt, nhdsWithin_prod_eq] using cf₂.comp this
            · simpa [nhdsWithin_prod_eq] using this.eventually df₂
          _ =O[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] fun y => (y.1 - x₁, y.2 - x₂) := by
            simp [isBigO_of_le]
