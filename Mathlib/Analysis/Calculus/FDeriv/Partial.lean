/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

Results in this file relate the partial derivatives of a bivariate function to its differentiability
in the product space.

## Main statements

- `hasStrictFDerivAt_uncurry_coprod`: establishing strict differentiability at a point `x` in the
  product space, this requires that both partial derivatives exist in a neighbourhood of `x` and be
  continuous at `x`.
-/

open Asymptotics Filter
open scoped Convex Topology

theorem isLittleO_sub_sub_fderiv
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {x : E} {y z : α → E} {l : Filter α} {f : α → E → F} {f' : α → E → E →L[𝕜] F} {φ : E →L[𝕜] F}
    (s : Set E := .univ) (seg : ∀ᶠ χ in l, [z χ -[ℝ] y χ] ⊆ s := by simp)
    (hy : Tendsto y l (𝓝 x)) (hz : Tendsto z l (𝓝 x)) (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] x) (𝓝 φ))
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] x, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2) :
    (fun χ => f χ (y χ) - f χ (z χ) - φ (y χ - z χ)) =o[l] (fun χ => y χ - z χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace cf' : ∀ᶠ χ in l, ∀ v ∈ [z χ -[ℝ] y χ], dist (f' χ v) φ < ε := by
    rw [Metric.tendsto_nhds] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hz hy seg
  replace df' : ∀ᶠ χ in l, ∀ v ∈ [z χ -[ℝ] y χ], HasFDerivWithinAt (f χ) (f' χ v) s v :=
    df'.segment_of_prod_nhdsWithin hz hy seg
  filter_upwards [seg, cf', df'] with χ seg cf' df'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun v hv => (df' v hv).mono seg) (fun v hv => (cf' v hv).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If a bivariate function `f` has partial derivatives `f₁` and `f₂` in a neighbourhood of a point
`(x₁, x₂)` and if they are continuous at that point then the uncurried function `↿f` is strictly
differentiable there with its derivative mapping `(h₁, h₂)` to `f₁ x₁ x₂ h₁ + f₂ x₁ x₂ h₂`. -/
theorem hasStrictFDerivAt_uncurry_coprod
    [IsRCLikeNormedField 𝕜] {x₁ : E₁} {x₂ : E₂} {f : E₁ → E₂ → F}
    {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} (cf₁ : ContinuousAt ↿f₁ (x₁, x₂))
    (df₁ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f · y.2) (f₁ y.1 y.2) y.1)
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousAt ↿f₂ (x₁, x₂))
    (df₂ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f y.1 ·) (f₂ y.1 y.2) y.2) :
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
      let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
      apply IsLittleO.add
      · calc
          fun (y, z) => f y.1 z.2 - f z.1 z.2 - f₁ x₁ x₂ (y.1 - z.1)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.1 - z.1 : _ → E₁) := by
            have h := tendsto_snd.prodMk <| tendsto_snd.comp <| tendsto_snd.comp <|
              tendsto_fst (f := (𝓝 x₁ ×ˢ 𝓝 x₂) ×ˢ (𝓝 x₁ ×ˢ 𝓝 x₂)) (g := 𝓝 x₁)
            let : NormedSpace ℝ E₁ := RestrictScalars.normedSpace ℝ 𝕜 E₁
            apply isLittleO_sub_sub_fderiv (α := (E₁ × E₂) × (E₁ × E₂))
              (f := fun (y, z) u => f u z.2) (f' := fun (y, z) u => f₁ u z.2)
            · simpa [nhds_prod_eq] using tendsto_fst.comp tendsto_fst
            · simpa [nhds_prod_eq] using tendsto_fst.comp tendsto_snd
            · simpa [nhds_prod_eq] using cf₁.comp h
            · simpa [nhds_prod_eq] using h.eventually df₁
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]
      · calc
          fun (y, z) => f y.1 y.2 - f y.1 z.2 - f₂ x₁ x₂ (y.2 - z.2)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.2 - z.2 : _ → E₂) := by
            have h := (tendsto_fst.comp <| tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := (𝓝 x₁ ×ˢ 𝓝 x₂) ×ˢ (𝓝 x₁ ×ˢ 𝓝 x₂)) (g := 𝓝 x₂)
            let : NormedSpace ℝ E₂ := RestrictScalars.normedSpace ℝ 𝕜 E₂
            apply isLittleO_sub_sub_fderiv (α := (E₁ × E₂) × (E₁ × E₂))
              (f := fun (y, z) v => f y.1 v) (f' := fun (y, z) v => f₂ y.1 v)
            · simpa [nhds_prod_eq] using tendsto_snd.comp tendsto_fst
            · simpa [nhds_prod_eq] using tendsto_snd.comp tendsto_snd
            · simpa [nhds_prod_eq] using cf₂.comp h
            · simpa [nhds_prod_eq] using h.eventually df₂
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]
