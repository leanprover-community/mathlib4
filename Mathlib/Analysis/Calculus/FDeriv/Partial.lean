/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

Results in this file relate the partial derivatives of a bivariate function to its differentiability
in the product space.

## Main statements

- `hasStrictFDerivAt_uncurry_coprod`: establishing strict differentiability at a point `u` in the
  product space, this requires that both partial derivatives exist in a neighbourhood of `u` and be
  continuous at `u`.
-/

public section

open Asymptotics Filter
open scoped Convex Topology

theorem isLittleO_sub_sub_fderiv
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], dist (f' χ z) φ < ε := by
    rw [Metric.tendsto_nhds] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If a bivariate function `f` has partial derivatives `f₁` and `f₂` in a neighbourhood of a point
`(u₁, u₂)` and if they are continuous at that point then the uncurried function `↿f` is strictly
differentiable there with its derivative mapping `(z₁, z₂)` to `f₁ u₁ u₂ z₁ + f₂ u₁ u₂ z₂`. -/
theorem hasStrictFDerivAt_uncurry_coprod
    [IsRCLikeNormedField 𝕜] {u : E₁ × E₂} {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[𝕜] F}
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f · v.2) (↿f₁ v) v.1)
    (df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f v.1 ·) (↿f₂ v) v.2) (cf₁ : ContinuousAt ↿f₁ u)
    (cf₂ : ContinuousAt ↿f₂ u) : HasStrictFDerivAt ↿f ((↿f₁ u).coprod (↿f₂ u)) u := by
  rw [hasStrictFDerivAt_iff_isLittleO]
  unfold ContinuousAt at cf₁ cf₂
  rw [nhds_prod_eq] at df₁ df₂ cf₁ cf₂
  calc
    fun (v, w) => f v.1 v.2 - f w.1 w.2 - ((↿f₁ u).coprod (↿f₂ u)) (v - w)
    _ = fun (v, w) => (f v.1 w.2 - f w.1 w.2 - ↿f₁ u (v.1 - w.1))
          + (f v.1 v.2 - f v.1 w.2 - ↿f₂ u (v.2 - w.2)) := by
      ext
      dsimp only [ContinuousLinearMap.coprod_apply]
      abel
    _ =o[𝓝 (u, u)] fun (v, w) => v - w := by
      let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
      rw [nhds_prod_eq, nhds_prod_eq]
      apply IsLittleO.add
      · calc
          fun (v, w) => f v.1 w.2 - f w.1 w.2 - ↿f₁ u (v.1 - w.1)
          _ =o[(𝓝 u.1 ×ˢ 𝓝 u.2) ×ˢ (𝓝 u.1 ×ˢ 𝓝 u.2)] (fun (v, w) => v.1 - w.1 : _ → E₁) := by
            have h := tendsto_snd.prodMk <| tendsto_snd.comp <| tendsto_snd.comp <|
              tendsto_fst (f := (𝓝 u.1 ×ˢ 𝓝 u.2) ×ˢ (𝓝 u.1 ×ˢ 𝓝 u.2)) (g := 𝓝 u.1)
            let : NormedSpace ℝ E₁ := RestrictScalars.normedSpace ℝ 𝕜 E₁
            apply isLittleO_sub_sub_fderiv (α := (E₁ × E₂) × (E₁ × E₂))
              (f := fun (v, w) x => f x w.2) (f' := fun (v, w) x => f₁ x w.2)
              (tendsto_fst.comp tendsto_fst) (tendsto_fst.comp tendsto_snd)
            · simpa using h.eventually df₁
            · simpa using cf₁.comp h
          _ =O[(𝓝 u.1 ×ˢ 𝓝 u.2) ×ˢ (𝓝 u.1 ×ˢ 𝓝 u.2)] (fun (v, w) => v - w : _ → E₁ × E₂) := by
            simp [isBigO_of_le]
      · calc
          fun (v, w) => f v.1 v.2 - f v.1 w.2 - ↿f₂ u (v.2 - w.2)
          _ =o[(𝓝 u.1 ×ˢ 𝓝 u.2) ×ˢ (𝓝 u.1 ×ˢ 𝓝 u.2)] (fun (v, w) => v.2 - w.2 : _ → E₂) := by
            have h := (tendsto_fst.comp <| tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := (𝓝 u.1 ×ˢ 𝓝 u.2) ×ˢ (𝓝 u.1 ×ˢ 𝓝 u.2)) (g := 𝓝 u.2)
            let : NormedSpace ℝ E₂ := RestrictScalars.normedSpace ℝ 𝕜 E₂
            apply isLittleO_sub_sub_fderiv (f' := fun (v, w) y => f₂ v.1 y)
              (tendsto_snd.comp tendsto_fst) (tendsto_snd.comp tendsto_snd)
            · simpa using h.eventually df₂
            · simpa using cf₂.comp h
          _ =O[(𝓝 u.1 ×ˢ 𝓝 u.2) ×ˢ (𝓝 u.1 ×ˢ 𝓝 u.2)] (fun (v, w) => v - w : _ → E₁ × E₂) := by
            simp [isBigO_of_le]

end
