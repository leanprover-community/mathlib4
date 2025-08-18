/-
Copyright (c) 2025 Igor Khavkine, A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine, A Tucker
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

Results in this file relate the partial derivatives of a bivariate function to its differentiability
in the product space.

## Main statements

* `hasStrictFDerivAt_uncurry_coprod`: establishing strict differentiability at a point `x` in the
  product space, this requires that both partial derivatives exist in a neighbourhood of `x` and be
  continuous at `x`.

* `hasFDerivWithinAt_uncurry_coprod_of_continuousWithinAt_snd`: this weaker result requires that
  both partial derivatives exist, but only the second need exist in a neighbourhood of `x` (and be
  continuous at `x`).

* `HasFDerivWithinAt.partial_fst` , `HasFDerivWithinAt.partial_snd`: if `f` is differentiable
   with derivative `f' x` at `x`, then the partial derivatives of `(f ∘ (x.1, ·))`
   and `(f ∘ (·, x.2))` are respectively `(f' x) ∘L (.inl 𝕜 E₁ E₂)` and
   `(f' x) ∘L (.inr 𝕜 E₁ E₂)`. If `f'` is continuous, then continuity can be obtained by
   by combining `Continuous(|At|On|WithinAt).clm_comp` and `Continuous(|At|On|WithinAt)_const`.

* `hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open` : a weak sufficient condition
  for differeniability of `f` at `x = (x₁,x₂)` is that, say, the first derivative (within set `s₁`)
  `f₁x` exists at `x`, while the second partial derivative `f₂ x` exists and is jointly
  continuous at `x` in the product set `s₁ ×ˢ s₂` where `s₂` is open, with the derivative given by
  `f'x = f₁x.coprod (f₂ x)`. `hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open` has
  the roles of the partial derivatives reversed.

  The proofs follow §8.9.1 from Dieudonné's *Foundations of Modern Analysis* (1969).

* `hasFDerivWithinAt_continuous(On|WithinAt)_of_partial_continuous(On|WithinAt)_open`: when
  both partial derivatives exist and are continuous on (or at `x` in) an open set `s`, this more
  convenient theorem directly deduces continous differentiability on (or at `x` in) `s`.
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
    [IsRCLikeNormedField 𝕜] {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
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

/-- If a bivariate function `f` has partial derivatives `f₁x` at `(x₁, x₂)` and `f₂` in a
neighbourhood of `(x₁, x₂)`, continuous there, then the uncurried function `↿f` is differentiable at
`(x₁, x₂)` with its derivative mapping `(h₁, h₂)` to `f₁x h₁ + f₂ x₁ x₂ h₂`. -/
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
            have h := (tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := 𝓝[s₁] x₁ ×ˢ 𝓝[s₂] x₂) (g := 𝓝[s₂] x₂)
            apply isLittleO_sub_sub_fderiv (f' := fun y v => f₂ y.1 v)
              s₂ (by simpa [nhdsWithin_prod_eq] using seg.prod_inr _)
            · simpa [nhdsWithin_prod_eq] using tendsto_nhds_of_tendsto_nhdsWithin tendsto_snd
            · exact tendsto_const_nhds
            · simpa [nhdsWithin_prod_eq] using cf₂.comp h
            · simpa [nhdsWithin_prod_eq] using h.eventually df₂
          _ =O[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] fun y => (y.1 - x₁, y.2 - x₂) := by
            simp [isBigO_of_le]

open Set Function Metric

section PartialFDeriv

/-- Differentiable implies also that the first partial derivative exists. -/
theorem HasFDerivWithinAt.partial_fst
  {f : E₁ × E₂ → F} {f' : E₁ × E₂ → E₁ × E₂ →L[𝕜] F}
  {s₁ : Set E₁} {s₂ : Set E₂}
  {x : E₁ × E₂} (hx : x ∈ s₁ ×ˢ s₂)
  (hf : HasFDerivWithinAt f (f' x) (s₁ ×ˢ s₂) x) :
    HasFDerivWithinAt (f ∘ (·, x.2)) (f' x ∘L .inl ..) s₁ x.1 := by
  have hleft (u:E₁) := HasFDerivWithinAt.prodMk
    (hasFDerivWithinAt_id (𝕜 := 𝕜) u s₁)
    (hasFDerivWithinAt_const x.2 u s₁)
  convert HasFDerivWithinAt.comp x.1 (hf) (hleft x.1)
    (fun u hu => mem_prod.mpr ⟨hu, (mem_prod.mp hx).right⟩)

/-- Differentiable implies also that the second partial derivative exists. -/
theorem HasFDerivWithinAt.partial_snd
  {f : E₁ × E₂ → F} {f' : E₁ × E₂ → E₁ × E₂ →L[𝕜] F}
  {s₁ : Set E₁} {s₂ : Set E₂}
  {x : E₁ × E₂} (hx : x ∈ s₁ ×ˢ s₂)
  (hf : HasFDerivWithinAt f (f' x) (s₁ ×ˢ s₂) x) :
    HasFDerivWithinAt (f ∘ (x.1, ·)) (f' x ∘L .inr ..) s₂ x.2 := by
  have hright (v:E₂) := HasFDerivWithinAt.prodMk
    (hasFDerivWithinAt_const x.1 v s₂)
    (hasFDerivWithinAt_id (𝕜 := 𝕜) v s₂)
  convert HasFDerivWithinAt.comp x.2 (hf) (hright x.2)
    (fun v hv => mem_prod.mpr ⟨(mem_prod.mp hx).left, hv⟩)

/-- If a function `f : E₁ × E₂ → F` has a first partial derivative (within set `s₁`) `f₁x` at `x`
and has a second partial derivative (within open set `s₂`) `f₂` continuous on `s₁ ×ˢ s₂`,
then `f` has a derivative at `x`, with the derivative given by `f'x = f₁x.coprod (f₂ x)`.

See `hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open` for the order of derivatives
swapped.
-/
theorem hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
  [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₂]
  {f : E₁ × E₂ → F} {s₁ : Set E₁} {s₂ : Set E₂} {x : E₁ × E₂}
  (hx : x ∈ s₁ ×ˢ s₂) (hs₂ : IsOpen s₂)
  {f₁x : E₁ →L[𝕜] F} {f₂ : E₁ × E₂ → E₂ →L[𝕜] F}
  (hf₂_cont : ContinuousWithinAt f₂ (s₁ ×ˢ s₂) x)
  (hf₁x : HasFDerivWithinAt (f ∘ (·, x.2)) f₁x s₁ x.1)
  (hf₂ : ∀ y ∈ s₁ ×ˢ s₂, HasFDerivAt (f ∘ (y.1, ·)) (f₂ y) y.2) :
    HasFDerivWithinAt f (f₁x.coprod (f₂ x)) (s₁ ×ˢ s₂) x := by
  replace hx : _ ∧ _ := ⟨mem_prod.mp hx, hx⟩
  simp only at hx
  -- rewrite derivatives as limits using norms
  simp only [hasFDerivWithinAt_iff_tendsto, tendsto_nhdsWithin_nhds, dist_eq_norm] at ⊢ hf₁x
  simp only [ContinuousLinearMap.coprod_apply, sub_zero, norm_mul, norm_inv,
    norm_norm] at ⊢ hf₁x
  simp only [Metric.continuousWithinAt_iff, dist_eq_norm] at hf₂_cont
  -- get a target ε' and immediately shrink it to ε for convenice
  intro ε' hε'
  rw [show ε' = (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 by ring]
  have hε := half_pos (half_pos (half_pos hε'))
  set ε := ε' / 2 / 2 / 2
  -- get δx₁ from x₁-differentiability
  -- get δx₂ from continuity of x₂-derivative
  -- get δs₂ is constrained by the possibly small size of s₂
  replace ⟨δx₁, hδx₁, hf₁x⟩ := hf₁x ε hε
  replace ⟨δx₂, hδx₂, hf₂_cont⟩ := hf₂_cont ε hε
  obtain ⟨δs₂, hδs₂⟩ := isOpen_iff.mp hs₂ x.2 hx.1.2
  use (min δx₁ (min δx₂ δs₂)) -- derive desired δ
  refine ⟨?pos, ?_⟩
  case pos => exact lt_min hδx₁ (lt_min hδx₂ hδs₂.1) -- positivity of δ
  -- get working point (y₁,x₂) ∈ E₁ × E₂ within δ distance of x
  intro (y₁,y₂) hs₁s₂ hδ
  replace hs₁s₂ : _ ∧ _ := ⟨mem_prod.mp hs₁s₂, hs₁s₂⟩
  simp only at hs₁s₂
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [mul_comm]
  -- simplify norm conditions into bounds on ‖y₁-x.1‖ and ‖y₂-x.2‖
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hδ
  simp only [lt_inf_iff, sup_lt_iff] at hδ
  obtain ⟨⟨h₁δx₁, h₂δx₁⟩, ⟨⟨h₁δx₂, h₂δx₂⟩, ⟨h₁δs₂, h₂δs₂⟩⟩⟩ := hδ
  -- rewrite desired variation in f for easier estimation
  have hf := calc
    f (y₁,y₂) - f x - (f₁x (y₁ - x.1) + (f₂ x) (y₂ - x.2))
      = f (y₁,y₂) - f (y₁,x.2)
      + f (y₁,x.2) - f (x.1,x.2) - (f₁x (y₁ - x.1) + (f₂ x) (y₂ - x.2)) := by
        abel
    _ = f (y₁,y₂) - f (y₁,x.2) - (f₂ x) (y₂ - x.2)
      + f (y₁,x.2) - f (x.1,x.2) - f₁x (y₁ - x.1) := by
        abel
    _ = f (y₁,y₂) - f (y₁,x.2) - (f₂ (y₁,x.2)) (y₂ - x.2)
      + (f₂ (y₁,x.2)) (y₂ - x.2) - (f₂ x) (y₂ - x.2)
      + f (y₁,x.2) - f (x.1,x.2) - f₁x (y₁ - x.1) := by
        abel
    _ = f (y₁,y₂) - f (y₁,x.2) - (f₂ (y₁,x.2)) (y₂ - x.2)
      + (f₂ (y₁,x.2) - f₂ x) (y₂ - x.2)
      + f (y₁,x.2) - f (x.1,x.2) - f₁x (y₁ - x.1) := by
        rw [ContinuousLinearMap.sub_apply]
        abel
    _ = f (y₁,y₂) - f (y₁,x.2) - (f₂ (y₁,x.2)) (y₂ - x.2)
      + (f₂ (y₁,x.2) - f₂ x) (y₂ - x.2)
      + (f (y₁,x.2) - f (x.1,x.2) - f₁x (y₁ - x.1)) := by
        abel
  -- set up the hypotheses and use the inequality version of the Mean Value Theorem
  have mvt_diff : ∀ v ∈ ball x.2 (min δx₂ δs₂),
      HasFDerivWithinAt (f ∘ (y₁,·)) (f₂ (y₁,v)) (ball x.2 (min δx₂ δs₂)) v := by
    intro v hv
    rw [mem_ball_iff_norm, lt_min_iff] at hv
    apply (hf₂ (y₁,v) (mem_prod.mpr ⟨hs₁s₂.1.1, _⟩)).hasFDerivWithinAt.mono
    · calc
        ball x.2 (min δx₂ δs₂)
          ⊆ ball x.2 δs₂ := ball_subset_ball (min_le_right _ _)
        _ ⊆ s₂ := hδs₂.2
    · exact mem_of_subset_of_mem hδs₂.2 (mem_ball_iff_norm.mpr hv.2)
  have mvt_bound : ∀ v ∈ ball x.2 (min δx₂ δs₂), ‖f₂ (y₁,v) - f₂ (y₁,x.2)‖ ≤ ε + ε := by
    intro v hv
    rw [mem_ball_iff_norm, lt_min_iff] at hv
    rw [← dist_eq_norm]
    apply (dist_triangle _ (f₂ x) _).trans
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (f₂ x) _]
    have hy₁v : ‖(y₁,v) - x‖ < δx₂ := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sup_lt_iff]
      exact ⟨h₁δx₂, hv.1⟩
    have hy₁x2 : ‖(y₁,x.2) - x‖ < δx₂ := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
        sup_of_le_left]
      exact h₁δx₂
    apply add_le_add (hf₂_cont _ hy₁v).le (hf₂_cont _ hy₁x2).le
    · apply mem_prod.mpr ⟨hs₁s₂.1.1, _⟩
      exact mem_of_subset_of_mem hδs₂.2 (mem_ball_iff_norm.mpr hv.2)
    · exact mem_prod.mpr ⟨hs₁s₂.1.1, hx.1.2⟩
  have mvt {a b} (ha : a ∈ _) (hb : b ∈ _) :=
    -- inequality version of Mean Value Theorem
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      mvt_diff
      mvt_bound
      (convex_ball x.2 (min δx₂ δs₂)) ha hb
  simp only [comp_apply] at mvt
  -- use the calculation above and start applying norms and estimates on the goal, term by term
  rw [hf]
  replace hf := calc
    ‖f (y₁,y₂) - f (y₁,x.2) - (f₂ (y₁,x.2)) (y₂ - x.2)
      + (f₂ (y₁,x.2) - f₂ x) (y₂ - x.2)
      + (f (y₁,x.2) - f (x.1,x.2) - f₁x (y₁ - x.1))‖
      ≤ ‖f (y₁,y₂) - f (y₁,x.2) - (f₂ (y₁,x.2)) (y₂ - x.2)‖
      + ‖(f₂ (y₁,x.2) - f₂ x) (y₂ - x.2)‖
      + ‖(f (y₁,x.2) - f (x.1,x.2) - f₁x (y₁ - x.1))‖ := norm_add₃_le
    _ ≤ (ε + ε) * ‖y₂ - x.2‖
      + ‖(f₂ (y₁,x.2) - f₂ x)‖ * ‖y₂ - x.2‖
      + ε * ‖y₁ - x.1‖ := by
        apply add_le_add (add_le_add _ _) _ -- compare term by term
        · exact mvt -- Mean Value estimate
            (mem_ball_self (lt_min hδx₂ hδs₂.1))
            (mem_ball_iff_norm.mpr (lt_min h₂δx₂ h₂δs₂))
        · exact ContinuousLinearMap.le_opNorm _ _ -- operator norm estimate
        · rw [mul_comm]
          by_cases hy₁nx : 0 < ‖y₁ - x.1‖
          case neg => -- handle trivial y₁ = x.1 case
            replace hy₁nx := (not_lt.mp hy₁nx).antisymm (norm_nonneg _)
            have hy₁ny := eq_of_sub_eq_zero (norm_eq_zero.mp hy₁nx)
            repeat rw [hy₁nx, hy₁ny]
            simp only [Prod.mk.eta, sub_self, map_zero, norm_zero, zero_mul, le_refl]
          case pos =>
            apply (inv_mul_le_iff₀ hy₁nx).mp
            exact (hf₁x hs₁s₂.1.1 h₁δx₁).le -- apply differentiability estimate
    _ ≤ ε * ‖y₂ - x.2‖ + ε * ‖y₂ - x.2‖ + ε * ‖y₂ - x.2‖ + ε * ‖y₁ - x.1‖ := by
        rw [add_mul]
        apply add_le_add (add_le_add le_rfl _) le_rfl
        apply mul_le_mul (hf₂_cont _ _).le le_rfl (norm_nonneg (y₂ - x.2)) hε.le
        · exact (mem_prod.mpr ⟨hs₁s₂.1.1, hx.1.2⟩)
        · simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
          sup_of_le_left, h₁δx₂]
  -- now apply the estimate hf to the goal
  apply (mul_le_mul_of_nonneg_right hf (by simp only [inv_nonneg, norm_nonneg])).trans_lt _
  -- it remains only to simplify the inequality term by term and compare coefficients
  simp only [add_mul, mul_assoc]
  apply add_lt_add (add_lt_add (add_lt_add _ _) _)
  all_goals
    apply (mul_lt_mul_left hε).mpr
    refine LE.le.trans_lt ?_ (one_lt_two)
    rw [mul_comm]
    apply inv_mul_le_of_le_mul₀ (norm_nonneg _) zero_le_one
    simp only [mul_one, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
    first | exact le_max_right _ _ | exact le_max_left _ _

/-- If a function `f : E₁ × E₂ → F` has a second partial derivative (within set `s₂`) `f₂x` at `x`
and has a first partial derivative (within open set `s₁`) `f₁` continuous on `s₁ ×ˢ s₂`,
then `f` has a derivative at `x`, with the derivative given by `f'x = (f₁ x).coprod f₂x`.

See `hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open` for the order of derivatives
swapped.
-/
theorem hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open
  [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₁]
  {f : E₁ × E₂ → F} {s₁ : Set E₁} {s₂ : Set E₂} {x : E₁ × E₂}
  (hx : x ∈ s₁ ×ˢ s₂) (hs₁ : IsOpen s₁)
  {f₁ : E₁ × E₂ → E₁ →L[𝕜] F} {f₂x : E₂ →L[𝕜] F}
  (hf₁_cont : ContinuousWithinAt f₁ (s₁ ×ˢ s₂) x)
  (hf₁ : ∀ y ∈ s₁ ×ˢ s₂, HasFDerivAt (f ∘ (·, y.2)) (f₁ y) y.1)
  (hf₂x : HasFDerivWithinAt (f ∘ (x.1, ·)) f₂x s₂ x.2) :
    HasFDerivWithinAt f ((f₁ x).coprod f₂x) (s₁ ×ˢ s₂) x := by
  have hmt_s₁s₂ := mapsTo_swap_prod s₁ s₂
  have hmt_s₂s₁ := mapsTo_swap_prod s₂ s₁
  have hf₁_swap_cont := (x.swap_swap ▸ hf₁_cont).comp
    continuous_swap.continuousWithinAt
    hmt_s₂s₁
  -- exchange `E₁` and `E₂` to use a previous result
  have hswap := hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
    (f := f ∘ Prod.swap)
    (x := x.swap)
    hx.symm hs₁
    hf₁_swap_cont
    hf₂x
    (fun y hy => (hf₁ y.swap (hmt_s₂s₁ hy)))
  -- exchange `E₁` and `E₂` back in the result to satisfy the goal
  let cle_swap := ContinuousLinearEquiv.prodComm 𝕜 E₁ E₂
  convert hswap.comp x (cle_swap.hasFDerivWithinAt) hmt_s₁s₂
  unfold cle_swap
  simp only [Prod.swap_swap, comp_apply, ContinuousLinearMap.coprod_comp_prodComm]

/-- If a function `f : E₁ × E₂ → F` has partial derivative `f₁` or `f₂` on an open set `s`,
and they are continuous at `x ∈ s`, then `f` is continously differentiable at `x`, with
the derivative given by `f' x = (f₁ x).coprod (f₂ x)`.
-/
theorem hasFDerivWithinAt_continuousWithinAt_of_partial_continuousWithinAt_open
  --NB: [NormedSpace ℝ E₁] is not needed because the proof eventually applies
  --    the Mean Value Theorem only in the E₂ direction. But it could have been
  --    the other way around and it is odd to not have symmetry in the hypotheses
  [IsRCLikeNormedField 𝕜] /-[NormedSpace ℝ E₁]-/ [NormedSpace ℝ E₂]
  {f : E₁ × E₂ → F} {s : Set (E₁ × E₂)} (hs : IsOpen s) {x : E₁ × E₂} (hx : x ∈ s)
  {f₁ : E₁ × E₂ → E₁ →L[𝕜] F} {f₂ : E₁ × E₂ → E₂ →L[𝕜] F}
  (hf₁_cont : ContinuousWithinAt f₁ s x) (hf₂_cont : ContinuousWithinAt f₂ s x)
  (hf₁ : ∀ y ∈ s, HasFDerivAt (f ∘ (·, y.2)) (f₁ y) y.1)
  (hf₂ : ∀ y ∈ s, HasFDerivAt (f ∘ (y.1, ·)) (f₂ y) y.2) :
    ContinuousWithinAt (fun y => (f₁ y).coprod (f₂ y)) s x
    ∧ HasFDerivAt f ((f₁ x).coprod (f₂ x)) x := by
  refine ⟨?cont, ?diff⟩
  case cont =>
    -- combine continuity of partial to get continuity of total derivative
    exact hf₁_cont.continuousLinearMapCoprod hf₂_cont
  case diff =>
    -- first restrict all properties to a product neighborhood of x
    obtain ⟨s₁,s₂,hs₁,hs₂,hx1,hx2,hs₁s₂⟩ := isOpen_prod_iff.mp hs x.1 x.2 hx
    have hs₁s₂n : s₁ ×ˢ s₂ ∈ nhds x := IsOpen.mem_nhds (hs₁.prod hs₂) (mem_prod.mpr ⟨hx1, hx2⟩)
    have hs₁s (y : E₁ × E₂) (hy : y ∈ s₁ ×ˢ s₂) : s₁ ⊆ ((·,y.2) ⁻¹' s) := by
      apply HasSubset.Subset.trans _ (preimage_mono hs₁s₂)
      rw [mk_preimage_prod_left (mem_prod.mpr hy).2]
    have hs₂s (y : E₁ × E₂) (hy : y ∈ s₁ ×ˢ s₂) : s₂ ⊆ ((y.1,·) ⁻¹' s) := by
      apply HasSubset.Subset.trans _ (preimage_mono hs₁s₂)
      rw [mk_preimage_prod_right (mem_prod.mpr hy).1]
    replace hf₂_cont := hf₂_cont.mono hs₁s₂
    -- now apply the weaker criteria to get differentiability
    apply HasFDerivWithinAt.hasFDerivAt _ hs₁s₂n
    apply hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
      ⟨hx1,hx2⟩ hs₂
      hf₂_cont
      _ _
    · exact (hf₁ x hx).hasFDerivWithinAt.mono (hs₁s x ⟨hx1,hx2⟩)
    · exact (fun y hy => (hf₂ y (mem_of_subset_of_mem hs₁s₂ hy)))

/-- If a function `f : E₁ × E₂ → F` has partial derivative `f₁` or `f₂` continuous
on an open set `s`, then `f` is continously differentiable on this set, with
the derivative given by `f' = f₁.coprod f₂`.
-/
theorem hasFDerivWithinAt_continuousOn_of_partial_continuousOn_open
  --NB: [NormedSpace ℝ E₁] is not needed because the proof eventually applies
  --    the Mean Value Theorem only in the E₂ direction. But it could have been
  --    the other way around and it is odd to not have symmetry in the hypotheses
  [IsRCLikeNormedField 𝕜] /-[NormedSpace ℝ E₁]-/ [NormedSpace ℝ E₂]
  {f : E₁ × E₂ → F} {s : Set (E₁ × E₂)} (hs : IsOpen s)
  {f₁ : E₁ × E₂ → E₁ →L[𝕜] F} {f₂ : E₁ × E₂ → E₂ →L[𝕜] F}
  (hf₁_cont : ContinuousOn f₁ s) (hf₂_cont : ContinuousOn f₂ s)
  (hf₁ : ∀ y ∈ s, HasFDerivAt (f ∘ (·, y.2)) (f₁ y) y.1)
  (hf₂ : ∀ y ∈ s, HasFDerivAt (f ∘ (y.1, ·)) (f₂ y) y.2) :
    ContinuousOn (fun y => (f₁ y).coprod (f₂ y)) s
    ∧ ∀ y ∈ s, HasFDerivAt f ((f₁ y).coprod (f₂ y)) y := by
  simp only [ContinuousOn, ← forall₂_and]
  intro y hy
  apply hasFDerivWithinAt_continuousWithinAt_of_partial_continuousWithinAt_open
    hs hy
    (hf₁_cont.continuousWithinAt hy) (hf₂_cont.continuousWithinAt hy)
    hf₁ hf₂

end PartialFDeriv
