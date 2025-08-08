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
   with derivative `f' z` at `z`, then the partial derivatives of `(f ∘ (z.1, ·))`
   and `(f ∘ (·, z.2))` are respectively `(f' z) ∘L (.inl 𝕜 E F)` and
   `(f' z) ∘L (.inr 𝕜 E F)`. If `f'` is continuous, then continuity can be obtained by
   by combining `Continuous(|At|On|WithinAt).clm_comp` and `Continuous(|At|On|WithinAt)_const`.

* `hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open` : a weak sufficient condition
  for differeniability of `f` at `z = (x,y)` is that, say, the first derivative (within set `s`)
  `f'xz` exists at `z`, while the second partial derivative `f'y z` exists and is jointly
  continuous at `z` in the product set `s ×ˢ t` where `t` is open, with the derivative given by
  `f'z = f'xz.coprod (f'y z)`. `hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open` has
  the roles of the partial derivatives reversed.

  The proofs follow §9.8.1 from Dieudonné's *Foundations of Modern Analysis* (1969).

* `hasFDerivWithinAt_continuous(On|WithinAt)_of_partial_continuous(On|WithinAt)_open`: when
  both partial derivatives exist and are continuous on (or at `z` in) an open set `u`, this more
  convenient theorem directly deduces continous differentiability on (or at `z` in) `u`.
-/

open Asymptotics Filter
open scoped Convex Topology

section aux

variable {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
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

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

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

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 F]

/-- If a bivariate function `f` has partial derivatives `f₁` and `f₂` in a neighbourhood of a point
`(x₁, x₂)` and if they are continuous at that point then the uncurried function `↿f` is strictly
differentiable there with its derivative mapping `(h₁, h₂)` to `f₁ x₁ x₂ h₁ + f₂ x₁ x₂ h₂`. -/
theorem hasStrictFDerivAt_uncurry_coprod {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
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
            rw [← nhdsWithin_univ]
            have h := tendsto_snd.prodMk <| tendsto_snd.comp <| tendsto_snd.comp <|
              tendsto_fst (f := (𝓝 x₁ ×ˢ 𝓝 x₂) ×ˢ (𝓝 x₁ ×ˢ 𝓝 x₂)) (g := 𝓝 x₁)
            let : NormedSpace ℝ E₁ := RestrictScalars.normedSpace ℝ 𝕜 E₁
            apply isLittleO_sub_sub_fderiv (E := (E₁ × E₂) × (E₁ × E₂))
              (t := Set.univ) (f := fun (y, z) u => f u z.2) (f' := fun (y, z) u => f₁ u z.2)
            · simpa [nhds_prod_eq] using tendsto_fst.comp tendsto_fst
            · simpa [nhds_prod_eq] using tendsto_fst.comp tendsto_snd
            · simp
            · simpa [continuousWithinAt_univ, ContinuousAt, nhds_prod_eq] using cf₁.comp h
            · simpa [nhds_prod_eq] using h.eventually df₁
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]
      · calc
          fun (y, z) => f y.1 y.2 - f y.1 z.2 - f₂ x₁ x₂ (y.2 - z.2)
          _ =o[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y.2 - z.2 : _ → E₂) := by
            rw [← nhdsWithin_univ]
            have h := (tendsto_fst.comp <| tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := (𝓝 x₁ ×ˢ 𝓝 x₂) ×ˢ (𝓝 x₁ ×ˢ 𝓝 x₂)) (g := 𝓝 x₂)
            let : NormedSpace ℝ E₂ := RestrictScalars.normedSpace ℝ 𝕜 E₂
            apply isLittleO_sub_sub_fderiv (E := (E₁ × E₂) × (E₁ × E₂))
              (t := Set.univ) (f := fun (y, z) v => f y.1 v) (f' := fun (y, z) v => f₂ y.1 v)
            · simpa [nhds_prod_eq] using tendsto_snd.comp tendsto_fst
            · simpa [nhds_prod_eq] using tendsto_snd.comp tendsto_snd
            · simp
            · simpa [continuousWithinAt_univ, ContinuousAt, nhds_prod_eq] using cf₂.comp h
            · simpa [nhds_prod_eq] using h.eventually df₂
          _ =O[𝓝 ((x₁, x₂), (x₁, x₂))] (fun (y, z) => y - z : _ → E₁ × E₂) := by
            simp [isBigO_of_le]

/-- If a bivariate function `f` has partial derivatives `f₁x` at `(x₁, x₂)` and `f₂` in a
neighbourhood of `(x₁, x₂)`, continuous there, then the uncurried function `↿f` is differentiable at
`(x₁, x₂)` with its derivative mapping `(h₁, h₂)` to `f₁x h₁ + f₂ x₁ x₂ h₂`. -/
theorem hasFDerivWithinAt_uncurry_coprod_of_continuousWithinAt_snd
    [NormedSpace ℝ E₂] {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
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
            apply isLittleO_sub_sub_fderiv (E := E₁ × E₂) (f' := fun y v => f₂ y.1 v)
            · simpa [nhdsWithin_prod_eq] using tendsto_nhds_of_tendsto_nhdsWithin tendsto_snd
            · exact tendsto_const_nhds
            · simpa [nhdsWithin_prod_eq] using seg.prod_inr _
            · simpa [ContinuousWithinAt, nhdsWithin_prod_eq] using cf₂.comp h
            · simpa [nhdsWithin_prod_eq] using h.eventually df₂
          _ =O[𝓝[s₁ ×ˢ s₂] (x₁, x₂)] fun y => (y.1 - x₁, y.2 - x₂) := by
            simp [isBigO_of_le]

open Set Function Metric

section PartialFDeriv

/-- Differentiable implies also that the first partial derivative exists. -/
theorem HasFDerivWithinAt.partial_fst
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {f' : E × F → E × F →L[𝕜] G}
  {s : Set E} {t : Set F}
  {z : E × F} (hz : z ∈ s ×ˢ t)
  (hf : HasFDerivWithinAt f (f' z) (s ×ˢ t) z) :
      HasFDerivWithinAt (f ∘ (·, z.2)) (f' z ∘L .inl ..) s z.1 := by
    have hleft (x:E) := HasFDerivWithinAt.prodMk
      (hasFDerivWithinAt_id (𝕜 := 𝕜) x s)
      (hasFDerivWithinAt_const z.2 x s)
    convert HasFDerivWithinAt.comp z.1 (hf) (hleft z.1)
      (fun x hx => mem_prod.mpr ⟨hx, (mem_prod.mp hz).right⟩)

/-- Differentiable implies also that the second partial derivative exists. -/
theorem HasFDerivWithinAt.partial_snd
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {f' : E × F → E × F →L[𝕜] G}
  {s : Set E} {t : Set F}
  {z : E × F} (hz : z ∈ s ×ˢ t)
  (hf : HasFDerivWithinAt f (f' z) (s ×ˢ t) z) :
      HasFDerivWithinAt (f ∘ (z.1, ·)) (f' z ∘L .inr ..) t z.2 := by
    have hright (y:F) := HasFDerivWithinAt.prodMk
      (hasFDerivWithinAt_const z.1 y t)
      (hasFDerivWithinAt_id (𝕜 := 𝕜) y t)
    convert HasFDerivWithinAt.comp z.2 (hf) (hright z.2)
      (fun y hy => mem_prod.mpr ⟨(mem_prod.mp hz).left, hy⟩)

/-- If a function `f : E × F → G` has a first partial derivative (within set `s`) `f'xz` at `z`
and has a second partial derivative (within open set `t`) `f'y` continuous on `s ×ˢ t`,
then `f` has a derivative at `z`, with the derivative given by `f'z = f'xz.coprod (f'y z)`.

See `hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open` for the order of derivatives
swapped.
-/
theorem hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {z : E × F}
  (hz : z ∈ s ×ˢ t) (ht : IsOpen t)
  {f'xz : E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'y_cont : ContinuousWithinAt f'y (s ×ˢ t) z)
  (hf'xz : HasFDerivWithinAt (f ∘ (·, z.2)) f'xz s z.1)
  (hf'y : ∀ z' ∈ s ×ˢ t, HasFDerivAt (f ∘ (z'.1, ·)) (f'y z') z'.2) :
    HasFDerivWithinAt f (f'xz.coprod (f'y z)) (s ×ˢ t) z := by
  replace hz : _ ∧ _ := ⟨mem_prod.mp hz, hz⟩
  simp only at hz
  -- rewrite derivatives as limits using norms
  simp only [hasFDerivWithinAt_iff_tendsto, tendsto_nhdsWithin_nhds, dist_eq_norm] at ⊢ hf'xz
  simp only [ContinuousLinearMap.coprod_apply, sub_zero, norm_mul, norm_inv,
    norm_norm] at ⊢ hf'xz
  simp only [Metric.continuousWithinAt_iff, dist_eq_norm] at hf'y_cont
  -- get a target ε' and immediately shrink it to ε for convenice
  intro ε' hε'
  rw [show ε' = (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 by ring]
  have hε := half_pos (half_pos (half_pos hε'))
  set ε := ε' / 2 / 2 / 2
  -- get δx from x-differentiability
  -- get δy from continuity of y-derivative
  -- get δt is constrained by the possibly small size of t
  replace ⟨δx, hδx, hf'xz⟩ := hf'xz ε hε
  replace ⟨δy, hδy, hf'y_cont⟩ := hf'y_cont ε hε
  obtain ⟨δt, hδt⟩ := isOpen_iff.mp ht z.2 hz.1.2
  use (min δx (min δy δt)) -- derive desired δ
  refine ⟨?pos, ?_⟩
  case pos => exact lt_min hδx (lt_min hδy hδt.1) -- positivity of δ
  -- get working point (x,y) ∈ E × F within δ distance of z
  intro (x,y) hst hδ
  replace hst : _ ∧ _ := ⟨mem_prod.mp hst, hst⟩
  simp only at hst
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [mul_comm]
  -- simplify norm conditions into bounds on ‖x-z.1‖ and ‖y-z.2‖
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hδ
  simp only [lt_inf_iff, sup_lt_iff] at hδ
  obtain ⟨⟨hxx, hyx⟩, ⟨⟨hxy, hyy⟩, ⟨hxt, hyt⟩⟩⟩ := hδ
  -- rewrite desired variation in f for easier estimation
  have hf := calc
    f (x,y) - f z - (f'xz (x - z.1) + (f'y z) (y - z.2))
      = f (x,y) - f (x,z.2)
      + f (x,z.2) - f (z.1,z.2) - (f'xz (x - z.1) + (f'y z) (y - z.2)) := by
        abel
    _ = f (x,y) - f (x,z.2) - (f'y z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1) := by
        abel
    _ = f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2)) (y - z.2) - (f'y z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1) := by
        abel
    _ = f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2) - f'y z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1) := by
        rw [ContinuousLinearMap.sub_apply]
        abel
    _ = f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2) - f'y z) (y - z.2)
      + (f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1)) := by
        abel
  -- set up the hypotheses and use the inequality version of the Mean Value Theorem
  have mvt_diff : ∀ y ∈ ball z.2 (min δy δt),
      HasFDerivWithinAt (f ∘ (x,·)) (f'y (x,y)) (ball z.2 (min δy δt)) y := by
    intro y' hy'
    rw [mem_ball_iff_norm, lt_min_iff] at hy'
    apply (hf'y (x,y') (mem_prod.mpr ⟨hst.1.1, _⟩)).hasFDerivWithinAt.mono
    · calc
        ball z.2 (min δy δt)
          ⊆ ball z.2 δt := ball_subset_ball (min_le_right _ _)
        _ ⊆ t := hδt.2
    · exact mem_of_subset_of_mem hδt.2 (mem_ball_iff_norm.mpr hy'.2)
  have mvt_bound : ∀ y' ∈ ball z.2 (min δy δt), ‖f'y (x,y') - f'y (x,z.2)‖ ≤ ε + ε := by
    intro y' hy'
    rw [mem_ball_iff_norm, lt_min_iff] at hy'
    rw [← dist_eq_norm]
    apply (dist_triangle _ (f'y z) _).trans
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (f'y z) _]
    have hxy' : ‖(x,y') - z‖ < δy := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sup_lt_iff]
      exact ⟨hxy, hy'.1⟩
    have hxz2 : ‖(x,z.2) - z‖ < δy := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
        sup_of_le_left]
      exact hxy
    apply add_le_add (hf'y_cont _ hxy').le (hf'y_cont _ hxz2).le
    · apply mem_prod.mpr ⟨hst.1.1, _⟩
      exact mem_of_subset_of_mem hδt.2 (mem_ball_iff_norm.mpr hy'.2)
    · exact mem_prod.mpr ⟨hst.1.1, hz.1.2⟩
  have mvt {a b} (ha : a ∈ _) (hb : b ∈ _) :=
    -- inequality version of Mean Value Theorem
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      mvt_diff
      mvt_bound
      (convex_ball z.2 (min δy δt)) ha hb
  simp only [comp_apply] at mvt
  -- use the calculation above and start applying norms and estimates on the goal, term by term
  rw [hf]
  replace hf := calc
    ‖f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2) - f'y z) (y - z.2)
      + (f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1))‖
      ≤ ‖f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)‖
      + ‖(f'y (x,z.2) - f'y z) (y - z.2)‖
      + ‖(f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1))‖ := norm_add₃_le
    _ ≤ (ε + ε) * ‖y - z.2‖
      + ‖(f'y (x,z.2) - f'y z)‖ * ‖y - z.2‖
      + ε * ‖x - z.1‖ := by
        apply add_le_add (add_le_add _ _) _ -- compare term by term
        · exact mvt -- Mean Value estimate
            (mem_ball_self (lt_min hδy hδt.1))
            (mem_ball_iff_norm.mpr (lt_min hyy hyt))
        · exact ContinuousLinearMap.le_opNorm _ _ -- operator norm estimate
        · rw [mul_comm]
          by_cases hxnz : 0 < ‖x - z.1‖
          case neg => -- handle trivial x = z.1 case
            replace hxnz := (not_lt.mp hxnz).antisymm (norm_nonneg _)
            have hxnz' := eq_of_sub_eq_zero (norm_eq_zero.mp hxnz)
            repeat rw [hxnz, hxnz']
            simp only [Prod.mk.eta, sub_self, map_zero, norm_zero, zero_mul, le_refl]
          case pos =>
            apply (inv_mul_le_iff₀ hxnz).mp
            exact (hf'xz hst.1.1 hxx).le -- apply differentiability estimate
    _ ≤ ε * ‖y - z.2‖ + ε * ‖y - z.2‖ + ε * ‖y - z.2‖ + ε * ‖x - z.1‖ := by
        rw [add_mul]
        apply add_le_add (add_le_add le_rfl _) le_rfl
        apply mul_le_mul (hf'y_cont _ _).le le_rfl (norm_nonneg (y - z.2)) hε.le
        · exact (mem_prod.mpr ⟨hst.1.1, hz.1.2⟩)
        · simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
          sup_of_le_left, hxy]
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

/-- If a function `f : E × F → G` has a second partial derivative (within set `t`) `f'yz` at `z`
and has a first partial derivative (within open set `s`) `f'x` continuous on `s ×ˢ t`,
then `f` has a derivative at `z`, with the derivative given by `f'z = (f'x z).coprod f'yz`.

See `hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open` for the order of derivatives
swapped.
-/
theorem hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {z : E × F}
  (hz : z ∈ s ×ˢ t) (hs : IsOpen s)
  {f'x : E × F → E →L[𝕜] G} {f'yz : F →L[𝕜] G}
  (hf'x_cont : ContinuousWithinAt f'x (s ×ˢ t) z)
  (hf'x : ∀ z' ∈ s ×ˢ t, HasFDerivAt (f ∘ (·, z'.2)) (f'x z') z'.1)
  (hf'yz : HasFDerivWithinAt (f ∘ (z.1, ·)) f'yz t z.2) :
    HasFDerivWithinAt f ((f'x z).coprod f'yz) (s ×ˢ t) z := by
  have hmt_st := mapsTo_swap_prod s t
  have hmt_ts := mapsTo_swap_prod t s
  have hf'x_swap_cont := (z.swap_swap ▸ hf'x_cont).comp
    continuous_swap.continuousWithinAt
    hmt_ts
  -- exchange `E` and `F` to use a previous result
  have hswap := hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
    (f := f ∘ Prod.swap)
    (z := z.swap)
    hz.symm hs
    hf'x_swap_cont
    hf'yz
    (fun z' hz' => (hf'x z'.swap (hmt_ts hz')))
  -- exchange `E` and `F` back in the result to satisfy the goal
  let cle_swap := ContinuousLinearEquiv.prodComm 𝕜 E F
  convert hswap.comp z (cle_swap.hasFDerivWithinAt) hmt_st
  unfold cle_swap
  simp only [Prod.swap_swap, comp_apply, ContinuousLinearMap.coprod_comp_prodComm]

/-- If a function `f : E × F → G` has partial derivative `f'x` or `f'y` on an open set `u`,
and they are continuous at `z ∈ u`, then `f` is continously differentiable at `z`, with
the derivative given by `f' z = (f'x z).coprod (f'y z)`.
-/
theorem hasFDerivWithinAt_continuousWithinAt_of_partial_continuousWithinAt_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  --NB: [NormedSpace ℝ E] is not needed because the proof eventually applies
  --    the Mean Value Theorem only in the F direction. But it could have been
  --    the other way around and it is odd to not have symmetry in the hypotheses
  {E : Type*} [NormedAddCommGroup E] /-[NormedSpace ℝ E]-/ [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {u : Set (E × F)} (hu : IsOpen u) {z : E × F} (hz : z ∈ u)
  {f'x : E × F → E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'x_cont : ContinuousWithinAt f'x u z) (hf'y_cont : ContinuousWithinAt f'y u z)
  (hf'x : ∀ z ∈ u, HasFDerivAt (f ∘ (·, z.2)) (f'x z) z.1)
  (hf'y : ∀ z ∈ u, HasFDerivAt (f ∘ (z.1, ·)) (f'y z) z.2) :
    ContinuousWithinAt (fun z => (f'x z).coprod (f'y z)) u z
    ∧ HasFDerivAt f ((f'x z).coprod (f'y z)) z := by
  refine ⟨?cont, ?diff⟩
  case cont =>
    -- combine continuity of partial to get continuity of total derivative
    exact hf'x_cont.continuousLinearMapCoprod hf'y_cont
  case diff =>
    -- first restrict all properties to a product neighborhood of z
    obtain ⟨s,t,hs,ht,hz1,hz2,hst⟩ := isOpen_prod_iff.mp hu z.1 z.2 hz
    have hstn : s ×ˢ t ∈ nhds z := IsOpen.mem_nhds (hs.prod ht) (mem_prod.mpr ⟨hz1, hz2⟩)
    have hsu (z : E × F) (hz : z ∈ s ×ˢ t) : s ⊆ ((·,z.2) ⁻¹' u) := by
      apply HasSubset.Subset.trans _ (preimage_mono hst)
      rw [mk_preimage_prod_left (mem_prod.mpr hz).2]
    have htu (z : E × F) (hz : z ∈ s ×ˢ t) : t ⊆ ((z.1,·) ⁻¹' u) := by
      apply HasSubset.Subset.trans _ (preimage_mono hst)
      rw [mk_preimage_prod_right (mem_prod.mpr hz).1]
    replace hf'y_cont := hf'y_cont.mono hst
    -- now apply the weaker criteria to get differentiability
    apply HasFDerivWithinAt.hasFDerivAt _ hstn
    apply hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
      ⟨hz1,hz2⟩ ht
      hf'y_cont
      _ _
    · exact (hf'x z hz).hasFDerivWithinAt.mono (hsu z ⟨hz1,hz2⟩)
    · exact (fun z hz => (hf'y z (mem_of_subset_of_mem hst hz)))

/-- If a function `f : E × F → G` has partial derivative `f'x` or `f'y` continuous
on an open set `u`, then `f` is continously differentiable on this set, with
the derivative given by `f' = f'x.coprod f'y`.
-/
theorem hasFDerivWithinAt_continuousOn_of_partial_continuousOn_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  --NB: [NormedSpace ℝ E] is not needed because the proof eventually applies
  --    the Mean Value Theorem only in the F direction. But it could have been
  --    the other way around and it is odd to not have symmetry in the hypotheses
  {E : Type*} [NormedAddCommGroup E] /-[NormedSpace ℝ E]-/ [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {u : Set (E × F)} (hu : IsOpen u)
  {f'x : E × F → E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'x_cont : ContinuousOn f'x u) (hf'y_cont : ContinuousOn f'y u)
  (hf'x : ∀ z ∈ u, HasFDerivAt (f ∘ (·, z.2)) (f'x z) z.1)
  (hf'y : ∀ z ∈ u, HasFDerivAt (f ∘ (z.1, ·)) (f'y z) z.2) :
    ContinuousOn (fun z => (f'x z).coprod (f'y z)) u
    ∧ ∀ z ∈ u, HasFDerivAt f ((f'x z).coprod (f'y z)) z := by
  simp only [ContinuousOn, ← forall₂_and]
  intro z hz
  apply hasFDerivWithinAt_continuousWithinAt_of_partial_continuousWithinAt_open
    hu hz
    (hf'x_cont.continuousWithinAt hz) (hf'y_cont.continuousWithinAt hz)
    hf'x hf'y

end PartialFDeriv
