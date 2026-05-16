/-
Copyright (c) 2025 Igor Khavkine, A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine, A Tucker
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

Results in this file relate the partial derivatives of a bivariate function to its differentiability
in the product space.

## Main statements

* `hasStrictFDerivAt_uncurry_coprod`: establishing strict differentiability at a point `u` in the
  product space, this requires that both partial derivatives exist in a neighbourhood of `u` and be
  continuous at `u`.

* `hasFDerivWithinAt_uncurry_coprod_of_continuousWithinAt_snd`: this weaker result requires that
  both partial derivatives exist, but only the second need exist in a neighbourhood of `u` (and be
  continuous at `u`).

* `HasFDerivWithinAt.partial_fst` , `HasFDerivWithinAt.partial_snd`: if `f` is differentiable
  with derivative `f' u` at `u`, then the partial derivatives of `(f ∘ (u.1, ·))`
  and `(f ∘ (·, u.2))` are respectively `(f' u) ∘L (.inl 𝕜 E₁ E₂)` and
  `(f' u) ∘L (.inr 𝕜 E₁ E₂)`. If `f'` is continuous, then continuity can be obtained by
  by combining `Continuous(|At|On|WithinAt).clm_comp` and `Continuous(|At|On|WithinAt)_const`.

* `hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open` : a weak sufficient condition
  for differentiability of `f` at `u = (u₁,u₂)` is that, say, the first derivative (within set `s₁`)
  `f₁u` exists at `u`, while the second partial derivative `f₂ u` exists and is jointly
  continuous at `u` in the product set `s₁ ×ˢ s₂` where `s₂` is open, with the derivative given by
  `f'u = f₁u.coprod (f₂ u)`. `hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open` has
  the roles of the partial derivatives reversed.

  The proofs follow §8.9.1 from Dieudonné's *Foundations of Modern Analysis* (1969).

* `hasFDerivWithinAt_continuous(On|WithinAt)_of_partial_continuous(On|WithinAt)_open`: when
  both partial derivatives exist and are continuous on (or at `u` in) an open set `s`, this more
  convenient theorem directly deduces continous differentiability on (or at `u` in) `s`.
-/

open Asymptotics Filter
open scoped Convex Topology

/-- Suppose that along `l : Filter α` each of `v w : α → E` tends to `u : E` and that along
`l ×ˢ 𝓝[s] u` the derivative of `f : α → E → F` tends to `φ : E →L[𝕜] F`. Then the difference
between `f χ (v χ)` and `f χ (w χ)` is, to first order, `φ (v χ - w χ)`. This can be useful where
`χ : α` stands for a point (or a pair of points) in a space containing `E`, and `v χ` or `w χ` is
its projection (or both are projections). -/
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
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If bivariate `f : E₁ → E₂ → F` has partial derivatives `f₁` and `f₂` in a neighbourhood of
`u : E₁ × E₂`, both continuous at `u`, then the uncurried function `↿f` is strictly differentiable
at `u` with its derivative mapping `z : E₁ × E₂` to `f₁ u.1 u.2 z.1 + f₂ u.1 u.2 z.2`. -/
public theorem hasStrictFDerivAt_uncurry_coprod
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

/-- If bivariate `f : E₁ → E₂ → F` has partial derivatives `f₁u` at `u : E₁ × E₂` and `f₂` in a
neighbourhood of `u`, the latter continuous at `u`, then the uncurried function `↿f` is
differentiable at `u` with its derivative mapping `z : E₁ × E₂` to `f₁u z.1 + f₂ u.1 u.2 z.2`. -/
public theorem hasFDerivWithinAt_uncurry_coprod_of_continuousWithinAt_snd
    [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₂] {u : E₁ × E₂} {s₁ : Set E₁} {s₂ : Set E₂}
    (seg : ∀ᶠ y in 𝓝[s₂] u.2, [u.2 -[ℝ] y] ⊆ s₂) {f : E₁ → E₂ → F} {f₁u : E₁ →L[𝕜] F}
    {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (df₁u : HasFDerivWithinAt (f · u.2) f₁u s₁ u.1)
    (df₂ : ∀ᶠ v in 𝓝[s₁ ×ˢ s₂] u, HasFDerivWithinAt (f v.1 ·) (↿f₂ v) s₂ v.2)
    (cf₂ : ContinuousWithinAt ↿f₂ (s₁ ×ˢ s₂) u) :
    HasFDerivWithinAt ↿f (f₁u.coprod (↿f₂ u)) (s₁ ×ˢ s₂) u := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  unfold ContinuousWithinAt at cf₂
  rw [nhdsWithin_prod_eq] at ⊢ df₂ cf₂
  calc
    fun v => ↿f v - ↿f u - (f₁u.coprod (↿f₂ u)) (v - u)
    _ = fun v => (f v.1 u.2 - ↿f u - f₁u (v - u).1) + (↿f v - f v.1 u.2 - ↿f₂ u (v - u).2) := by
      ext
      rw [ContinuousLinearMap.coprod_apply]
      abel
    _ =o[𝓝[s₁] u.1 ×ˢ 𝓝[s₂] u.2] fun v => v - u := by
      apply IsLittleO.add
      · calc
          (fun x => f x u.2 - f u.1 u.2 - f₁u (x - u.1)) ∘ Prod.fst
          _ =o[𝓝[s₁] u.1 ×ˢ 𝓝[s₂] u.2] ((fun x => x - u.1) ∘ Prod.fst) := by
            apply IsLittleO.comp_fst
            rwa [hasFDerivWithinAt_iff_isLittleO] at df₁u
          _ =O[𝓝[s₁] u.1 ×ˢ 𝓝[s₂] u.2] fun v => (v.1 - u.1, v.2 - u.2) := by
            simp [isBigO_of_le]
      · calc
          fun v => f v.1 v.2 - f v.1 u.2 - ↿f₂ u (v.2 - u.2)
          _ =o[𝓝[s₁] u.1 ×ˢ 𝓝[s₂] u.2] fun v => v.2 - u.2 := by
            have h := (tendsto_fst.comp tendsto_fst).prodMk <|
              tendsto_snd (f := 𝓝[s₁] u.1 ×ˢ 𝓝[s₂] u.2) (g := 𝓝[s₂] u.2)
            exact isLittleO_sub_sub_fderiv (f' := fun v y => f₂ v.1 y)
              (tendsto_nhds_of_tendsto_nhdsWithin tendsto_snd) tendsto_const_nhds
              s₂ (seg.prod_inr _) (h.eventually df₂) (cf₂.comp h)
          _ =O[𝓝[s₁] u.1 ×ˢ 𝓝[s₂] u.2] fun v => (v.1 - u.1, v.2 - u.2) := by
            simp [isBigO_of_le]

public section PartialFDeriv

open Set Function Metric

/-- Differentiable implies also that the first partial derivative exists. -/
theorem HasFDerivWithinAt.partial_fst
    {f : E₁ × E₂ → F} {f' : E₁ × E₂ → E₁ × E₂ →L[𝕜] F}
    {s₁ : Set E₁} {s₂ : Set E₂}
    {u : E₁ × E₂} (hu : u ∈ s₁ ×ˢ s₂)
    (hf : HasFDerivWithinAt f (f' u) (s₁ ×ˢ s₂) u) :
    HasFDerivWithinAt (f ∘ (·, u.2)) (f' u ∘L .inl ..) s₁ u.1 := by
  have hleft (x:E₁) := HasFDerivWithinAt.prodMk
    (hasFDerivWithinAt_id (𝕜 := 𝕜) x s₁)
    (hasFDerivWithinAt_const u.2 x s₁)
  convert HasFDerivWithinAt.comp u.1 (hf) (hleft u.1)
    (fun x hx => mem_prod.mpr ⟨hx, (mem_prod.mp hu).right⟩)

/-- Differentiable implies also that the second partial derivative exists. -/
theorem HasFDerivWithinAt.partial_snd
    {f : E₁ × E₂ → F} {f' : E₁ × E₂ → E₁ × E₂ →L[𝕜] F}
    {s₁ : Set E₁} {s₂ : Set E₂}
    {u : E₁ × E₂} (hu : u ∈ s₁ ×ˢ s₂)
    (hf : HasFDerivWithinAt f (f' u) (s₁ ×ˢ s₂) u) :
    HasFDerivWithinAt (f ∘ (u.1, ·)) (f' u ∘L .inr ..) s₂ u.2 := by
  have hright (y:E₂) := HasFDerivWithinAt.prodMk
    (hasFDerivWithinAt_const u.1 y s₂)
    (hasFDerivWithinAt_id (𝕜 := 𝕜) y s₂)
  convert HasFDerivWithinAt.comp u.2 (hf) (hright u.2)
    (fun y hy => mem_prod.mpr ⟨(mem_prod.mp hu).left, hy⟩)

/-- If a function `f : E₁ × E₂ → F` has a first partial derivative (within set `s₁`) `f₁u` at `u`
and has a second partial derivative (within open set `s₂`) `f₂` continuous on `s₁ ×ˢ s₂`,
then `f` has a derivative at `u`, with the derivative given by `f'u = f₁u.coprod (f₂ u)`.

See `hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open` for the order of derivatives
swapped.
-/
theorem hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
    [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₂]
    {f : E₁ × E₂ → F} {s₁ : Set E₁} {s₂ : Set E₂} {u : E₁ × E₂}
    (hu : u ∈ s₁ ×ˢ s₂) (hs₂ : IsOpen s₂)
    {f₁u : E₁ →L[𝕜] F} {f₂ : E₁ × E₂ → E₂ →L[𝕜] F}
    (hf₂_cont : ContinuousWithinAt f₂ (s₁ ×ˢ s₂) u)
    (hf₁u : HasFDerivWithinAt (f ∘ (·, u.2)) f₁u s₁ u.1)
    (hf₂ : ∀ v ∈ s₁ ×ˢ s₂, HasFDerivAt (f ∘ (v.1, ·)) (f₂ v) v.2) :
    HasFDerivWithinAt f (f₁u.coprod (f₂ u)) (s₁ ×ˢ s₂) u := by
  replace hu : _ ∧ _ := ⟨mem_prod.mp hu, hu⟩
  simp only at hu
  -- rewrite derivatives as limits using norms
  simp only [hasFDerivWithinAt_iff_tendsto, tendsto_nhdsWithin_nhds, dist_eq_norm] at ⊢ hf₁u
  simp only [ContinuousLinearMap.coprod_apply, sub_zero, norm_mul, norm_inv,
    norm_norm] at ⊢ hf₁u
  simp only [Metric.continuousWithinAt_iff, dist_eq_norm] at hf₂_cont
  -- get a target ε' and immediately shrink it to ε for convenice
  intro ε' hε'
  rw [show ε' = (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 by ring]
  have hε := half_pos (half_pos (half_pos hε'))
  set ε := ε' / 2 / 2 / 2
  -- get δu₁ from u₁-differentiability
  -- get δu₂ from continuity of u₂-derivative
  -- get δs₂ is constrained by the possibly small size of s₂
  replace ⟨δu₁, hδu₁, hf₁u⟩ := hf₁u ε hε
  replace ⟨δu₂, hδu₂, hf₂_cont⟩ := hf₂_cont ε hε
  obtain ⟨δs₂, hδs₂⟩ := isOpen_iff.mp hs₂ u.2 hu.1.2
  use (min δu₁ (min δu₂ δs₂)) -- derive desired δ
  refine ⟨?pos, ?_⟩
  case pos => exact lt_min hδu₁ (lt_min hδu₂ hδs₂.1) -- positivity of δ
  -- get working point (v₁,v₂) ∈ E₁ × E₂ within δ distance of u
  intro (v₁,v₂) hs₁s₂ hδ
  replace hs₁s₂ : _ ∧ _ := ⟨mem_prod.mp hs₁s₂, hs₁s₂⟩
  simp only at hs₁s₂
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [mul_comm]
  -- simplify norm conditions into bounds on ‖v₁-u.1‖ and ‖v₂-u.2‖
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hδ
  simp only [lt_inf_iff, sup_lt_iff] at hδ
  obtain ⟨⟨h₁δu₁, h₂δu₁⟩, ⟨⟨h₁δu₂, h₂δu₂⟩, ⟨h₁δs₂, h₂δs₂⟩⟩⟩ := hδ
  -- rewrite desired variation in f for easier estimation
  have hf := calc
    f (v₁,v₂) - f u - (f₁u (v₁ - u.1) + (f₂ u) (v₂ - u.2))
      = f (v₁,v₂) - f (v₁,u.2)
      + f (v₁,u.2) - f (u.1,u.2) - (f₁u (v₁ - u.1) + (f₂ u) (v₂ - u.2)) := by
        abel
    _ = f (v₁,v₂) - f (v₁,u.2) - (f₂ u) (v₂ - u.2)
      + f (v₁,u.2) - f (u.1,u.2) - f₁u (v₁ - u.1) := by
        abel
    _ = f (v₁,v₂) - f (v₁,u.2) - (f₂ (v₁,u.2)) (v₂ - u.2)
      + (f₂ (v₁,u.2)) (v₂ - u.2) - (f₂ u) (v₂ - u.2)
      + f (v₁,u.2) - f (u.1,u.2) - f₁u (v₁ - u.1) := by
        abel
    _ = f (v₁,v₂) - f (v₁,u.2) - (f₂ (v₁,u.2)) (v₂ - u.2)
      + (f₂ (v₁,u.2) - f₂ u) (v₂ - u.2)
      + f (v₁,u.2) - f (u.1,u.2) - f₁u (v₁ - u.1) := by
        rw [ContinuousLinearMap.sub_apply]
        abel
    _ = f (v₁,v₂) - f (v₁,u.2) - (f₂ (v₁,u.2)) (v₂ - u.2)
      + (f₂ (v₁,u.2) - f₂ u) (v₂ - u.2)
      + (f (v₁,u.2) - f (u.1,u.2) - f₁u (v₁ - u.1)) := by
        abel
  -- set up the hypotheses and use the inequality version of the Mean Value Theorem
  have mvt_diff : ∀ y ∈ ball u.2 (min δu₂ δs₂),
      HasFDerivWithinAt (f ∘ (v₁,·)) (f₂ (v₁,y)) (ball u.2 (min δu₂ δs₂)) y := by
    intro y hy
    rw [mem_ball_iff_norm, lt_min_iff] at hy
    apply (hf₂ (v₁,y) (mem_prod.mpr ⟨hs₁s₂.1.1, _⟩)).hasFDerivWithinAt.mono
    · calc
        ball u.2 (min δu₂ δs₂)
          ⊆ ball u.2 δs₂ := ball_subset_ball (min_le_right _ _)
        _ ⊆ s₂ := hδs₂.2
    · exact mem_of_subset_of_mem hδs₂.2 (mem_ball_iff_norm.mpr hy.2)
  have mvt_bound : ∀ y ∈ ball u.2 (min δu₂ δs₂), ‖f₂ (v₁,y) - f₂ (v₁,u.2)‖ ≤ ε + ε := by
    intro y hy
    rw [mem_ball_iff_norm, lt_min_iff] at hy
    rw [← dist_eq_norm]
    apply (dist_triangle _ (f₂ u) _).trans
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (f₂ u) _]
    have hv₁y : ‖(v₁,y) - u‖ < δu₂ := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sup_lt_iff]
      exact ⟨h₁δu₂, hy.1⟩
    have hv₁u2 : ‖(v₁,u.2) - u‖ < δu₂ := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
        sup_of_le_left]
      exact h₁δu₂
    apply add_le_add (hf₂_cont _ hv₁y).le (hf₂_cont _ hv₁u2).le
    · apply mem_prod.mpr ⟨hs₁s₂.1.1, _⟩
      exact mem_of_subset_of_mem hδs₂.2 (mem_ball_iff_norm.mpr hy.2)
    · exact mem_prod.mpr ⟨hs₁s₂.1.1, hu.1.2⟩
  have mvt {a b} (ha : a ∈ _) (hb : b ∈ _) :=
    -- inequality version of Mean Value Theorem
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      mvt_diff
      mvt_bound
      (convex_ball u.2 (min δu₂ δs₂)) ha hb
  simp only [comp_apply] at mvt
  -- use the calculation above and start applying norms and estimates on the goal, term by term
  rw [hf]
  replace hf := calc
    ‖f (v₁,v₂) - f (v₁,u.2) - (f₂ (v₁,u.2)) (v₂ - u.2)
      + (f₂ (v₁,u.2) - f₂ u) (v₂ - u.2)
      + (f (v₁,u.2) - f (u.1,u.2) - f₁u (v₁ - u.1))‖
      ≤ ‖f (v₁,v₂) - f (v₁,u.2) - (f₂ (v₁,u.2)) (v₂ - u.2)‖
      + ‖(f₂ (v₁,u.2) - f₂ u) (v₂ - u.2)‖
      + ‖(f (v₁,u.2) - f (u.1,u.2) - f₁u (v₁ - u.1))‖ := norm_add₃_le
    _ ≤ (ε + ε) * ‖v₂ - u.2‖
      + ‖(f₂ (v₁,u.2) - f₂ u)‖ * ‖v₂ - u.2‖
      + ε * ‖v₁ - u.1‖ := by
        apply add_le_add (add_le_add _ _) _ -- compare term by term
        · exact mvt -- Mean Value estimate
            (mem_ball_self (lt_min hδu₂ hδs₂.1))
            (mem_ball_iff_norm.mpr (lt_min h₂δu₂ h₂δs₂))
        · exact ContinuousLinearMap.le_opNorm _ _ -- operator norm estimate
        · rw [mul_comm]
          by_cases hv₁nu : 0 < ‖v₁ - u.1‖
          case neg => -- handle trivial v₁ = u.1 case
            replace hv₁nu := (not_lt.mp hv₁nu).antisymm (norm_nonneg _)
            have hv₁nu' := eq_of_sub_eq_zero (norm_eq_zero.mp hv₁nu)
            repeat rw [hv₁nu, hv₁nu']
            simp only [Prod.mk.eta, sub_self, map_zero, norm_zero, zero_mul, le_refl]
          case pos =>
            apply (inv_mul_le_iff₀ hv₁nu).mp
            exact (hf₁u hs₁s₂.1.1 h₁δu₁).le -- apply differentiability estimate
    _ ≤ ε * ‖v₂ - u.2‖ + ε * ‖v₂ - u.2‖ + ε * ‖v₂ - u.2‖ + ε * ‖v₁ - u.1‖ := by
        rw [add_mul]
        apply add_le_add (add_le_add le_rfl _) le_rfl
        apply mul_le_mul (hf₂_cont _ _).le le_rfl (norm_nonneg (v₂ - u.2)) hε.le
        · exact (mem_prod.mpr ⟨hs₁s₂.1.1, hu.1.2⟩)
        · simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
          sup_of_le_left, h₁δu₂]
  -- now apply the estimate hf to the goal
  apply (mul_le_mul_of_nonneg_right hf (by simp only [inv_nonneg, norm_nonneg])).trans_lt _
  -- it remains only to simplify the inequality term by term and compare coefficients
  simp only [add_mul, mul_assoc]
  apply add_lt_add (add_lt_add (add_lt_add _ _) _)
  all_goals
    apply (mul_lt_mul_iff_right₀ hε).mpr
    refine LE.le.trans_lt ?_ (one_lt_two)
    rw [mul_comm]
    apply inv_mul_le_of_le_mul₀ (norm_nonneg _) zero_le_one
    simp only [mul_one, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
    first | exact le_max_right _ _ | exact le_max_left _ _

/-- If a function `f : E₁ × E₂ → F` has a second partial derivative (within set `s₂`) `f₂u` at `u`
and has a first partial derivative (within open set `s₁`) `f₁` continuous on `s₁ ×ˢ s₂`,
then `f` has a derivative at `u`, with the derivative given by `f'u = (f₁ u).coprod f₂u`.

See `hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open` for the order of derivatives
swapped.
-/
theorem hasFDerivWithinAt_of_partial_fst_continuousWithinAt_prod_open
    [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E₁]
    {f : E₁ × E₂ → F} {s₁ : Set E₁} {s₂ : Set E₂} {u : E₁ × E₂}
    (hu : u ∈ s₁ ×ˢ s₂) (hs₁ : IsOpen s₁)
    {f₁ : E₁ × E₂ → E₁ →L[𝕜] F} {f₂u : E₂ →L[𝕜] F}
    (hf₁_cont : ContinuousWithinAt f₁ (s₁ ×ˢ s₂) u)
    (hf₁ : ∀ v ∈ s₁ ×ˢ s₂, HasFDerivAt (f ∘ (·, v.2)) (f₁ v) v.1)
    (hf₂u : HasFDerivWithinAt (f ∘ (u.1, ·)) f₂u s₂ u.2) :
    HasFDerivWithinAt f ((f₁ u).coprod f₂u) (s₁ ×ˢ s₂) u := by
  have hmt_s₁s₂ := mapsTo_swap_prod s₁ s₂
  have hmt_s₂s₁ := mapsTo_swap_prod s₂ s₁
  have hf₁_swap_cont := (u.swap_swap ▸ hf₁_cont).comp
    continuous_swap.continuousWithinAt
    hmt_s₂s₁
  -- exchange `E₁` and `E₂` to use a previous result
  have hswap := hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
    (f := f ∘ Prod.swap)
    (u := u.swap)
    hu.symm hs₁
    hf₁_swap_cont
    hf₂u
    (fun v hv => (hf₁ v.swap (hmt_s₂s₁ hv)))
  -- exchange `E₁` and `E₂` back in the result to satisfy the goal
  let cle_swap := ContinuousLinearEquiv.prodComm 𝕜 E₁ E₂
  convert hswap.comp u (cle_swap.hasFDerivWithinAt) hmt_s₁s₂
  unfold cle_swap
  simp only [Prod.swap_swap, comp_apply, ContinuousLinearMap.coprod_comp_prodComm]

/-- If a function `f : E₁ × E₂ → F` has partial derivative `f₁` or `f₂` on an open set `s`,
and they are continuous at `u ∈ s`, then `f` is continously differentiable at `u`, with
the derivative given by `f' u = (f₁ u).coprod (f₂ u)`.
-/
theorem hasFDerivWithinAt_continuousWithinAt_of_partial_continuousWithinAt_open
    --NB: [NormedSpace ℝ E₁] is not needed because the proof eventually applies
    --    the Mean Value Theorem only in the E₂ direction. But it could have been
    --    the other way around and it is odd to not have symmetry in the hypotheses
    [IsRCLikeNormedField 𝕜] /-[NormedSpace ℝ E₁]-/ [NormedSpace ℝ E₂]
    {f : E₁ × E₂ → F} {s : Set (E₁ × E₂)} (hs : IsOpen s) {u : E₁ × E₂} (hu : u ∈ s)
    {f₁ : E₁ × E₂ → E₁ →L[𝕜] F} {f₂ : E₁ × E₂ → E₂ →L[𝕜] F}
    (hf₁_cont : ContinuousWithinAt f₁ s u) (hf₂_cont : ContinuousWithinAt f₂ s u)
    (hf₁ : ∀ v ∈ s, HasFDerivAt (f ∘ (·, v.2)) (f₁ v) v.1)
    (hf₂ : ∀ v ∈ s, HasFDerivAt (f ∘ (v.1, ·)) (f₂ v) v.2) :
    ContinuousWithinAt (fun v => (f₁ v).coprod (f₂ v)) s u
    ∧ HasFDerivAt f ((f₁ u).coprod (f₂ u)) u := by
  refine ⟨?cont, ?diff⟩
  case cont =>
    -- combine continuity of partial to get continuity of total derivative
    exact hf₁_cont.continuousLinearMapCoprod hf₂_cont
  case diff =>
    -- first restrict all properties to a product neighborhood of u
    obtain ⟨s₁,s₂,hs₁,hs₂,hu1,hu2,hs₁s₂⟩ := isOpen_prod_iff.mp hs u.1 u.2 hu
    have hs₁s₂n : s₁ ×ˢ s₂ ∈ nhds u := IsOpen.mem_nhds (hs₁.prod hs₂) (mem_prod.mpr ⟨hu1, hu2⟩)
    have hs₁s (v : E₁ × E₂) (hv : v ∈ s₁ ×ˢ s₂) : s₁ ⊆ ((·,v.2) ⁻¹' s) := by
      apply HasSubset.Subset.trans _ (preimage_mono hs₁s₂)
      rw [mk_preimage_prod_left (mem_prod.mpr hv).2]
    have hs₂s (v : E₁ × E₂) (hv : v ∈ s₁ ×ˢ s₂) : s₂ ⊆ ((v.1,·) ⁻¹' s) := by
      apply HasSubset.Subset.trans _ (preimage_mono hs₁s₂)
      rw [mk_preimage_prod_right (mem_prod.mpr hv).1]
    replace hf₂_cont := hf₂_cont.mono hs₁s₂
    -- now apply the weaker criteria to get differentiability
    apply HasFDerivWithinAt.hasFDerivAt _ hs₁s₂n
    apply hasFDerivWithinAt_of_partial_snd_continuousWithinAt_prod_open
      ⟨hu1,hu2⟩ hs₂
      hf₂_cont
      _ _
    · exact (hf₁ u hu).hasFDerivWithinAt.mono (hs₁s u ⟨hu1,hu2⟩)
    · exact (fun v hv => (hf₂ v (mem_of_subset_of_mem hs₁s₂ hv)))

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
    (hf₁ : ∀ v ∈ s, HasFDerivAt (f ∘ (·, v.2)) (f₁ v) v.1)
    (hf₂ : ∀ v ∈ s, HasFDerivAt (f ∘ (v.1, ·)) (f₂ v) v.2) :
    ContinuousOn (fun v => (f₁ v).coprod (f₂ v)) s
    ∧ ∀ v ∈ s, HasFDerivAt f ((f₁ v).coprod (f₂ v)) v := by
  simp only [ContinuousOn, ← forall₂_and]
  intro v hv
  apply hasFDerivWithinAt_continuousWithinAt_of_partial_continuousWithinAt_open
    hs hv
    (hf₁_cont.continuousWithinAt hv) (hf₂_cont.continuousWithinAt hv)
    hf₁ hf₂

end PartialFDeriv
