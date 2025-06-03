/-
Copyright (c) 2025 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

In this file we prove some basic facts about partial derivatives of functions
defined on a product space, like `f : E × F → G`:

* `HasFDerivWithinAt.partial_fst` , `HasFDerivWithinAt.partial_snd`: if `f` is differentiable
   with derivative `f' z` at `z`, then the partial derivatives of `(f ∘ (z.1, ·))`
   and `(f ∘ (·, z.2))` are respectively `(f' z) ∘L (.inl 𝕜 E F)` and
   `(f' z) ∘L (.inr 𝕜 E F)`. If `f'` is continuous, then continuity can be obtained by
   by combining `Continuous(|At|On|WithinAt).clm_comp` and `Continuous(|At|On|WithinAt)_const`.

* `hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open` : a weak sufficient condition
  for differeniability of `f` at `z = (x,y)` is that, say, the first derivative (within set `s`)
  `f'xz` exists at `z`, while the second partial derivative `f'y z` exists and is continuos on
  a product set `s ×ˢ t` where `t` is open, with the derivative given by
  `f'z = f'xz.coprod (f'y z)`. `hasFDerivWithinAt_of_partial_fst_continuousOn_prod_open` has the
  roles of the partial derivatives reversed.

  The proofs follow §9.8.1 from Dieudonné's *Foundations of Modern Analysis* (1969).

* `hasFDerivWithinAt_continuousOn_of_partial_continuousOn_open`: when both partial derivatives
  exist and are continuous on an open set `u`, this more covenient theorem directly
  deduces continous differentiability on `u`.

-/

open Set Function Metric Real

section PartialFDeriv

/-- Like `Prod.swap`, but for `ContinuousLinearMap`. -/
abbrev ContinuousLinearMap.prodComm (R : Type*) [Semiring R]
  (M₁ : Type*) [TopologicalSpace M₁] [AddCommMonoid M₁]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] := (ContinuousLinearEquiv.prodComm R M₁ M₂).toContinuousLinearMap

open ContinuousLinearMap in
theorem ContinousLinearMap.coprod_comp_prodComm
  (R : Type*) [Semiring R]
  (M₁ : Type*) [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd M]
  (f : M₁ →L[R] M) (g : M₂ →L[R] M) :
    (f.coprod g).comp (prodComm R M₂ M₁) = (g.coprod f) := by
  ext; all_goals
  simp only [coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply, inl_apply, inr_apply,
    ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk, coprod_apply, map_zero,
    zero_add, add_zero, coprod_comp_inl, coprod_comp_inr]

theorem continuousOn_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set (X × Y)) : ContinuousOn Prod.swap s := by
  unfold ContinuousOn; intro z hz
  apply continuous_swap.continuousWithinAt

open ContinuousLinearMap in
theorem ContinuousLinearMap.coprod_fst_snd
  (R : Type*) [Semiring R]
  (M₁ : Type*) [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd M]
  (f : M₁ →L[R] M) (g : M₂ →L[R] M) :
    (f.coprod g) = f.comp (fst R M₁ M₂) + g.comp (snd R M₁ M₂) := by
  ext; all_goals
  simp only [coprod_comp_inl, coprod_comp_inr, add_comp, add_apply, coe_comp', Function.comp_apply,
    coe_fst', coe_snd', inl_apply, inr_apply, map_zero, add_zero, zero_add]

open ContinuousLinearMap in
theorem ContinuousOn.clm_coprod {X : Type*} [TopologicalSpace X]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).coprod (g x)) s := by
  simp only [coprod_fst_snd]
  exact (hf.clm_comp continuousOn_const).add (hg.clm_comp continuousOn_const)

theorem hasFDerivWithinAt_swap
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (s : Set (E × F)) (z : E × F) :
    HasFDerivWithinAt
      (Prod.swap : E × F → F × E)
      (ContinuousLinearMap.prodComm 𝕜 E F)
      s z
    := by
  convert hasFDerivWithinAt_snd.prodMk (hasFDerivWithinAt_fst (𝕜 := 𝕜) (p := z))

theorem HasFDerivWithinAt.partial_fst
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {f' : E × F → E × F →L[𝕜] G}
  {s : Set E} {t : Set F}
  {z : E × F} (hz : z ∈ s ×ˢ t)
  (hf : HasFDerivWithinAt f (f' z) (s ×ˢ t) z) :
      HasFDerivWithinAt (f ∘ (·, z.2)) ((f' z) ∘L (.inl _ _ _)) s z.1 := by
    have hleft (x:E) := HasFDerivWithinAt.prodMk
      (hasFDerivWithinAt_id (𝕜 := 𝕜) x s)
      (hasFDerivWithinAt_const z.2 x s)
    convert HasFDerivWithinAt.comp z.1 (hf) (hleft z.1)
      (fun x hx => mem_prod.mpr ⟨hx, (mem_prod.mp hz).right⟩)

theorem HasFDerivWithinAt.partial_snd
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {f' : E × F → E × F →L[𝕜] G}
  {s : Set E} {t : Set F}
  {z : E × F} (hz : z ∈ s ×ˢ t)
  (hf : HasFDerivWithinAt f (f' z) (s ×ˢ t) z) :
      HasFDerivWithinAt (f ∘ (z.1, ·)) ((f' z) ∘L (.inr _ _ _)) t z.2 := by
    have hright (y:F) := HasFDerivWithinAt.prodMk
      (hasFDerivWithinAt_const z.1 y t)
      (hasFDerivWithinAt_id (𝕜 := 𝕜) y t)
    convert HasFDerivWithinAt.comp z.2 (hf) (hright z.2)
      (fun y hy => mem_prod.mpr ⟨(mem_prod.mp hz).left, hy⟩)

/-- If a function `f : E × F → G` has a first partial derivative (within set `s`) `f'xz` at `z`
and has a second partial derivative (within open set `t`) `f'y` continuous on `s ×ˢ t`,
then `f` has a derivative at `z`, with the derivative given by `f'z = f'xz.coprod (f'y z)`.

See `hasFDerivWithinAt_of_partial_fst_continuousOn_prod_open` for the order of derivatives swapped.
-/
theorem hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {z : E × F}
  (hz : z ∈ s ×ˢ t) (ht : IsOpen t)
  {f'xz : E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'y_cont : ContinuousOn f'y (s ×ˢ t))
  (hf'xz : HasFDerivWithinAt (f ∘ (·, z.2)) f'xz s z.1)
  (hf'y : ∀ z' ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (z'.1, ·)) (f'y z') t z'.2) :
    HasFDerivWithinAt f (f'xz.coprod (f'y z)) (s ×ˢ t) z := by
  replace hz : _ ∧ _ := ⟨mem_prod.mp hz, hz⟩
  simp only at hz
  -- rewrite derivatives as limits using norms
  simp only [hasFDerivWithinAt_iff_tendsto, tendsto_nhdsWithin_nhds, dist_eq_norm] at ⊢ hf'xz
  simp only [ContinuousLinearMap.coprod_apply, sub_zero, norm_mul, norm_inv,
    norm_norm] at ⊢ hf'xz
  simp only [Metric.continuousOn_iff, dist_eq_norm, norm_eq_abs] at hf'y_cont
  -- get a target ε' and immediately shrink it to ε for convenice
  intro ε' hε'
  rw [show ε' = (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 + (ε'/2/2/2)*2 by ring]
  have hε := half_pos (half_pos (half_pos hε'))
  set ε := ε' / 2 / 2 / 2
  -- get δx from x-differentiability
  -- get δy from continuity of y-derivative
  -- get δt is constrained by the possibly small size of t
  replace ⟨δx, hδx, hf'xz⟩ := hf'xz ε hε
  replace ⟨δy, hδy, hf'y_cont⟩ := hf'y_cont z hz.2 ε hε
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
        simp only [map_sub, sub_add_cancel, Prod.mk.eta]
    _ = f (x,y) - f (x,z.2) - (f'y z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1) := by
        rw [add_comm _ (f'y _ _), ← sub_sub]
        rw [sub_right_comm _ _ (f'y _ _), add_sub_right_comm _ _ (f'y _ _)]
    _ = f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2)) (y - z.2) - (f'y z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1) := by
        simp only [map_sub, Prod.mk.eta, sub_add_cancel]
    _ = f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2) - f'y z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1) := by
        rw [ContinuousLinearMap.sub_apply]
        simp only [map_sub, sub_add_cancel, Prod.mk.eta, sub_add_sub_cancel]
    _ = f (x,y) - f (x,z.2) - (f'y (x,z.2)) (y - z.2)
      + (f'y (x,z.2) - f'y z) (y - z.2)
      + (f (x,z.2) - f (z.1,z.2) - f'xz (x - z.1)) := by
        rw [add_sub_assoc _ (f _) _, add_sub_assoc _ ((f _) - _) _]
  -- set up the hypotheses and use the inequality version of the Mean Value Theorem
  have mvt_diff : ∀ y ∈ ball z.2 (min δy δt),
      HasFDerivWithinAt (f ∘ (x,·)) (f'y (x,y)) (ball z.2 (min δy δt)) y := by
    intro y' hy'
    rw [mem_ball_iff_norm, lt_min_iff] at hy'
    apply (hf'y (x,y') (mem_prod.mpr ⟨hst.1.1, _⟩)).mono
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
    apply add_le_add (hf'y_cont _ _ hxy').le (hf'y_cont _ _ hxz2).le
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
        apply mul_le_mul (hf'y_cont _ _ _).le le_rfl (norm_nonneg (y - z.2)) hε.le
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

See `hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open` for the order of derivatives swapped.
-/
theorem hasFDerivWithinAt_of_partial_fst_continuousOn_prod_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {z : E × F}
  (hz : z ∈ s ×ˢ t) (hs : IsOpen s)
  {f'x : E × F → E →L[𝕜] G} {f'yz : F →L[𝕜] G}
  (hf'x_cont : ContinuousOn f'x (s ×ˢ t))
  (hf'x : ∀ z' ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (·, z'.2)) (f'x z') s z'.1)
  (hf'yz : HasFDerivWithinAt (f ∘ (z.1, ·)) f'yz t z.2) :
    HasFDerivWithinAt f ((f'x z).coprod f'yz) (s ×ˢ t) z := by
  have hmt_st := mapsTo_swap_prod s t
  have hmt_ts := mapsTo_swap_prod t s
  have hf'x_swap_cont := hf'x_cont.comp (continuousOn_swap (t ×ˢ s)) hmt_ts
  -- exchange `E` and `F` to use a previous result
  have hswap := hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open
    (f := f ∘ Prod.swap)
    (z := z.swap)
    hz.symm hs
    hf'x_swap_cont
    hf'yz
    (fun z' hz' => (hf'x z'.swap (hmt_ts hz')))
  -- exchange `E` and `F` back in the result to satisfy the goal
  convert hswap.comp z (hasFDerivWithinAt_swap 𝕜 E F (s ×ˢ t) z) hmt_st
  simp only [Prod.swap_swap, comp_apply, ContinousLinearMap.coprod_comp_prodComm]

/-- If a function `f : E × F → G` has partial derivative `f'x` or `f'y` continuous
on an open set `u`, then `f` is continously differentiable on this set, with
the derivative given by `f' = f'x.coprod f'y`.
-/
theorem hasFDerivWithinAt_continuousOn_of_partial_continuousOn_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {u : Set (E × F)} (hu : IsOpen u)
  {f'x : E × F → E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'x_cont : ContinuousOn f'x u) (hf'y_cont : ContinuousOn f'y u)
  (hf'x : ∀ z ∈ u, HasFDerivWithinAt (f ∘ (·, z.2)) (f'x z) ((·,z.2) ⁻¹' u) z.1)
  (hf'y : ∀ z ∈ u, HasFDerivWithinAt (f ∘ (z.1, ·)) (f'y z) ((z.1,·) ⁻¹' u) z.2) :
    ContinuousOn (fun z => (f'x z).coprod (f'y z)) u
    ∧ ∀ z ∈ u, HasFDerivWithinAt f ((f'x z).coprod (f'y z)) u z := by
  refine ⟨?cont, ?diff⟩
  case cont =>
    -- combine continuity of partial to get continuity of total derivative
    exact hf'x_cont.clm_coprod hf'y_cont
  case diff =>
    intro z hz
    -- first restrict all properties to a product neighborhood of z
    obtain ⟨s,t,hs,ht,hz1,hz2,hst⟩ := isOpen_prod_iff.mp hu z.1 z.2 hz
    have hstn : s ×ˢ t ∈ nhds z := IsOpen.mem_nhds (hs.prod ht) (mem_prod.mpr ⟨hz1, hz2⟩)
    apply (hasFDerivWithinAt_inter hstn).mp
    rw [← right_eq_inter.mpr hst]
    have hsu (z : E × F) (hz : z ∈ s ×ˢ t) : s ⊆ ((·,z.2) ⁻¹' u) := by
      apply HasSubset.Subset.trans _ (preimage_mono hst)
      rw [mk_preimage_prod_left (mem_prod.mpr hz).2]
    have htu (z : E × F) (hz : z ∈ s ×ˢ t) : t ⊆ ((z.1,·) ⁻¹' u) := by
      apply HasSubset.Subset.trans _ (preimage_mono hst)
      rw [mk_preimage_prod_right (mem_prod.mpr hz).1]
    replace hf'x_cont := hf'x_cont.mono hst
    replace hf'y_cont := hf'y_cont.mono hst
    -- now apply the weaker criteria to get differentiability
    apply hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open
      ⟨hz1,hz2⟩ ht
      hf'y_cont
      _ _
    · exact (hf'x z hz).mono (hsu z ⟨hz1,hz2⟩)
    · exact (fun z hz => (hf'y z (mem_of_subset_of_mem hst hz)).mono (htu z hz))

end PartialFDeriv
