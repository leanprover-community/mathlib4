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

* `HasFDerivWithinAt.continuousOn_open_prod_of_partial_continuousOn` ,
  `HasFDerivWithinAt.continuousOn_open_of_partial_continuousOn` : if `f` is differentiable
  on an open set `u`, such that the partial derivaties along `E` and `F` are continuous on `u`,
  then `f` is continuously differentiable on `E × F`. The first version has simplified
  hypotheses for wen `u = s ×ˢ t` is a product of open sets.

* `HasFDerivWithinAt.partial_continuousOn_of_continuousOn` ,
  `HasFDerivWithinAt.partial_continuous_of_continuousOn_prod` : if `f` is continuously
  differentiable within a set `u`, then it is partially differentiable `E` and `F` within `u`
  and its partial derivatives, given by restricting the derivative of `f`, are also
  continuous within `u`. This is the easier converse direction of the preceding result.

The proofs follow §9.8.1 from Dieudonné's *Foundations of Modern Analysis* (1969).
-/

open Set Function Metric Real

section PartialFDeriv

universe u_EF

theorem continuousOn_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set (X × Y)) : ContinuousOn Prod.swap s := by
  unfold ContinuousOn; intro z hz
  apply continuous_swap.continuousWithinAt

open ContinuousLinearMap in
theorem ContinousLinearMap.coprod_comp_prod
  (R : Type*) [Semiring R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  (M₃ : Type*) [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  (M₄ : Type*) [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄] [ContinuousAdd M₄]
  (f : M₂ →L[R] M₄) (g : M₃ →L[R] M₄) (f' : M →L[R] M₂) (g' : M →L[R] M₃) :
    (f.coprod g).comp  (f'.prod g') = f.comp f' + g.comp g' := by
  ext
  simp only [coe_comp', Function.comp_apply, prod_apply, coprod_apply, add_apply]

abbrev ContinuousLinearMap.swap
  (𝕜 : Type*) [Semiring 𝕜]
  (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
  (F : Type*) [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F]
  := (ContinuousLinearMap.snd 𝕜 E F).prod (ContinuousLinearMap.fst 𝕜 E F)

open ContinuousLinearMap in
theorem ContinousLinearMap.coprod_comp_swap
  (R : Type*) [Semiring R]
  (M₁ : Type*) [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd M]
  (f : M₁ →L[R] M) (g : M₂ →L[R] M) :
    (f.coprod g).comp (ContinuousLinearMap.swap R _ _) = (g.coprod f) := by
  ext; all_goals
  simp only [coe_comp', Function.comp_apply, inl_apply, inr_apply, prod_apply, coe_snd', coe_fst',
    coprod_apply, map_zero, zero_add, add_zero, coprod_comp_inl, coprod_comp_inr]

theorem hasFDerivWithinAt_swap
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (s : Set (E × F)) (z : E × F) :
    HasFDerivWithinAt
      (Prod.swap : E × F → F × E)
      (ContinuousLinearMap.swap 𝕜 E F)
      s z
  := hasFDerivWithinAt_snd.prodMk hasFDerivWithinAt_fst

/-- If a function `f : E × F → G` has partial derivatives `fx` and `fy` continuous
  on an open set `s ×ˢ t`, then `f` is continously differentiable on this set, with
  the deriative given by combining `fx` and `fy`.
-/
theorem HasFDerivWithinAt.continuousOn_open_prod_of_partial_continuousOn
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type u_EF} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type u_EF} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} (hs : IsOpen s) (ht : IsOpen t)
  {fx : E × F → E →L[𝕜] G} {fy : E × F → F →L[𝕜] G}
  (fxy_cont : ContinuousOn fx (s ×ˢ t) ∨ ContinuousOn fy (s ×ˢ t))
  (hfx : ∀ z ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (·, z.2)) (fx z) s z.1)
  (hfy : ∀ z ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (z.1, ·)) (fy z) t z.2) :
    ∀ z ∈ s ×ˢ t, HasFDerivWithinAt f ((fx z).coprod (fy z)) (s ×ˢ t) z := by
  -- if fx is continuous, WLOG swap the E and F arguments
  wlog fy_cont : ContinuousOn fy (s ×ˢ t)
  case inr =>
    have fx_cont := Or.resolve_right fxy_cont fy_cont
    clear fy_cont fxy_cont
    intro z hz
    simp only [mem_prod, Prod.fst_swap, Prod.snd_swap] at hz
    have hmt_st := mapsTo_swap_prod s t
    have hmt_ts := mapsTo_swap_prod t s
    have fx_swap_cont := fx_cont.comp (continuousOn_swap (t ×ˢ s)) hmt_ts
    have hswap := this
      (f := f ∘ Prod.swap)
      ht hs
      (Or.inr fx_swap_cont)
      (fun z' hz' => (hfy z'.swap (hmt_ts hz')))
      (fun z' hz' => (hfx z'.swap (hmt_ts hz')))
      fx_swap_cont
      z.swap hz.symm
    convert hswap.comp z (hasFDerivWithinAt_swap 𝕜 E F (s ×ˢ t) z) hmt_st
    simp only [ContinousLinearMap.coprod_comp_swap, comp_apply, Prod.swap_swap]
  -- now continue the proof with the default hypothesis that fy is continuous
  clear fxy_cont
  intro z hz
  replace hz : _ ∧ _ := ⟨mem_prod.mp hz, hz⟩
  simp only at hz
  have hfy_within := hfy -- save hypothesis hfy before rewriting it
  -- rewrite derivatives as limits using norms
  simp only [hasFDerivWithinAt_iff_tendsto, tendsto_nhdsWithin_nhds, dist_eq_norm] at ⊢ hfx hfy
  simp only [ContinuousLinearMap.coprod_apply, sub_zero, norm_mul, norm_inv, norm_norm] at ⊢ hfx hfy
  simp only [Metric.continuousOn_iff, dist_eq_norm, norm_eq_abs] at fy_cont
  -- get a target ε' and immediately shrink it to ε for convenice
  intro ε' hε'
  rw [show ε' = 2*(ε'/2/2/2) + 2*(ε'/2/2/2) + 2*(ε'/2/2/2) + 2*(ε'/2/2/2) by ring]
  have hε := half_pos (half_pos (half_pos hε'))
  set ε := ε' / 2 / 2 / 2
  -- get δx from x-differentiability and δy from continuity of y-derivative
  -- also δs and δt are constrained by the possibly small sizes of s and t
  obtain ⟨δx, hδx, hfx_z⟩ := hfx z hz.2 ε hε
  obtain ⟨δy, hδy, hfy_z⟩ := fy_cont z hz.2 ε hε
  obtain ⟨δs, hδs⟩ := isOpen_iff.mp hs z.1 hz.1.1
  obtain ⟨δt, hδt⟩ := isOpen_iff.mp ht z.2 hz.1.2
  use (min (min δx δs) (min δy δt)) -- derive desired δ
  constructor; · exact lt_min (lt_min hδx hδs.1) (lt_min hδy hδt.1) -- positivity of δ
  -- get working point (x,y) ∈ E × F within δ distance of z
  intro (x,y) hst hδ
  replace hst : _ ∧ _ := ⟨mem_prod.mp hst, hst⟩
  simp only at hst
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [mul_comm]
  -- simplify norm conditions into bounds on ‖x-z.1‖ and ‖y-z.2‖
  have hxx := hδ
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hxx
  simp only [lt_inf_iff, sup_lt_iff] at hxx
  replace ⟨⟨⟨hxx, hyx⟩, ⟨hxs, hys⟩⟩, ⟨⟨hxy, hyy⟩, ⟨hxt, hyt⟩⟩⟩ := hxx
  -- rewrite desired variation in f for easier estimation
  have hf := calc
    f (x,y) - f z - ((fx z) (x - z.1) + (fy z) (y - z.2))
      = f (x,y) - f (x,z.2)
      + f (x,z.2) - f (z.1,z.2) - ((fx z) (x - z.1) + (fy z) (y - z.2)) := by
        simp only [map_sub, sub_add_cancel, Prod.mk.eta]
    _ = f (x,y) - f (x,z.2) - (fy z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - (fx z) (x - z.1) := by
        rw [add_comm _ (fy _ _), ← sub_sub]
        rw [sub_right_comm _ _ (fy _ _), add_sub_right_comm _ _ (fy _ _)]
    _ = f (x,y) - f (x,z.2) - (fy (x,z.2)) (y - z.2)
      + (fy (x,z.2)) (y - z.2) - (fy z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - (fx z) (x - z.1) := by
        simp only [map_sub, Prod.mk.eta, sub_add_cancel]
    _ = f (x,y) - f (x,z.2) - (fy (x,z.2)) (y - z.2)
      + (fy (x,z.2) - fy z) (y - z.2)
      + f (x,z.2) - f (z.1,z.2) - (fx z) (x - z.1) := by
        rw [ContinuousLinearMap.sub_apply]
        simp only [map_sub, sub_add_cancel, Prod.mk.eta, sub_add_sub_cancel]
    _ = f (x,y) - f (x,z.2) - (fy (x,z.2)) (y - z.2)
      + (fy (x,z.2) - fy z) (y - z.2)
      + (f (x,z.2) - f (z.1,z.2) - (fx z) (x - z.1)) := by
        rw [add_sub_assoc _ (f _) _, add_sub_assoc _ ((f _) - _) _]
  -- set up the hypotheses and use the inequality version of the Mean Value Theorem
  have mvt_diff : ∀ y ∈ ball z.2 (min δy δt),
      HasFDerivWithinAt (f ∘ (x,·)) (fy (x,y)) (ball z.2 (min δy δt)) y := by
    intro y' hy'
    rw [mem_ball_iff_norm, lt_min_iff] at hy'
    apply (hfy_within (x,y') (mem_prod.mpr ⟨hst.1.1, _⟩)).mono
    · calc
        ball z.2 (min δy δt) ⊆ ball z.2 δt := ball_subset_ball (min_le_right _ _)
        _ ⊆ t := hδt.2
    · exact mem_of_subset_of_mem hδt.2 (mem_ball_iff_norm.mpr hy'.2)
  have mvt_bound : ∀ y' ∈ ball z.2 (min δy δt), ‖fy (x,y') - fy (x,z.2)‖ ≤ ε + ε := by
    intro y' hy'
    rw [mem_ball_iff_norm, lt_min_iff] at hy'
    rw [← dist_eq_norm]
    apply (dist_triangle _ (fy z) _).trans
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (fy z) _]
    have hxy' : ‖(x,y') - z‖ < δy := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sup_lt_iff]
      exact ⟨hxy, hy'.1⟩
    have hxz2 : ‖(x,z.2) - z‖ < δy := by
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
        sup_of_le_left]
      exact hxy
    apply add_le_add (hfy_z _ _ hxy').le (hfy_z _ _ hxz2).le
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
  -- use the calculation above and start applying norms and estimates, term by term
  rw [hf]
  replace hf := calc
    ‖f (x,y) - f (x,z.2) - (fy (x,z.2)) (y - z.2)
      + (fy (x,z.2) - fy z) (y - z.2)
      + (f (x,z.2) - f (z.1,z.2) - (fx z) (x - z.1))‖
      ≤ ‖f (x,y) - f (x,z.2) - (fy (x,z.2)) (y - z.2)‖
      + ‖(fy (x,z.2) - fy z) (y - z.2)‖
      + ‖(f (x,z.2) - f (z.1,z.2) - (fx z) (x - z.1))‖ := norm_add₃_le
    _ ≤ (ε + ε) * ‖y - z.2‖
      + ‖(fy (x,z.2) - fy z)‖ * ‖y - z.2‖
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
            exact (hfx_z hst.1.1 hxx).le -- apply differentiability estimate
    _ ≤ ε * ‖y - z.2‖ + ε * ‖y - z.2‖ + ε * ‖y - z.2‖ + ε * ‖x - z.1‖ := by
        rw [add_mul]
        apply add_le_add (add_le_add le_rfl _) le_rfl
        apply mul_le_mul (hfy_z _ _ _).le le_rfl (norm_nonneg (y - z.2)) hε.le
        · exact (mem_prod.mpr ⟨hst.1.1, hz.1.2⟩)
        · simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero, norm_nonneg,
          sup_of_le_left, hxy]
  -- now apply the estimate hf to the goal
  apply (mul_le_mul_of_nonneg_right hf (by simp only [inv_nonneg, norm_nonneg])).trans_lt _
  -- it remains only to simplify the inequality term by term and compare coefficients
  simp only [add_mul, mul_assoc]
  rw [mul_comm 2]
  apply add_lt_add (add_lt_add (add_lt_add _ _) _)
  all_goals
    apply (mul_lt_mul_left hε).mpr
    refine LE.le.trans_lt ?_ (one_lt_two)
    rw [mul_comm]
    apply inv_mul_le_of_le_mul₀ (norm_nonneg _) zero_le_one
    simp only [mul_one, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
    first | exact le_max_right _ _ | exact le_max_left _ _

/-- If a function `f : E × F → G` has partial derivatives `fx` and `fy` continuous
  on an open set `u`, then `f` is continously differentiable on this set, with
  the deriative given by combining `fx` and `fy`.

  See `HasFDerivWithinAt.continuousOn_open_prod_of_partial_continuousOn` for simplified
  version with `u = s ×ˢ t` being a product of two opens.
-/
theorem HasFDerivWithinAt.continuousOn_open_of_partial_continuousOn
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type u_EF} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type u_EF} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {u : Set (E × F)} (hu : IsOpen u)
  {fx : E × F → E →L[𝕜] G} {fy : E × F → F →L[𝕜] G}
  (fxy_cont : ContinuousOn fx u ∨ ContinuousOn fy u)
  (hfx : ∀ z ∈ u, HasFDerivWithinAt (f ∘ (·, z.2)) (fx z) ((·,z.2) ⁻¹' u) z.1)
  (hfy : ∀ z ∈ u, HasFDerivWithinAt (f ∘ (z.1, ·)) (fy z) ((z.1,·) ⁻¹' u) z.2) :
    ∀ z ∈ u, HasFDerivWithinAt f ((fx z).coprod (fy z)) u z := by
  intro z hz
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
  have fxy_cont_st : ContinuousOn fx (s ×ˢ t) ∨ ContinuousOn fy (s ×ˢ t) := by
    rcases fxy_cont with fx_cont | fy_cont
    · exact Or.inl (fx_cont.mono hst)
    · exact Or.inr (fy_cont.mono hst)
  apply HasFDerivWithinAt.continuousOn_open_prod_of_partial_continuousOn
    hs ht
    fxy_cont_st
    _ _
    z (mem_prod.mpr ⟨hz1, hz2⟩)
  · exact (fun z hz => (hfx z (mem_of_subset_of_mem hst hz)).mono (hsu z hz))
  · exact (fun z hz => (hfy z (mem_of_subset_of_mem hst hz)).mono (htu z hz))

/-- If `f : E × F → G` is continuously differentiable within a set `u`, then
  it is partially differentiable within `u` and its partial derivatives,
  obtained by restricting the total derivative of `f`, are also continuous on `u`.

  See `HasFDerivWithinAt.partial_continuousOn_of_continuousOn_prod` for a simplified
  version where `u = s ×ˢ t` is a product set.
-/
theorem HasFDerivWithinAt.partial_continuousOn_of_continuousOn
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {f' : E × F → E × F →L[𝕜] G} {u : Set (E × F)}
  (hfc : ContinuousOn f' u) (hf : ∀ z ∈ u, HasFDerivWithinAt f (f' z) u z) :
    let fx' := fun z => (f' z).comp (.inl _ _ _);
    let fy' := fun z => (f' z).comp (.inr _ _ _);
    (ContinuousOn fx' u ∧ ContinuousOn fy' u) ∧
    ( (∀ z ∈ u, HasFDerivWithinAt (f ∘ (· ,z.2)) (fx' z) ((·,z.2) ⁻¹' u) z.1)
    ∧ (∀ z ∈ u, HasFDerivWithinAt (f ∘ (z.1, ·)) (fy' z) ((z.1,·) ⁻¹' u) z.2) )
    := by
  set fx' := fun z => (f' z).comp (.inl _ _ _)
  set fy' := fun z => (f' z).comp (.inr _ _ _)
  refine ⟨?cont, ?diff⟩
  case cont =>
    rw [continuousOn_iff_continuous_restrict] at hfc ⊢
    rw [continuousOn_iff_continuous_restrict] at ⊢
    exact ⟨hfc.clm_comp_const _, hfc.clm_comp_const _⟩
  case diff =>
    rw [← forall₂_and]
    intro z hz
    have hz12 := (Prod.mk.eta (p := z)).symm ▸ hz
    set su := ((· ,z.2)) ⁻¹' u
    set tu := ((z.1, ·)) ⁻¹' u
    set fx := (f ∘ (· ,z.2))
    set fy := (f ∘ (z.1, ·))
    have hfx (x:E) := HasFDerivWithinAt.prodMk
      (hasFDerivWithinAt_id (𝕜 := 𝕜) x su)
      (hasFDerivWithinAt_const z.2 x su)
    have hfy (y:F) := HasFDerivWithinAt.prodMk
      (hasFDerivWithinAt_const z.1 y tu)
      (hasFDerivWithinAt_id (𝕜 := 𝕜) y tu)
    refine ⟨HasFDerivWithinAt.comp z.1 (hf (z.1,z.2) hz12) (hfx z.1) ?_,
      HasFDerivWithinAt.comp z.2 (hf (z.1,z.2) hz12) (hfy z.2) ?_⟩
    · exact fun ⦃_⦄ a ↦ a
    · exact fun ⦃_⦄ a ↦ a

/-- If `f : E × F → G` is continuously differentiable within a set `s ×ˢ t`, then
  it is partially differentiable within `s ×ˢ t` and its partial derivatives,
  obtained by restricting the total derivative of `f`, are also continuous on `s ×ˢ t`.
-/
theorem HasFDerivWithinAt.partial_continuousOn_of_continuousOn_prod
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {f' : E × F → E × F →L[𝕜] G} {s : Set E} {t : Set F}
  (hf : ∀ z ∈ s ×ˢ t, HasFDerivWithinAt f (f' z) (s ×ˢ t) z) (hfc : ContinuousOn f' (s ×ˢ t)) :
    let fx' := fun z => (f' z).comp (.inl _ _ _);
    let fy' := fun z => (f' z).comp (.inr _ _ _);
    (ContinuousOn fx' (s ×ˢ t) ∧ ContinuousOn fy' (s ×ˢ t)) ∧
    ( (∀ z ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (· ,z.2)) (fx' z) s z.1)
    ∧ (∀ z ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (z.1, ·)) (fy' z) t z.2) )
     := by
  refine ⟨?cont, ?diff⟩
  case cont =>
    rw [continuousOn_iff_continuous_restrict] at hfc ⊢
    rw [continuousOn_iff_continuous_restrict] at ⊢
    exact ⟨hfc.clm_comp_const _, hfc.clm_comp_const _⟩
  case diff =>
    rw [← forall₂_and]
    intro z hz
    have hsu : ((fun x ↦ (x, z.2)) ⁻¹' s ×ˢ t) = s := by
      exact mk_preimage_prod_left (mem_prod.mpr hz).2
    have htu : ((fun y ↦ (z.1, y)) ⁻¹' s ×ˢ t) = t := by
      exact mk_preimage_prod_right (mem_prod.mpr hz).1
    have := forall₂_and.mpr (HasFDerivWithinAt.partial_continuousOn_of_continuousOn hfc hf).2 z hz
    rw [hsu, htu] at this
    exact this

end PartialFDeriv
