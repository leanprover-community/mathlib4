/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.SetToL1.L1

/-!
# Extension of set functions to integrable functions

This file defines `MeasureTheory.setToFun`, the function-level version of
`MeasureTheory.L1.setToL1`. It applies the L¹ extension to an integrable function and is defined
to be zero when the function is not integrable or the target is not complete.

The file proves the core algebraic, congruence, order, indicator, simple-function, and continuity
properties of `setToFun`, including continuity under convergence in L¹.
-/

@[expose] public section

noncomputable section

open scoped Topology

open Set Filter ENNReal

namespace MeasureTheory

variable {α E F 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

section Function

variable {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ} {f g : α → E}
variable (μ T)

open scoped Classical in
/-- Extend `T : Set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E`). We set it to
0 if the function is not integrable or if the target space is not complete. -/
def setToFun (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F :=
  if _hF : CompleteSpace F then
    if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
  else 0

variable {μ T}

theorem setToFun_eq [hF : CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT f = L1.setToL1 hT (hf.toL1 f) := by
  simp [setToFun, hF, hf]

theorem L1.setToFun_eq_setToL1 [CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    setToFun μ T hT f = L1.setToL1 hT f := by
  rw [setToFun_eq hT (L1.integrable_coeFn f), Integrable.toL1_coeFn]

theorem setToFun_undef (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ) :
    setToFun μ T hT f = 0 := by
  by_cases hF : CompleteSpace F
  · simp [setToFun, hF, hf]
  · simp [setToFun, hF]

theorem setToFun_non_aestronglyMeasurable (hT : DominatedFinMeasAdditive μ T C)
    (hf : ¬AEStronglyMeasurable f μ) : setToFun μ T hT f = 0 :=
  setToFun_undef hT (not_and_of_not_left _ hf)

theorem setToFun_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α → E) :
    setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

theorem setToFun_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α → E) : setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left' T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

theorem setToFun_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α → E) :
    setToFun μ (T + T') (hT.add hT') f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left hT hT']
  · simp_rw [setToFun_undef _ hf, add_zero]

/-- `setToFun` applied to the sum `T + T'` of two operators is the sum of the corresponding
`setToFun`. See also `setToFun_add_left'` for a version varying the reference measures. -/
theorem setToFun_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α → E) :
    setToFun μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left' hT hT' hT'' h_add]
  · simp_rw [setToFun_undef _ hf, add_zero]

theorem setToFun_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α → E) :
    setToFun μ (fun s => c • T s) (hT.smul c) f = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left hT c]
  · simp_rw [setToFun_undef _ hf, smul_zero]

theorem setToFun_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α → E) :
    setToFun μ T' hT' f = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left' hT hT' c h_smul]
  · simp_rw [setToFun_undef _ hf, smul_zero]

@[simp]
theorem setToFun_zero (hT : DominatedFinMeasAdditive μ T C) : setToFun μ T hT (0 : α → E) = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (integrable_zero _ _ _), Integrable.toL1_zero, map_zero]

@[simp]
theorem setToFun_zero_left {hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C} :
    setToFun μ 0 hT f = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left hT _
  · exact setToFun_undef hT hf

theorem setToFun_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) : setToFun μ T hT f = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left' hT h_zero _
  · exact setToFun_undef hT hf

theorem setToFun_add (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (hf.add hg), setToFun_eq hT hf, setToFun_eq hT hg, Integrable.toL1_add,
    (L1.setToL1 hT).map_add]

theorem setToFun_finsetSum' (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι)
    {f : ι → α → E} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    setToFun μ T hT (∑ i ∈ s, f i) = ∑ i ∈ s, setToFun μ T hT (f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [setToFun_zero, Finset.sum_empty]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    rw [setToFun_add hT (hf i (Finset.mem_insert_self i s)) _]
    · rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    · convert! integrable_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi) with x
      simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum' := setToFun_finsetSum'

theorem setToFun_finsetSum (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (setToFun μ T hT fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, setToFun μ T hT (f i) := by
  convert! setToFun_finsetSum' hT s hf with a; simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum := setToFun_finsetSum

theorem setToFun_neg (hT : DominatedFinMeasAdditive μ T C) (f : α → E) :
    setToFun μ T hT (-f) = -setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT hf.neg, Integrable.toL1_neg,
      (L1.setToL1 hT).map_neg]
  · rw [setToFun_undef hT hf, setToFun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf

theorem setToFun_neg' (hT : DominatedFinMeasAdditive μ T C) (f : α → E) :
    setToFun μ (-T) hT.neg f = -setToFun μ T hT f := by
  simpa using setToFun_smul_left' hT hT.neg (-1) (by simp) f

theorem setToFun_sub (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, setToFun_add hT hf hg.neg, setToFun_neg hT g]

theorem setToFun_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [Module 𝕜 F] [NormSMulClass 𝕜 F]
    (hT : DominatedFinMeasAdditive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α → E) : setToFun μ T hT (c • f) = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT (hf.smul c), Integrable.toL1_smul' f hf,
      L1.setToL1_smul hT h_smul c]
  · by_cases hr : c = 0
    · rw [hr]; simp
    · have hf' : ¬Integrable (c • f) μ := by rwa [integrable_smul_iff hr f]
      rw [setToFun_undef hT hf, setToFun_undef hT hf', smul_zero]

theorem setToFun_congr_ae (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g) :
    setToFun μ T hT f = setToFun μ T hT g := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ := hfi.congr h
    rw [setToFun_eq hT hfi, setToFun_eq hT hgi, (Integrable.toL1_eq_toL1_iff f g hfi hgi).2 h]
  · have hgi : ¬Integrable g μ := by rw [integrable_congr h] at hfi; exact hfi
    rw [setToFun_undef hT hfi, setToFun_undef hT hgi]

theorem setToFun_measure_zero (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0) :
    setToFun μ T hT f = 0 := by
  have : f =ᵐ[μ] 0 := by simp [h, EventuallyEq]
  rw [setToFun_congr_ae hT this, setToFun_zero]

theorem setToFun_measure_zero' (hT : DominatedFinMeasAdditive μ T C)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → μ s = 0) : setToFun μ T hT f = 0 :=
  setToFun_zero_left' hT fun s hs hμs => hT.eq_zero_of_measure_zero hs (h s hs hμs)

theorem setToFun_toL1 (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT (hf.toL1 f) = setToFun μ T hT f :=
  setToFun_congr_ae hT hf.coeFn_toL1

theorem setToFun_indicator_const [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToFun μ T hT (s.indicator fun _ => x) = T s x := by
  rw [setToFun_congr_ae hT (@indicatorConstLp_coeFn _ _ _ 1 _ _ _ hs hμs x).symm]
  rw [L1.setToFun_eq_setToL1 hT]
  exact L1.setToL1_indicatorConstLp hT hs hμs x

theorem setToFun_const [CompleteSpace F] [IsFiniteMeasure μ]
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    (setToFun μ T hT fun _ => x) = T univ x := by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  rw [this]
  exact setToFun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x

theorem setToFun_simpleFunc [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C)
    (f : SimpleFunc α E) (hf : Integrable f μ) :
    setToFun μ T hT f = ∑ x ∈ f.range, T (f ⁻¹' {x}) x := by
  have h'f : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  let g := f.toLp h'f
  have A : f =ᵐ[μ] g := h'f.coeFn_toLp.symm
  rw [setToFun_congr_ae hT A, L1.setToFun_eq_setToL1 hT, L1.setToL1_eq_setToL1SCLM]
  apply (SimpleFunc.setToSimpleFunc_congr T (fun s ↦ hT.eq_zero_of_measure_zero) hT.1 hf _).symm
  grw [A, Lp.simpleFunc.toSimpleFunc_eq_toFun]

theorem setToFun_simpleFunc_eq_setToSimpleFunc [CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (f : SimpleFunc α E) (hf : Integrable f μ) :
    setToFun μ T hT f = f.setToSimpleFunc T := by
  rw [setToFun_simpleFunc hT f hf]
  rfl

section Order

-- Naming chosen to match the corresponding declarations in `L1.lean`.
variable {G' G'' : Type*}
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace ℝ G']
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G'']
  [NormedSpace ℝ G'']

theorem setToFun_mono_left' [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α → E) :
    setToFun μ T hT f ≤ setToFun μ T' hT' f := by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf]; exact L1.setToL1_mono_left' hT hT' hTT' _
  · simp_rw [setToFun_undef _ hf, le_rfl]

theorem setToFun_mono_left [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToFun μ T hT f ≤ setToFun μ T' hT' f :=
  setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

theorem setToFun_nonneg [ClosedIciTopology G''] {T : Set α → G' →L[ℝ] G''} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α → G'}
    (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f := by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hfi : Integrable f μ
  · simp_rw [setToFun_eq _ hfi]
    exact L1.setToL1_nonneg hT hT_nonneg hf
  · simp_rw [setToFun_undef _ hfi, le_rfl]

theorem setToFun_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G']
    {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α → G'}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    setToFun μ T hT f ≤ setToFun μ T hT g := by
  rw [← sub_nonneg, ← setToFun_sub hT hg hf]
  refine setToFun_nonneg hT hT_nonneg (hfg.mono fun a ha => ?_)
  rw [Pi.sub_apply, Pi.zero_apply, sub_nonneg]
  exact ha

end Order

@[continuity]
theorem continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) :
    Continuous fun f : α →₁[μ] E => setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF, continuous_const]
  simp_rw [L1.setToFun_eq_setToL1 hT]; exact ContinuousLinearMap.continuous _

/-- If `F i → f` in `L1`, then `setToFun μ T hT (F i) → setToFun μ T hT f`. -/
theorem tendsto_setToFun_of_L1 (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α → E)
    (hf : AEStronglyMeasurable f μ) {fs : ι → α → E} {l : Filter ι}
    (hfsi : ∀ᶠ i in l, Integrable (fs i) μ)
    (hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => setToFun μ T hT (fs i)) l (𝓝 <| setToFun μ T hT f) := by
  classical
  rcases eq_or_neBot l with rfl | hl
  · simp
  have hfi : Integrable f μ := by
    obtain ⟨i, hi, h'i⟩ : ∃ i, ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ < 1 ∧ Integrable (fs i) μ :=
      (((tendsto_order.1 hfs).2 _ zero_lt_one).and hfsi).exists
    have : Integrable (fs i - f) μ := ⟨h'i.aestronglyMeasurable.sub hf, hi.trans one_lt_top⟩
    convert h'i.sub this
    abel
  let f_lp := hfi.toL1 f
  let F_lp i := if hFi : Integrable (fs i) μ then hFi.toL1 (fs i) else 0
  have tendsto_L1 : Tendsto F_lp l (𝓝 f_lp) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply]
    refine (tendsto_congr' ?_).mp hfs
    filter_upwards [hfsi] with i hi
    refine lintegral_congr_ae ?_
    filter_upwards [hi.coeFn_toL1, hfi.coeFn_toL1] with x hxi hxf
    simp_rw [F_lp, dite_eq_left hi, hxi, f_lp, hxf]
  suffices Tendsto (fun i => setToFun μ T hT (F_lp i)) l (𝓝 (setToFun μ T hT f)) by
    refine (tendsto_congr' ?_).mp this
    filter_upwards [hfsi] with i hi
    suffices h_ae_eq : F_lp i =ᵐ[μ] fs i from setToFun_congr_ae hT h_ae_eq
    simp_rw [F_lp, dite_eq_left hi]
    exact hi.coeFn_toL1
  rw [setToFun_congr_ae hT hfi.coeFn_toL1.symm]
  exact ((continuous_setToFun hT).tendsto f_lp).comp tendsto_L1


end Function

end MeasureTheory
