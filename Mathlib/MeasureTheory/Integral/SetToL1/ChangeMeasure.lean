/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.SetToL1.Function

/-!
# Change of measure for set-to-function extensions

This file develops compatibility of `MeasureTheory.setToFun` with measurable maps and changes of
measure. It first proves approximation results using integrable simple functions, then compares
`setToFun` across dominated measures and establishes formulas for sums and scalar multiples of
measures.
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal

open Set Filter TopologicalSpace ENNReal

namespace MeasureTheory

variable {α E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  {m : MeasurableSpace α} {μ μ' μ'' : Measure α}

section Function

variable {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ} {f : α → E}

theorem tendsto_setToFun_approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C)
    [MeasurableSpace E] [BorelSpace E] {f : α → E} {s : Set E} [SeparableSpace s]
    (hfi : Integrable f μ) (hfm : Measurable f) (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E}
    (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f hfm s y₀ h₀ n)) atTop
      (𝓝 <| setToFun μ T hT f) :=
  tendsto_setToFun_of_L1 hT _ hfi.aestronglyMeasurable
    (Eventually.of_forall (SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i))
    (SimpleFunc.tendsto_approxOn_L1_enorm hfm _ hs (hfi.sub h₀i).2)

theorem tendsto_setToFun_approxOn_of_measurable_of_range_subset
    (hT : DominatedFinMeasAdditive μ T C) [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n)) atTop
      (𝓝 <| setToFun μ T hT f) := by
  refine tendsto_setToFun_approxOn_of_measurable hT hf fmeas ?_ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

theorem setToFun_of_le_map_of_stronglyMeasurable
    (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : MeasurableSpace β}
    {μ' : Measure β} {φ : α → β} {T' : Set β → E →L[ℝ] F} (hT' : DominatedFinMeasAdditive μ' T' C')
    {f : β → E} (hf : Integrable (f ∘ φ) μ) (hfm : StronglyMeasurable f) (hφ : Measurable φ)
    (hμ' : μ' ≤ μ.map φ)
    (h : ∀ (s : Set β) (x : E), MeasurableSet s → T' s x = T (φ ⁻¹' s) x) :
    setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hfi' : Integrable f μ' :=
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hf).mono_measure hμ'
  borelize E
  have : SeparableSpace (range f ∪ {0} : Set E) := hfm.separableSpace_range_union_singleton
  refine tendsto_nhds_unique
    (tendsto_setToFun_approxOn_of_measurable_of_range_subset
      hT' hfm.measurable hfi' _ Subset.rfl) ?_
  convert tendsto_setToFun_approxOn_of_measurable_of_range_subset
    hT (hfm.measurable.comp hφ) hf (range f ∪ {0})
    (union_subset_union_left {0} (range_comp_subset_range φ f)) using 1
  ext i : 1
  rw [setToFun_simpleFunc _ _ (SimpleFunc.integrable_approxOn_range _ hfi' _),
    setToFun_simpleFunc, SimpleFunc.approxOn_comp hfm.measurable hφ]; swap
  · apply SimpleFunc.integrable_approxOn _ hf (by simp) (by simp)
  simp only [union_singleton, SimpleFunc.measurableSet_preimage, h, ← preimage_comp,
    SimpleFunc.coe_comp]
  refine (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => ?_).symm
  rw [SimpleFunc.mem_range, ← Set.preimage_singleton_eq_empty, SimpleFunc.coe_comp] at hy
  simp [hy, hT.1.map_empty_eq_zero]

theorem setToFun_of_le_map
    (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : MeasurableSpace β}
    {μ' : Measure β} {φ : α → β} {T' : Set β → E →L[ℝ] F} (hT' : DominatedFinMeasAdditive μ' T' C')
    {f : β → E} (hf : Integrable (f ∘ φ) μ) (hfm : AEStronglyMeasurable f (μ.map φ))
    (hφ : Measurable φ) (hμ' : μ' ≤ μ.map φ)
    (h : ∀ (s : Set β) (x : E), MeasurableSet s → T' s x = T (φ ⁻¹' s) x) :
    setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ) := by
  let g := hfm.mk
  have A : setToFun μ' T' hT' f = setToFun μ' T' hT' g :=
    setToFun_congr_ae _ (ae_mono hμ' hfm.ae_eq_mk)
  have B : setToFun μ T hT (f ∘ φ) = setToFun μ T hT (g ∘ φ) := by
    apply setToFun_congr_ae
    exact ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk
  rw [A, B]
  exact setToFun_of_le_map_of_stronglyMeasurable _ _
    (hf.congr (ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk)) hfm.stronglyMeasurable_mk hφ hμ' h

/-- Auxiliary lemma for `setToFun_congr_measure`: the function sending `f : α →₁[μ] G` to
`f : α →₁[μ'] G` is continuous when `μ' ≤ c' • μ` for `c' ≠ ∞`. -/
theorem continuous_L1_toL1 {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞) (hμ'_le : μ' ≤ c' • μ) :
    Continuous fun f : α →₁[μ] G =>
      (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f := by
  by_cases hc'0 : c' = 0
  · have hμ'0 : μ' = 0 := by rw [← Measure.nonpos_iff_eq_zero']; refine hμ'_le.trans ?_; simp [hc'0]
    have h_im_zero :
      (fun f : α →₁[μ] G =>
          (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f) =
        0 := by
      ext1 f; ext1; simp_rw [hμ'0]; simp only [ae_zero, EventuallyEq, eventually_bot]
    rw [h_im_zero]
    exact continuous_zero
  rw [Metric.continuous_iff]
  intro f ε hε_pos
  use ε / 2 / c'.toReal
  refine ⟨div_pos (half_pos hε_pos) (toReal_pos hc'0 hc'), ?_⟩
  intro g hfg
  rw [Lp.dist_def] at hfg ⊢
  let h_int := fun f' : α →₁[μ] G => (L1.integrable_coeFn f').of_measure_le_smul hc' hμ'_le
  have :
    eLpNorm (⇑(Integrable.toL1 g (h_int g)) - ⇑(Integrable.toL1 f (h_int f))) 1 μ' =
      eLpNorm (⇑g - ⇑f) 1 μ' :=
    eLpNorm_congr_ae ((Integrable.coeFn_toL1 _).sub (Integrable.coeFn_toL1 _))
  rw [this]
  have h_eLpNorm_ne_top : eLpNorm (⇑g - ⇑f) 1 μ ≠ ∞ := by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _)]; exact Lp.eLpNorm_ne_top _
  calc
    (eLpNorm (⇑g - ⇑f) 1 μ').toReal ≤ (c' * eLpNorm (⇑g - ⇑f) 1 μ).toReal := by
      refine toReal_mono (ENNReal.mul_ne_top hc' h_eLpNorm_ne_top) ?_
      refine (eLpNorm_mono_measure (⇑g - ⇑f) hμ'_le).trans_eq ?_
      rw [eLpNorm_smul_measure_of_ne_zero hc'0, smul_eq_mul]
      simp
    _ = c'.toReal * (eLpNorm (⇑g - ⇑f) 1 μ).toReal := toReal_mul
    _ ≤ c'.toReal * (ε / 2 / c'.toReal) := by gcongr
    _ = ε / 2 := by
      refine mul_div_cancel₀ (ε / 2) ?_; rw [Ne, toReal_eq_zero_iff]; simp [hc', hc'0]
    _ < ε := half_lt_self hε_pos

theorem setToFun_congr_measure_of_integrable {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞)
    (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) (hfμ : Integrable f μ) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : ∀ g : α → E, Integrable g μ → Integrable g μ' := fun g hg =>
    Integrable.of_measure_le_smul hc' hμ'_le hg
  -- We use `Integrable.induction`
  apply hfμ.induction (P := fun f => setToFun μ T hT f = setToFun μ' T hT' f)
  · intro c s hs hμs
    have hμ's : μ' s ≠ ∞ := by
      refine ((hμ'_le s).trans_lt ?_).ne
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc'.lt_top hμs
    rw [setToFun_indicator_const hT hs hμs.ne, setToFun_indicator_const hT' hs hμ's]
  · intro f₂ g₂ _ hf₂ hg₂ h_eq_f h_eq_g
    rw [setToFun_add hT hf₂ hg₂, setToFun_add hT' (h_int f₂ hf₂) (h_int g₂ hg₂), h_eq_f, h_eq_g]
  · refine isClosed_eq (continuous_setToFun hT) ?_
    have :
      (fun f : α →₁[μ] E => setToFun μ' T hT' f) = fun f : α →₁[μ] E =>
        setToFun μ' T hT' ((h_int f (L1.integrable_coeFn f)).toL1 f) := by
      ext1 f; exact setToFun_congr_ae hT' (Integrable.coeFn_toL1 _).symm
    rw [this]
    exact (continuous_setToFun hT').comp (continuous_L1_toL1 c' hc' hμ'_le)
  · intro f₂ g₂ hfg _ hf_eq
    have hfg' : f₂ =ᵐ[μ'] g₂ := (Measure.absolutelyContinuous_of_le_smul hμ'_le).ae_eq hfg
    rw [← setToFun_congr_ae hT hfg, hf_eq, setToFun_congr_ae hT' hfg']

theorem setToFun_congr_measure {μ' : Measure α} (c c' : ℝ≥0∞) (hc : c ≠ ∞) (hc' : c' ≠ ∞)
    (hμ_le : μ ≤ c • μ') (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hf : Integrable f μ
  · exact setToFun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
  · -- if `f` is not integrable, both `setToFun` are 0.
    have h_int : ∀ g : α → E, ¬Integrable g μ → ¬Integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul hc hμ_le
    simp_rw [setToFun_undef _ hf, setToFun_undef _ (h_int f hf)]

theorem setToFun_congr_measure_of_add_right {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ T C)
    (f : α → E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ T hT f := by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← add_zero μ]
  exact add_le_add le_rfl bot_le

theorem setToFun_congr_measure_of_add_left {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ' T C)
    (f : α → E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ' T hT f := by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  exact Measure.le_add_left le_rfl

theorem setToFun_add_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
    (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrable f ν) :
    setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f =
      setToFun μ T hTμ f + setToFun ν T' hTν f :=
  have hTμ_add : DominatedFinMeasAdditive (μ + ν) T (max C 0) :=
    (hTμ.of_le (le_max_left C 0)).add_measure_right μ ν (le_max_right C 0)
  have hTν_add : DominatedFinMeasAdditive (μ + ν) T' (max C' 0) :=
    (hTν.of_le (le_max_left C' 0)).add_measure_left μ ν (le_max_right C' 0)
  calc
    setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f =
      setToFun (μ + ν) T hTμ_add f + setToFun (μ + ν) T' hTν_add f :=
        setToFun_add_left hTμ_add hTν_add f
    _ = setToFun μ T hTμ f + setToFun ν T' hTν f := by
      rw [setToFun_congr_measure_of_add_right hTμ_add hTμ f (hμ.add_measure hν),
        setToFun_congr_measure_of_add_left hTν_add hTν f (hμ.add_measure hν)]

theorem setToFun_sub_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
    (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrable f ν) :
    setToFun (μ + ν) (T - T') (hTμ.sub_measure μ ν hTν) f =
      setToFun μ T hTμ f - setToFun ν T' hTν f := by
  simp [sub_eq_add_neg, setToFun_add_measure hTμ hTν.neg hμ hν, setToFun_neg' hTν]

theorem setToFun_finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty)
    {μ : ι → Measure α} {T : ι → Set α → E →L[ℝ] F} {C : ι → ℝ}
    (hTs : ∀ i, DominatedFinMeasAdditive (μ i) (T i) (C i))
    (hf : ∀ i ∈ s, Integrable f (μ i)) :
    setToFun (∑ i ∈ s, μ i) (∑ i ∈ s, T i)
      (DominatedFinMeasAdditive.finsetSum_measure hs μ T C hTs) f =
      ∑ i ∈ s, setToFun (μ i) (T i) (hTs i) f := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | @cons i s his hs' ih =>
    simpa [his, ih fun j hj => hf j (Finset.mem_cons_of_mem hj)] using!
      setToFun_add_measure (hTs i) (DominatedFinMeasAdditive.finsetSum_measure hs' μ T C hTs)
      (hf i (Finset.mem_cons_self i s))
      (integrable_finsetSum_measure.2 fun j hj => hf j (Finset.mem_cons_of_mem hj))

theorem setToFun_top_smul_measure (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α → E) :
    setToFun (∞ • μ) T hT f = 0 := by
  refine setToFun_measure_zero' hT fun s _ hμs => ?_
  rw [lt_top_iff_ne_top] at hμs
  simp only [true_and, Measure.smul_apply, ENNReal.mul_eq_top,
    top_ne_zero, Ne, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs
  simp only [hμs.right, Measure.smul_apply, mul_zero, smul_eq_mul]

theorem setToFun_congr_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α → E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  by_cases hc0 : c = 0
  · simp [hc0] at hT_smul
    have h : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0 := fun s hs _ => hT_smul.eq_zero hs
    rw [setToFun_zero_left' _ h, setToFun_measure_zero]
    simp [hc0]
  refine setToFun_congr_measure c⁻¹ c ?_ hc_ne_top (le_of_eq ?_) le_rfl hT hT_smul f
  · simp [hc0]
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]

theorem setToFun_congr_smul_measure' (c : ℝ≥0)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α → E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  rw! [ENNReal.smul_def]
  apply setToFun_congr_smul_measure _ (by simp)

/-- `setToFun` applied to the sum `T + T'` of two operators is the sum of the corresponding
`setToFun`. -/
theorem setToFun_add_left'' {hT : DominatedFinMeasAdditive μ T C}
    {hT' : DominatedFinMeasAdditive μ' T' C'} {hT'' : DominatedFinMeasAdditive μ'' T'' C''}
    (h : ∀ s, MeasurableSet s → (μ + μ') s < ∞ → T'' s = T s + T' s)
    (hf : Integrable f μ) (hf' : Integrable f μ') (hμ : μ'' ≤ μ + μ')
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hC'' : 0 ≤ C'') :
    setToFun μ'' T'' hT'' f = setToFun μ T hT f + setToFun μ' T' hT' f := by
  have I : DominatedFinMeasAdditive (μ + μ') T C := .add_measure_right _ _ hT hC
  have A : setToFun (μ + μ') T I f = setToFun μ T hT f :=
    setToFun_congr_measure_of_add_right _ _ _ (hf.add_measure hf')
  have I' : DominatedFinMeasAdditive (μ + μ') T' C' := .add_measure_left _ _ hT' hC'
  have A' : setToFun (μ + μ') T' I' f = setToFun μ' T' hT' f :=
    setToFun_congr_measure_of_add_left _ _ _ (hf.add_measure hf')
  have I'' : DominatedFinMeasAdditive (μ + μ') T'' C'' := .of_measure_le hμ hT'' hC''
  have A'' : setToFun (μ + μ') T'' I'' f = setToFun μ'' T'' hT'' f := by
    apply setToFun_congr_measure_of_integrable (c' := 1) (by simp) (by simpa using hμ)
    apply hf.add_measure hf'
  rw [← A, ← A', ← A'']
  apply setToFun_add_left' _ _ _ h


end Function

end MeasureTheory
