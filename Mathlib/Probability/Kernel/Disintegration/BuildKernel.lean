/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.StieltjesReal
import Mathlib.Probability.Kernel.MeasureCompProd

/-!


-/


open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α]

section todo3

variable {α β : Type*} [MeasurableSpace α] {mβ : MeasurableSpace β}
  {f : α × β → ℚ → ℝ} {μ : kernel α (β × ℝ)} {ν : kernel α β}

structure IsRatKernelCDF (f : α × β → ℚ → ℝ) (μ : kernel α (β × ℝ)) (ν : kernel α β) : Prop :=
  (measurable (q : ℚ) : Measurable fun p ↦ f p q)
  (isRatStieltjesPoint_ae (a : α) : ∀ᵐ t ∂(ν a), IsRatStieltjesPoint f (a, t))
  (integrable (a : α) (q : ℚ) : Integrable (fun t ↦ f (a, t) q) (ν a))
  (isCDF (a : α) {s : Set β} (_hs : MeasurableSet s) (q : ℚ) :
    ∫ t in s, f (a, t) q ∂(ν a) = (μ a (s ×ˢ Iic (q : ℝ))).toReal)

structure IsKernelCDF (f : α × β → StieltjesFunction) (μ : kernel α (β × ℝ)) (ν : kernel α β) :
    Prop :=
  (measurable (x : ℝ) : Measurable fun p ↦ f p x)
  (integrable (a : α) (x : ℝ) : Integrable (fun t ↦ f (a, t) x) (ν a))
  (isCDF (a : α) {s : Set β} (_hs : MeasurableSet s) (x : ℝ) :
    ∫ t in s, f (a, t) x ∂(ν a) = (μ a (s ×ˢ Iic x)).toReal)

lemma todo3_ae_eq (hf : IsRatKernelCDF f μ ν) (a : α) (q : ℚ) :
    (fun t ↦ todo3 f hf.measurable (a, t) q) =ᵐ[ν a] fun t ↦ f (a, t) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [todo3_eq, toCDFLike_of_isRatStieltjesPoint ha]

lemma set_integral_todo3_rat (hf : IsRatKernelCDF f μ ν) (a : α) (q : ℚ)
    {s : Set β} (hs : MeasurableSet s) :
    ∫ t in s, todo3 f hf.measurable (a, t) q ∂(ν a) = (μ a (s ×ˢ Iic (q : ℝ))).toReal := by
  rw [set_integral_congr_ae hs (g := fun t ↦ f (a, t) q) ?_, hf.isCDF a hs]
  filter_upwards [todo3_ae_eq hf a q] with b hb using fun _ ↦ hb

lemma set_lintegral_todo3_rat [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) (q : ℚ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, ENNReal.ofReal (todo3 f hf.measurable (a, t) q) ∂(ν a) = μ a (s ×ˢ Iic (q : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [set_integral_todo3_rat hf a q hs, ENNReal.ofReal_toReal]
    exact measure_ne_top _ _
  · refine Integrable.restrict ?_
    rw [integrable_congr (todo3_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x ↦ todo3_nonneg _ _ _)

lemma set_lintegral_todo3_Iic [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, ENNReal.ofReal (todo3 f hf.measurable (a, t) x) ∂(ν a) = μ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_todo3_rat`.
  -- We use the equality `condCDF ρ a x = ⨅ r : {r' : ℚ // x < r'}, condCDF ρ a r` and a monotone
  -- convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices μ a (s ×ˢ Iic (q : ℝ)) = 0 by
      symm
      refine measure_mono_null (fun p ↦ ?_) this
      simp only [mem_prod, mem_Iic, and_imp]
      exact fun h1 h2 ↦ ⟨h1, h2.trans hq.le⟩
    suffices (μ a (s ×ˢ Iic (q : ℝ))).toReal = 0 by
      rw [ENNReal.toReal_eq_zero_iff] at this
      simpa [measure_ne_top] using this
    rw [← hf.isCDF a hs q]
    simp [hρ_zero]
  have h : ∫⁻ t in s, ENNReal.ofReal (todo3 f hf.measurable (a, t) x) ∂(ν a)
      = ∫⁻ t in s, ⨅ r : { r' : ℚ // x < r' },
        ENNReal.ofReal (todo3 f hf.measurable (a, t) r) ∂(ν a) := by
    congr with t : 1
    simp_rw [← measure_todo3_Iic]
    rw [← measure_iInter_eq_iInf]
    · congr with y : 1
      simp only [mem_Iic, mem_iInter, Subtype.forall]
      refine ⟨fun h a ha ↦ h.trans ?_, fun h ↦ ?_⟩
      · exact mod_cast ha.le
      · refine le_of_forall_lt_rat_imp_le fun q hq ↦ h q ?_
        exact mod_cast hq
    · exact fun _ ↦ measurableSet_Iic
    · refine Monotone.directed_ge fun r r' hrr' ↦ ?_
      refine Iic_subset_Iic.mpr ?_
      exact mod_cast hrr'
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      exact ⟨⟨q, hq⟩, measure_ne_top _ _⟩
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h, lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } ↦ ?_]
  rotate_left
  · intro b
    rw [set_lintegral_todo3_rat hf a _ hs]
    exact measure_ne_top _ _
  · refine Monotone.directed_ge fun i j hij t ↦ ?_
    simp_rw [← measure_todo3_Iic]
    refine measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
  · refine Measurable.ennreal_ofReal ?_
    exact (measurable_todo3 hf.measurable _).comp measurable_prod_mk_left
  simp_rw [set_lintegral_todo3_rat hf _ _ hs]
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq ↦ hyx.trans hq.le⟩
  · exact fun i ↦ hs.prod measurableSet_Iic
  · refine Monotone.directed_ge fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩


end todo3

section kernel

variable {f : α → ℚ → ℝ} {hf : ∀ q, Measurable fun a ↦ f a q}

noncomputable
def cdfKernel (f : α → ℚ → ℝ) (hf : ∀ q, Measurable fun a ↦ f a q) : kernel α ℝ where
  val a := (todo3 f hf a).measure
  property := measurable_measure_todo3 hf

instance instIsMarkovKernel_cdfKernel : IsMarkovKernel (cdfKernel f hf) :=
  ⟨fun _ ↦ instIsProbabilityMeasure_todo3 _ _⟩

lemma cdfKernel_Iic (a : α) (x : ℝ) :
    cdfKernel f hf a (Iic x) = ENNReal.ofReal (todo3 f hf a x) := measure_todo3_Iic hf a x

lemma cdfKernel_unit_prod_Iic (a : α) (x : ℝ) :
    cdfKernel (fun p : Unit × α ↦ f p.2) (fun q ↦ (hf q).comp measurable_snd) ((), a) (Iic x)
      = cdfKernel f hf a (Iic x) := by
  simp only [cdfKernel_Iic]
  rw [todo3_unit_prod hf a]

end kernel

section

variable {α β : Type*} [MeasurableSpace α] {mβ : MeasurableSpace β}
  {f : α × β → ℚ → ℝ} {μ : kernel α (β × ℝ)} {ν : kernel α β}

lemma set_lintegral_cdfKernel_Iic_rat [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) (q : ℚ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, cdfKernel f hf.measurable (a, t) (Iic q) ∂(ν a) = μ a (s ×ˢ Iic (q : ℝ)) := by
  simp_rw [cdfKernel_Iic, set_lintegral_todo3_rat hf a q hs]

lemma set_lintegral_cdfKernel_Iic [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, cdfKernel f hf.measurable (a, t) (Iic x) ∂(ν a) = μ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_cdfKernel_Iic_rat`.
  -- We use the equality `condCDF ρ a x = ⨅ r : {r' : ℚ // x < r'}, condCDF ρ a r` and a monotone
  -- convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices μ a (s ×ˢ Iic (q : ℝ)) = 0 by
      symm
      refine measure_mono_null (fun p ↦ ?_) this
      simp only [mem_prod, mem_Iic, and_imp]
      exact fun h1 h2 ↦ ⟨h1, h2.trans hq.le⟩
    suffices (μ a (s ×ˢ Iic (q : ℝ))).toReal = 0 by
      rw [ENNReal.toReal_eq_zero_iff] at this
      simpa [measure_ne_top] using this
    rw [← hf.isCDF a hs q]
    simp [hρ_zero]
  have h : ∫⁻ t in s, cdfKernel f hf.measurable (a, t) (Iic x) ∂(ν a)
      = ∫⁻ t in s, ⨅ r : { r' : ℚ // x < r' },
        cdfKernel f hf.measurable (a, t) (Iic r) ∂(ν a) := by
    congr with t : 1
    rw [← measure_iInter_eq_iInf]
    · congr with y : 1
      simp only [mem_Iic, mem_iInter, Subtype.forall]
      refine ⟨fun h a ha ↦ h.trans ?_, fun h ↦ ?_⟩
      · exact mod_cast ha.le
      · refine le_of_forall_lt_rat_imp_le fun q hq ↦ h q ?_
        exact mod_cast hq
    · exact fun _ ↦ measurableSet_Iic
    · refine Monotone.directed_ge fun r r' hrr' ↦ ?_
      refine Iic_subset_Iic.mpr ?_
      exact mod_cast hrr'
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      exact ⟨⟨q, hq⟩, measure_ne_top _ _⟩
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h, lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } ↦ ?_]
  rotate_left
  · intro b
    rw [set_lintegral_cdfKernel_Iic_rat hf a _ hs]
    exact measure_ne_top _ _
  · refine Monotone.directed_ge fun i j hij t ↦ measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
  · exact (kernel.measurable_coe _ measurableSet_Iic).comp measurable_prod_mk_left
  simp_rw [set_lintegral_cdfKernel_Iic_rat hf _ _ hs]
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq ↦ hyx.trans hq.le⟩
  · exact fun i ↦ hs.prod measurableSet_Iic
  · refine Monotone.directed_ge fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩

theorem Real.iUnion_Iic_rat' : ⋃ r : ℚ, Iic (r : ℝ) = univ := sorry

lemma set_lintegral_cdfKernel_univ [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, cdfKernel f hf.measurable (a, t) univ ∂(ν a) = μ a (s ×ˢ univ) := by
  rw [← Real.iUnion_Iic_rat', prod_iUnion]
  have h_dir : Directed (fun x y ↦ x ⊆ y) fun q : ℚ ↦ Iic (q : ℝ) := by
    refine Monotone.directed_le fun r r' hrr' ↦ Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  have h_dir_prod : Directed (fun x y ↦ x ⊆ y) fun q : ℚ ↦ s ×ˢ Iic (q : ℝ) := by
    refine Monotone.directed_le fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  simp_rw [measure_iUnion_eq_iSup h_dir, measure_iUnion_eq_iSup h_dir_prod]
  rw [lintegral_iSup_directed]
  · simp_rw [set_lintegral_cdfKernel_Iic hf _ _ hs]
  · refine fun q ↦ Measurable.aemeasurable ?_
    exact (kernel.measurable_coe _ measurableSet_Iic).comp measurable_prod_mk_left
  · refine Monotone.directed_le fun i j hij t ↦ measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij

lemma lintegral_cdfKernel_univ [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν) (a : α) :
    ∫⁻ t, cdfKernel f hf.measurable (a, t) univ ∂(ν a) = μ a univ := by
  rw [← set_lintegral_univ, set_lintegral_cdfKernel_univ hf a MeasurableSet.univ, univ_prod_univ]

lemma set_lintegral_cdfKernel_prod [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set ℝ} (ht : MeasurableSet t) :
    ∫⁻ x in s, cdfKernel f hf.measurable (a, x) t ∂(ν a) = μ a (s ×ˢ t) := by
  -- `set_lintegral_cdfKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  apply MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ ht
  · simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
  · rintro t ⟨q, rfl⟩
    exact set_lintegral_cdfKernel_Iic hf a _ hs
  · intro t ht ht_lintegral
    calc ∫⁻ x in s, cdfKernel f hf.measurable (a, x) tᶜ ∂(ν a)
      = ∫⁻ x in s, cdfKernel f hf.measurable (a, x) univ - cdfKernel f hf.measurable (a, x) t ∂(ν a) := by
          congr with x; rw [measure_compl ht (measure_ne_top (cdfKernel f hf.measurable (a, x)) _)]
    _ = ∫⁻ x in s, cdfKernel f hf.measurable (a, x) univ ∂(ν a)
          - ∫⁻ x in s, cdfKernel f hf.measurable (a, x) t ∂(ν a) := by
        rw [lintegral_sub]
        · exact (kernel.measurable_coe (cdfKernel f hf.measurable) ht).comp measurable_prod_mk_left
        · rw [ht_lintegral]
          exact measure_ne_top _ _
        · exact eventually_of_forall fun a ↦ measure_mono (subset_univ _)
    _ = μ a (s ×ˢ univ) - μ a (s ×ˢ t) := by
        rw [set_lintegral_cdfKernel_univ hf a hs, ht_lintegral]
    _ = μ a (s ×ˢ tᶜ) := by
        rw [← measure_diff _ (hs.prod ht) (measure_ne_top _ _)]
        · rw [prod_diff_prod, compl_eq_univ_diff]
          simp only [diff_self, empty_prod, union_empty]
        · rw [prod_subset_prod_iff]
          exact Or.inl ⟨subset_rfl, subset_univ t⟩
  · intro f hf_disj hf_meas hf_eq
    simp_rw [measure_iUnion hf_disj hf_meas]
    rw [lintegral_tsum, prod_iUnion, measure_iUnion]
    · simp_rw [hf_eq]
    · intro i j hij
      rw [Function.onFun, Set.disjoint_prod]
      exact Or.inr (hf_disj hij)
    · exact fun i ↦ MeasurableSet.prod hs (hf_meas i)
    · exact fun i ↦
        ((kernel.measurable_coe _ (hf_meas i)).comp measurable_prod_mk_left).aemeasurable.restrict

lemma lintegral_cdfKernel_mem [IsFiniteKernel μ] (hf : IsRatKernelCDF f μ ν)
    (a : α) {s : Set (β × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ x, cdfKernel f hf.measurable (a, x) {y | (x, y) ∈ s} ∂(ν a) = μ a s := by
  -- `set_lintegral_condKernelReal_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp only [mem_empty_iff_false, setOf_false, measure_empty, lintegral_const,
      zero_mul]
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_setOf_eq] at ht₁ ht₂
    have h_prod_eq_snd : ∀ a ∈ t₁, {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = t₂ := by
      intro a ha
      simp only [ha, prod_mk_mem_set_prod_eq, true_and_iff, setOf_mem_eq]
    rw [← lintegral_add_compl _ ht₁]
    have h_eq1 : ∫⁻ x in t₁, cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} ∂(ν a)
        = ∫⁻ x in t₁, cdfKernel f hf.measurable (a, x) t₂ ∂(ν a) := by
      refine' set_lintegral_congr_fun ht₁ (eventually_of_forall fun a ha ↦ _)
      rw [h_prod_eq_snd a ha]
    have h_eq2 : ∫⁻ x in t₁ᶜ, cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} ∂(ν a) = 0 := by
      suffices h_eq_zero : ∀ x ∈ t₁ᶜ, cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} = 0
      · rw [set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero)]
        simp only [lintegral_const, zero_mul]
      intro a hat₁
      rw [mem_compl_iff] at hat₁
      simp only [hat₁, prod_mk_mem_set_prod_eq, false_and_iff, setOf_false, measure_empty]
    rw [h_eq1, h_eq2, add_zero]
    exact set_lintegral_cdfKernel_prod hf a ht₁ ht₂
  · intro t ht ht_eq
    calc ∫⁻ x, cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ tᶜ} ∂(ν a)
      = ∫⁻ x, cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t}ᶜ ∂(ν a) := rfl
    _ = ∫⁻ x, cdfKernel f hf.measurable (a, x) univ
          - cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t} ∂(ν a) := by
        congr with x : 1
        exact measure_compl (measurable_prod_mk_left ht)
          (measure_ne_top (cdfKernel f hf.measurable (a, x)) _)
    _ = ∫⁻ x, cdfKernel f hf.measurable (a, x) univ ∂(ν a) -
          ∫⁻ x, cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t} ∂(ν a) := by
        have h_le : (fun x ↦ cdfKernel f hf.measurable (a, x) {y : ℝ | (x, y) ∈ t})
              ≤ᵐ[ν a] fun x ↦ cdfKernel f hf.measurable (a, x) univ :=
          eventually_of_forall fun _ ↦ measure_mono (subset_univ _)
        rw [lintegral_sub _ _ h_le]
        · exact kernel.measurable_kernel_prod_mk_left' ht a
        refine ((lintegral_mono_ae h_le).trans_lt ?_).ne
        rw [lintegral_cdfKernel_univ hf]
        exact measure_lt_top _ univ
    _ = μ a univ - μ a t := by rw [ht_eq, lintegral_cdfKernel_univ hf]
    _ = μ a tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
  · intro f' hf_disj hf_meas hf_eq
    have h_eq : ∀ a, {x | (a, x) ∈ ⋃ i, f' i} = ⋃ i, {x | (a, x) ∈ f' i} := by
      intro a; ext x; simp only [mem_iUnion, mem_setOf_eq]
    simp_rw [h_eq]
    have h_disj : ∀ a, Pairwise (Disjoint on fun i ↦ {x | (a, x) ∈ f' i}) := by
      intro a i j hij
      have h_disj := hf_disj hij
      rw [Function.onFun, disjoint_iff_inter_eq_empty] at h_disj ⊢
      ext1 x
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false_iff]
      intro h_mem_both
      suffices (a, x) ∈ ∅ by rwa [mem_empty_iff_false] at this
      rwa [← h_disj, mem_inter_iff]
    calc ∫⁻ x, cdfKernel f hf.measurable (a, x) (⋃ i, {y | (x, y) ∈ f' i}) ∂(ν a)
      = ∫⁻ x, ∑' i, cdfKernel f hf.measurable (a, x) {y | (x, y) ∈ f' i} ∂(ν a) := by
          congr with x : 1
          rw [measure_iUnion (h_disj x) fun i ↦ measurable_prod_mk_left (hf_meas i)]
    _ = ∑' i, ∫⁻ x, cdfKernel f hf.measurable (a, x) {y | (x, y) ∈ f' i} ∂(ν a) :=
          lintegral_tsum fun i ↦ (kernel.measurable_kernel_prod_mk_left' (hf_meas i) a).aemeasurable
    _ = ∑' i, μ a (f' i) := by simp_rw [hf_eq]
    _ = μ a (iUnion f') := (measure_iUnion hf_disj hf_meas).symm

lemma kernel.eq_compProd_cdfKernel [IsFiniteKernel μ] [IsSFiniteKernel ν]
    (hf : IsRatKernelCDF f μ ν) :
    μ = ν ⊗ₖ cdfKernel f hf.measurable := by
  ext a s hs
  rw [kernel.compProd_apply _ _ _ hs, lintegral_cdfKernel_mem hf a hs]

lemma ae_cdfKernel_eq_one [IsFiniteKernel μ] [IsSFiniteKernel ν] (hf : IsRatKernelCDF f μ ν) (a : α)
    {s : Set ℝ} (hs : MeasurableSet s) (hμs : μ a {x | x.snd ∈ sᶜ} = 0) :
    ∀ᵐ t ∂(ν a), cdfKernel f hf.measurable (a, t) s = 1 := by
  have h_eq : μ = ν ⊗ₖ cdfKernel f hf.measurable := kernel.eq_compProd_cdfKernel hf
  have h : μ a {x | x.snd ∈ sᶜ} = (ν ⊗ₖ cdfKernel f hf.measurable) a {x | x.snd ∈ sᶜ} := by
    rw [← h_eq]
  rw [hμs, kernel.compProd_apply] at h
  swap; · exact measurable_snd hs.compl
  rw [eq_comm, lintegral_eq_zero_iff] at h
  swap
  · simp only [mem_compl_iff, mem_setOf_eq]
    change Measurable ((fun p ↦ cdfKernel f _ p {c | c ∉ s}) ∘ (fun b : β ↦ (a, b)))
    exact (kernel.measurable_coe _ hs.compl).comp measurable_prod_mk_left
  simp only [mem_compl_iff, mem_setOf_eq, kernel.prodMkLeft_apply'] at h
  filter_upwards [h] with t ht
  change cdfKernel f hf.measurable (a, t) sᶜ = 0 at ht
  rwa [prob_compl_eq_zero_iff hs] at ht

lemma measurableSet_eq_one (hf : IsRatKernelCDF f μ ν) {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet {p | cdfKernel f hf.measurable p s = 1} :=
  (kernel.measurable_coe _ hs) (measurableSet_singleton 1)


end

end ProbabilityTheory
