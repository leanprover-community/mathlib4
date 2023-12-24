import Mathlib.Probability.Divergences.KullbackLeibler

open scoped ENNReal

open MeasureTheory Real

variable {α : Type*} {mα : MeasurableSpace α}

lemma set_integral_exp_neg_llr_le {μ ν : Measure α} [SigmaFinite ν] [SigmaFinite μ]
    (hμν : μ ≪ ν) (s : Set α) (hνs : ν s ≠ ∞) :
    ∫ x in s, exp (- LLR μ ν x) ∂μ ≤ (ν s).toReal := by
  set t := toMeasurable ν s with ht_eq
  have ht : MeasurableSet t := measurableSet_toMeasurable ν s
  have hνt : ν t ≠ ∞ := by rwa [ht_eq, measure_toMeasurable s]
  calc ∫ x in s, exp (- LLR μ ν x) ∂μ
    ≤ ∫ x in t, exp (- LLR μ ν x) ∂μ := by
        refine set_integral_mono_set ?_ ?_ (HasSubset.Subset.eventuallyLE (subset_toMeasurable _ _))
        · exact integrableOn_exp_neg_llr hμν t hνt
        · exact ae_of_all _ (fun _ ↦ (exp_pos _).le)
  _ = ∫ x in t, exp (LLR ν μ x) ∂μ := by
        refine set_integral_congr_ae ht ?_
        filter_upwards [neg_llr hμν] with x hx _
        rw [← hx]
        rfl
  _ = ∫ x in t, (ν.rnDeriv μ x).toReal ∂μ := by
        refine set_integral_congr_ae ht ?_
        filter_upwards [exp_llr ν μ, Measure.rnDeriv_pos' hμν] with x hx hx_pos _
        rw [hx]
        simp [hx_pos.ne']
  _ ≤ (ν t).toReal := Measure.set_integral_toReal_rnDeriv_le hνt
  _ = (ν s).toReal := by rw [measure_toMeasurable s]

-- todo: if `0 < c` then `hμc` can be deducted from an integrability assumption on `LLR μ ν`.
lemma todo' {μ ν : Measure α} [IsFiniteMeasure ν] [SigmaFinite μ] (hμν : μ ≪ ν)
    (s : Set α) (c : ℝ) (hμc : μ {x | LLR μ ν x > c} ≠ ∞) :
    (μ s).toReal - (μ {x | LLR μ ν x > c}).toReal ≤ (ν s).toReal * exp c := by
  by_cases hμs : μ s = ∞
  · simp only [hμs, ENNReal.top_toReal, gt_iff_lt, zero_sub]
    calc - (μ {x | LLR μ ν x > c}).toReal
      ≤ 0 := by simp
    _ ≤ (ν s).toReal * exp c := by positivity
  rw [← div_le_iff (exp_pos _), div_eq_mul_inv, ← exp_neg]
  calc ((μ s).toReal - (μ {x | LLR μ ν x > c}).toReal) * rexp (-c)
    ≤ (μ (s \ {x | LLR μ ν x > c})).toReal * rexp (-c) := by
        gcongr
        refine (ENNReal.le_toReal_sub hμc).trans ?_
        rw [ENNReal.toReal_le_toReal]
        · exact le_measure_diff
        · exact (tsub_le_self.trans_lt (Ne.lt_top hμs)).ne
        · exact ((measure_mono (Set.inter_subset_left _ _)).trans_lt (Ne.lt_top hμs)).ne
  _ = (μ (s ∩ {x | LLR μ ν x ≤ c})).toReal * rexp (-c) := by congr with x; simp
  _ = ∫ _ in s ∩ {x | LLR μ ν x ≤ c}, exp (- c) ∂μ := by rw [set_integral_const _, smul_eq_mul]
  _ ≤ ∫ x in s ∩ {x | LLR μ ν x ≤ c}, exp (- LLR μ ν x) ∂μ := by
        refine set_integral_mono_ae_restrict ?_ ?_ ?_
        · simp only [integrableOn_const]
          exact Or.inr ((measure_mono (Set.inter_subset_left _ _)).trans_lt (Ne.lt_top hμs))
        · refine Integrable.integrableOn ?_
          refine (integrable_congr (exp_neg_llr hμν)).mpr ?_
          exact Measure.integrable_toReal_rnDeriv
        · rw [Filter.EventuallyLE, ae_restrict_iff]
          · refine ae_of_all _ (fun x hxs ↦ ?_)
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hxs
            simp [hxs.2]
          · exact (measurable_llr _ _).neg.exp measurableSet_Ici
  _ ≤ (ν (s ∩ {x | LLR μ ν x ≤ c})).toReal := by
        refine set_integral_exp_neg_llr_le hμν (s ∩ {x | LLR μ ν x ≤ c}) ?_
        exact ((measure_mono (Set.inter_subset_left _ _)).trans_lt (measure_lt_top _ _)).ne
  _ ≤ (ν s).toReal := by
        rw [ENNReal.toReal_le_toReal _ (measure_ne_top _ _)]
        · exact measure_mono (Set.inter_subset_left _ _)
        · exact ((measure_mono (Set.inter_subset_left _ _)).trans_lt (measure_lt_top _ _)).ne

lemma measure_univ_le_add_compl {μ : Measure α} (s : Set α) :
    μ Set.univ ≤ μ s + μ sᶜ := by
  rw [← Set.union_compl_self s]
  exact measure_union_le s sᶜ

lemma todo {μ ν ν' : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsProbabilityMeasure μ]
    (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c c' : ℝ) :
    1 - (μ {x | LLR μ ν x > c}).toReal - (μ {x | LLR μ ν' x > c'}).toReal
      ≤ (ν s).toReal * exp c + (ν' sᶜ).toReal * exp c' := by
  have h := todo' hμν s c (measure_ne_top _ _)
  have h' := todo' hμν' sᶜ c' (measure_ne_top _ _)
  calc 1 - (μ {x | LLR μ ν x > c}).toReal
      - (μ {x | LLR μ ν' x > c'}).toReal
    ≤ (μ s).toReal + (μ sᶜ).toReal - (μ {x | LLR μ ν x > c}).toReal
      - (μ {x | LLR μ ν' x > c'}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        gcongr
        rw [← ENNReal.one_toReal, ← measure_univ (μ := μ), ENNReal.toReal_le_toReal]
        · exact measure_univ_le_add_compl s
        · exact measure_ne_top _ _
        · simp only [ne_eq, ENNReal.add_eq_top, measure_ne_top μ, or_self, not_false_eq_true]
  _ = ((μ s).toReal - (μ {x | LLR μ ν x > c}).toReal)
      + ((μ sᶜ).toReal - (μ {x | LLR μ ν' x > c'}).toReal) := by abel
  _ ≤ (ν s).toReal * exp c + (ν' sᶜ).toReal * exp c' := by gcongr

lemma todo'' {μ ν ν' : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsProbabilityMeasure μ]
    (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c c' : ℝ) :
    1 - (μ {x | LLR μ ν x > c}).toReal - (μ {x | LLR μ ν' x > c'}).toReal
      ≤ 2 * (max (ν s).toReal (ν' sᶜ).toReal) * exp (max c c') := by
  refine (todo hμν hμν' s c c').trans ?_
  rw [two_mul, add_mul]
  gcongr
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact le_max_right _ _

lemma todo''' {μ ν ν' : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsProbabilityMeasure μ]
    (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c : ℝ) :
    1 - (μ {x | LLR μ ν x > ∫ x, LLR μ ν x ∂μ + c}).toReal
        - (μ {x | LLR μ ν' x > ∫ x, LLR μ ν' x ∂μ + c}).toReal
      ≤ 2 * (max (ν s).toReal (ν' sᶜ).toReal)
        * exp (max (∫ x, LLR μ ν x ∂μ) (∫ x, LLR μ ν' x ∂μ) + c) := by
    calc _
      ≤ _ := todo'' hμν hμν' s (∫ x, LLR μ ν x ∂μ + c) (∫ x, LLR μ ν' x ∂μ + c)
    _ = 2 * (max (ν s).toReal (ν' sᶜ).toReal)
        * exp (max (∫ x, LLR μ ν x ∂μ) (∫ x, LLR μ ν' x ∂μ) + c) := by
          congr
          rw [max_add_add_right]
