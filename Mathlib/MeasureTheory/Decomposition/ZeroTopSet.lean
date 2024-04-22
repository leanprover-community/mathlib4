/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
# ZeroTopSet

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Set α}

namespace Measure

theorem iSup_restrict_spanningSets'' [SigmaFinite μ] (s : Set α) :
    ⨆ i, μ.restrict (spanningSets μ i) (toMeasurable μ s) = μ s := by
  rw [← measure_toMeasurable s, iSup_restrict_spanningSets (measurableSet_toMeasurable _ _)]

theorem iSup_restrict_spanningSets' [SigmaFinite μ] (s : Set α) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s := by
  rw [← measure_toMeasurable s, ← iSup_restrict_spanningSets (measurableSet_toMeasurable _ _)]
  simp_rw [restrict_apply' (measurable_spanningSets μ _), Set.inter_comm s,
    ← restrict_apply (measurable_spanningSets μ _), ← restrict_toMeasurable_of_sFinite s,
    restrict_apply (measurable_spanningSets μ _), Set.inter_comm _ (toMeasurable μ s)]

lemma absolutelyContinuous_sum_left {ι : Type*} {ν : Measure α} {μs : ι → Measure α}
    (hμs : ∀ i, μs i ≪ ν) :
    Measure.sum μs ≪ ν :=
  AbsolutelyContinuous.mk fun s hs hs0 ↦ by simp [sum_apply _ hs, fun i ↦ hμs i hs0]

lemma absolutelyContinuous_sum_right {ι : Type*} {ν : Measure α} {μs : ι → Measure α} (i : ι)
    (hνμ : ν ≪ μs i) :
    ν ≪ Measure.sum μs := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)

instance instSFiniteRestrict (μ : Measure α) [SFinite μ] (s : Set α) :
    SFinite (μ.restrict s) := by
  refine ⟨fun n ↦ (sFiniteSeq μ n).restrict s, fun n ↦ inferInstance, ?_⟩
  rw [← restrict_sum_of_countable, sum_sFiniteSeq]

/-! ### SFinite measures can be written as withDensity of a finite measure -/

open Classical in
noncomputable
def toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  Measure.sum (fun n ↦ if sFiniteSeq μ n ≠ 0
    then (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ • sFiniteSeq μ n
    else 0)

lemma toFinite_apply (μ : Measure α) [SFinite μ] [∀ n, Decidable (sFiniteSeq μ n ≠ 0)]
    (hs : MeasurableSet s) :
    toFinite μ s
      = ∑' n, if sFiniteSeq μ n ≠ 0
        then (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ * sFiniteSeq μ n s else 0 := by
  rw [toFinite, sum_apply _ hs]
  congr with n
  split_ifs with h <;> congr

lemma sFiniteSet_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : ℕ) :
    sFiniteSeq μ n ≪ toFinite μ := by
  refine absolutelyContinuous_sum_right n ?_
  split_ifs with h0
  · refine absolutelyContinuous_smul ?_
    simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · rw [ne_eq, not_not] at h0
    simp [h0]

lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] :
    μ ≪ toFinite μ := by
  conv_lhs => rw [← sum_sFiniteSeq μ]
  exact absolutelyContinuous_sum_left (sFiniteSet_absolutelyContinuous_toFinite μ)

lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] :
    toFinite μ ≪ μ := by
  conv_rhs => rw [← sum_sFiniteSeq μ]
  refine AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  classical
  simp [toFinite_apply _ hs, hs0]

lemma toFinite_univ_le_one (μ : Measure α) [SFinite μ] :
    toFinite μ Set.univ ≤ 1 := by
  classical
  rw [toFinite_apply _ MeasurableSet.univ]
  have h_le_pow : ∀ n, (if sFiniteSeq μ n ≠ 0
        then (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ * sFiniteSeq μ n Set.univ else 0)
      ≤ (2 ^ (n + 1))⁻¹ := by
    intro n
    split_ifs with h
    · simp only [ENNReal.le_inv_iff_mul_le]
      rw [mul_assoc, mul_comm (sFiniteSeq μ n Set.univ), ENNReal.inv_mul_cancel]
      · simp [h]
      · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    · exact zero_le'
  refine (tsum_le_tsum h_le_pow ENNReal.summable ENNReal.summable).trans ?_
  simp_rw [pow_add, pow_one]
  calc ∑' i, ((2 : ℝ≥0∞) ^ i * 2)⁻¹
  _ = ∑' i, (2⁻¹ ^ i) * 2⁻¹ := by
        congr with i
        rw [ENNReal.mul_inv (by simp) (by simp), ENNReal.inv_pow]
  _ = (∑' i, 2⁻¹ ^ i) * 2⁻¹ := by rw [ENNReal.tsum_mul_right]
  _ = (1 - 2⁻¹)⁻¹ * 2⁻¹ := by rw [ENNReal.tsum_geometric]
  _ ≤ 1 := by simp [ENNReal.one_sub_inv_two, inv_inv, ENNReal.mul_inv_cancel]

instance instIsFiniteMeasureToFinite [SFinite μ] : IsFiniteMeasure (toFinite μ) :=
  ⟨(toFinite_univ_le_one μ).trans_lt ENNReal.one_lt_top⟩

noncomputable
def densityToFinite (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  ∑' n, (sFiniteSeq μ n).rnDeriv (toFinite μ) a

lemma densityToFinite_def (μ : Measure α) [SFinite μ] :
    densityToFinite μ = fun a ↦ ∑' n, (sFiniteSeq μ n).rnDeriv (toFinite μ) a := rfl

lemma measurable_densityToFinite (μ : Measure α) [SFinite μ] :
    Measurable (densityToFinite μ) := by
  rw [densityToFinite_def]
  exact Measurable.ennreal_tsum (fun n ↦ measurable_rnDeriv _ _)

theorem withDensity_densitytoFinite (μ : Measure α) [SFinite μ] :
    (toFinite μ).withDensity (densityToFinite μ) = μ := by
  rw [densityToFinite_def]
  have : ((toFinite μ).withDensity
        fun a ↦ ∑' n, (sFiniteSeq μ n).rnDeriv (toFinite μ) a)
      = (toFinite μ).withDensity (∑' n, (sFiniteSeq μ n).rnDeriv (toFinite μ)) := by
    congr with a
    rw [ENNReal.tsum_apply]
  rw [this, withDensity_tsum (fun i ↦ measurable_rnDeriv _ _)]
  conv_rhs => rw [← sum_sFiniteSeq μ]
  congr with n
  rw [withDensity_rnDeriv_eq]
  exact sFiniteSet_absolutelyContinuous_toFinite μ n

noncomputable
def densityToSigmaFinite (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  if densityToFinite μ a = ∞ then densityToFinite μ a else 1

lemma densityToSigmaFinite_def (μ : Measure α) [SFinite μ] :
    densityToSigmaFinite μ = fun a ↦ if densityToFinite μ a = ∞ then densityToFinite μ a else 1 :=
  rfl

lemma measurable_densityToSigmaFinite (μ : Measure α) [SFinite μ] :
    Measurable (densityToSigmaFinite μ) := by
  rw [densityToSigmaFinite_def]
  exact Measurable.ite (measurable_densityToFinite μ (measurableSet_singleton _))
    (measurable_densityToFinite μ) measurable_const

lemma densityToSigmaFinite_eq_one_or_top (μ : Measure α) [SFinite μ] (a : α) :
    densityToSigmaFinite μ a = 1 ∨ densityToSigmaFinite μ a = ∞ := by
  rw [densityToSigmaFinite]
  split_ifs with h <;> simp [h]

lemma densityToSigmaFinite_eq_top_iff (μ : Measure α) [SFinite μ] (a : α) :
    densityToSigmaFinite μ a = ∞ ↔ densityToFinite μ a = ∞ := by
  rw [densityToSigmaFinite]
  split_ifs with h <;> simp [h]

lemma densityToSigmaFinite_eq_one_iff (μ : Measure α) [SFinite μ] (a : α) :
    densityToSigmaFinite μ a = 1 ↔ densityToFinite μ a ≠ ∞ := by
  rw [densityToSigmaFinite]
  split_ifs with h <;> simp [h]

noncomputable
def toSigmaFiniteAuxFun (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  if densityToFinite μ a ≠ ∞ then densityToFinite μ a else 1

lemma toSigmaFiniteAuxFun_def (μ : Measure α) [SFinite μ] :
    toSigmaFiniteAuxFun μ = fun a ↦ if densityToFinite μ a ≠ ∞ then densityToFinite μ a else 1 :=
  rfl

lemma measurable_toSigmaFiniteAuxFun (μ : Measure α) [SFinite μ] :
    Measurable (toSigmaFiniteAuxFun μ) := by
  rw [toSigmaFiniteAuxFun_def]
  exact Measurable.ite (measurable_densityToFinite μ (measurableSet_singleton _)).compl
    (measurable_densityToFinite μ) measurable_const

lemma toSigmaFiniteAuxFun_lt_top (μ : Measure α) [SFinite μ] (a : α) :
    toSigmaFiniteAuxFun μ a < ∞ := by
  rw [toSigmaFiniteAuxFun]
  split_ifs with h <;> simp [lt_top_iff_ne_top, h]

lemma toSigmaFiniteAuxFun_ne_top (μ : Measure α) [SFinite μ] (a : α) :
    toSigmaFiniteAuxFun μ a ≠ ∞ := (toSigmaFiniteAuxFun_lt_top μ a).ne

lemma toSigmaFiniteAuxFun_mul_densityToSigmaFinite (μ : Measure α) [SFinite μ] (a : α) :
    toSigmaFiniteAuxFun μ a * densityToSigmaFinite μ a = densityToFinite μ a := by
  rw [toSigmaFiniteAuxFun, densityToSigmaFinite]
  split_ifs with h1 h2
  · rw [mul_one]
  · rw [one_mul]
  · rw [← ne_eq] at h2
    exact absurd h2 h1

lemma toSigmaFiniteAuxFun_mul_densityToSigmaFinite' (μ : Measure α) [SFinite μ] :
    toSigmaFiniteAuxFun μ * densityToSigmaFinite μ = densityToFinite μ := by
    ext a
    rw [Pi.mul_apply]
    exact toSigmaFiniteAuxFun_mul_densityToSigmaFinite μ a

@[pp_dot]
noncomputable
def toSigmaFinite (μ : Measure α) [SFinite μ] : Measure α :=
  (toFinite μ).withDensity (toSigmaFiniteAuxFun μ)

instance instSigmaFiniteToSigmaFinite (μ : Measure α) [SFinite μ] :
    SigmaFinite μ.toSigmaFinite :=
  SigmaFinite.withDensity_of_ne_top' (measurable_toSigmaFiniteAuxFun μ).aemeasurable
    (toSigmaFiniteAuxFun_ne_top μ)

lemma withDensity_densityToSigmaFinite (μ : Measure α) [SFinite μ] :
    μ.toSigmaFinite.withDensity (densityToSigmaFinite μ) = μ := by
  rw [toSigmaFinite, ← withDensity_mul]
  · rw [toSigmaFiniteAuxFun_mul_densityToSigmaFinite', withDensity_densitytoFinite]
  · exact measurable_toSigmaFiniteAuxFun μ
  · exact measurable_densityToSigmaFinite μ

lemma absolutelyContinuous_toSigmaFinite (μ : Measure α) [SFinite μ] :
    μ ≪ μ.toSigmaFinite := by
  nth_rewrite 1 [← withDensity_densityToSigmaFinite μ]
  exact withDensity_absolutelyContinuous _ _

lemma toSigmaFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] :
    μ.toSigmaFinite ≪ μ :=
  (withDensity_absolutelyContinuous _ _).trans (toFinite_absolutelyContinuous μ)

/-! ### IsZeroTopSet -/

def IsZeroTopSet (s : Set α) (μ : Measure α) : Prop :=
  ∀ t, MeasurableSet t → t ⊆ s → μ t = 0 ∨ μ t = ∞

lemma isZeroTopSet_of_null (hs_zero : μ s = 0) : IsZeroTopSet s μ :=
  fun _ _ ht_subset ↦ Or.inl <| measure_mono_null ht_subset hs_zero

lemma measure_isZeroTopSet (hs0 : IsZeroTopSet s μ) (hs : MeasurableSet s) : μ s = 0 ∨ μ s = ⊤ :=
  hs0 s hs subset_rfl

lemma measure_eq_iSup_measure_subset [SigmaFinite μ] (hs : MeasurableSet s) :
    μ s = ⨆ (t : Set α) (_ht : MeasurableSet t) (_hμt : μ t ≠ ∞) (_hts : t ⊆ s), μ t := by
  refine le_antisymm ?_ ?_
  · rw [← iSup_restrict_spanningSets hs]
    simp only [ne_eq, iSup_le_iff]
    intro i
    rw [restrict_apply' (measurable_spanningSets _ _)]
    refine le_trans ?_ (le_iSup _ (s ∩ spanningSets μ i))
    simp only [hs.inter (measurable_spanningSets _ _),
      ((measure_mono (Set.inter_subset_right s _)).trans_lt (measure_spanningSets_lt_top μ _)).ne,
      not_false_eq_true, Set.inter_subset_left, iSup_pos, le_refl]
  · simp only [ne_eq, iSup_le_iff]
    exact fun _ _ _ hts ↦ measure_mono hts

lemma measure_eq_iSup_measure_subset_toMeasurable [SigmaFinite μ] (s : Set α) :
    μ s = ⨆ (t : Set α) (_ht : MeasurableSet t) (_hμt : μ t ≠ ∞) (_hts : t ⊆ toMeasurable μ s),
      μ t := by
  rw [← measure_toMeasurable s,measure_eq_iSup_measure_subset (measurableSet_toMeasurable _ _)]

lemma iSup_measure_subset_eq_zero_of_isZeroTopSet (hs : IsZeroTopSet s μ) :
    ⨆ (t : Set α) (_ : MeasurableSet t) (_ : μ t ≠ ∞) (_ : t ⊆ s), μ t = 0 := by
  simp only [ne_eq, ENNReal.iSup_eq_zero]
  exact fun t ht hμt hts ↦ (hs t ht hts).resolve_right hμt

lemma isZeroTopSet_iff_null [SigmaFinite μ] (hs : MeasurableSet s) :
    IsZeroTopSet s μ ↔ μ s = 0 := by
  refine ⟨fun h ↦ ?_, isZeroTopSet_of_null⟩
  rw [measure_eq_iSup_measure_subset hs, iSup_measure_subset_eq_zero_of_isZeroTopSet h]

def maxZeroTopSet (μ : Measure α) [SFinite μ] : Set α :=
  {x | densityToSigmaFinite μ x = ∞}

lemma measurableSet_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    MeasurableSet (maxZeroTopSet μ) :=
  measurable_densityToSigmaFinite μ (measurableSet_singleton ∞)

lemma isZeroTopSet_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    IsZeroTopSet (maxZeroTopSet μ) μ := by
  intro t ht ht_subset
  rw [← withDensity_densityToSigmaFinite μ, withDensity_apply _ ht]
  have h_int_eq : ∫⁻ a in t, densityToSigmaFinite μ a ∂μ.toSigmaFinite = ∞ * μ.toSigmaFinite t := by
    calc ∫⁻ a in t, densityToSigmaFinite μ a ∂μ.toSigmaFinite
    _ = ∫⁻ _ in t, ∞ ∂μ.toSigmaFinite :=
        set_lintegral_congr_fun ht (ae_of_all _ (fun x hx ↦ ht_subset hx))
    _ = ∞ * μ.toSigmaFinite t := by simp
  rw [h_int_eq]
  by_cases h0 : μ.toSigmaFinite t = 0 <;> simp [h0]

lemma restrict_compl_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    μ.restrict (maxZeroTopSet μ)ᶜ = (μ.toSigmaFinite).restrict (maxZeroTopSet μ)ᶜ := by
  have hμ := withDensity_densityToSigmaFinite μ
  nth_rewrite 1 [← hμ]
  ext s hs
  rw [restrict_apply hs, withDensity_apply _ (hs.inter (measurableSet_maxZeroTopSet μ).compl),
    restrict_apply hs, ← set_lintegral_one]
  refine set_lintegral_congr_fun (hs.inter (measurableSet_maxZeroTopSet μ).compl)
    (ae_of_all _ (fun x hx ↦ ?_))
  simp only [maxZeroTopSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
    densityToSigmaFinite_eq_top_iff] at hx
  rw [densityToSigmaFinite_eq_one_iff]
  exact hx.2

lemma toSigmaFinite_add_restrict_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    (μ.toSigmaFinite).restrict (maxZeroTopSet μ)ᶜ + μ.restrict (maxZeroTopSet μ) = μ := by
  rw [← restrict_compl_maxZeroTopSet, restrict_compl_add_restrict (measurableSet_maxZeroTopSet μ)]

lemma restrict_maxZeroTopSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (hs : MeasurableSet s) :
    μ.restrict (maxZeroTopSet μ) s = 0 ∨ μ.restrict (maxZeroTopSet μ) s = ∞ := by
  rw [restrict_apply' (measurableSet_maxZeroTopSet μ)]
  exact isZeroTopSet_maxZeroTopSet μ (s ∩ maxZeroTopSet μ)
    (hs.inter (measurableSet_maxZeroTopSet μ)) (Set.inter_subset_right _ _)

lemma sigmaFinite_iff_measure_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    SigmaFinite μ ↔ μ (maxZeroTopSet μ) = 0 := by
  refine ⟨fun h ↦ (isZeroTopSet_iff_null (measurableSet_maxZeroTopSet μ)).mp
    (isZeroTopSet_maxZeroTopSet μ), fun h ↦ ?_⟩
  rw [← toSigmaFinite_add_restrict_maxZeroTopSet μ, restrict_eq_zero.mpr h, add_zero]
  infer_instance

lemma isZeroTopSet_iff_ne_iSup_of_eq_top (hμs : μ s = ∞) :
    IsZeroTopSet s μ
      ↔ μ s ≠ ⨆ (t : Set α) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (hts : t ⊆ s), μ t := by
  refine ⟨fun hs ↦ ?_, fun h ↦ ?_⟩
  · simp [iSup_measure_subset_eq_zero_of_isZeroTopSet hs, hμs]
  · sorry

end Measure

end MeasureTheory
