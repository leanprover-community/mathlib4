/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.Probability.ConditionalProbability

/-!
# s-finite measures can be written as `withDensity` of a finite measure

If `μ` is an s-finite measure, then there exists a finite measure `μ.toFinite` and a measurable
function `densityToFinite μ` such that `μ = μ.toFinite.withDensity μ.densityToFinite`. If `μ` is
zero this is the zero measure, and otherwise we can choose a probability measure for `μ.toFinite`.

That measure is not unique, and in particular our implementation leads to `μ.toFinite ≠ μ` even if
`μ` is a probability measure.

We use this construction to define a set `μ.sigmaFiniteSet`, such that `μ.restrict μ.sigmaFiniteSet`
is sigma-finite, and for all measurable sets `s ⊆ μ.sigmaFiniteSetᶜ`, either `μ s = 0`
or `μ s = ∞`.

## Main definitions

In these definitions and the results below, `μ` is an s-finite measure (`SFinite μ`).

* `MeasureTheory.Measure.toFinite`: a finite measure with `μ ≪ μ.toFinite` and `μ.toFinite ≪ μ`.
  If `μ ≠ 0`, this is a probability measure.
* `MeasureTheory.Measure.densityToFinite`: a measurable function such that
  `μ = μ.toFinite.withDensity μ.densityToFinite`.
* `MeasureTheory.Measure.sigmaFiniteSet`: a measurable set such that `μ.restrict μ.sigmaFiniteSet`
  is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`, either `μ s = 0` or `μ s = ∞`.

## Main statements

* `absolutelyContinuous_toFinite`: `μ ≪ μ.toFinite`.
* `toFinite_absolutelyContinuous`: `μ.toFinite ≪ μ`.
* `withDensity_densitytoFinite`: `μ.toFinite.withDensity μ.densityToFinite = μ`.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: an s-finite measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- Auxiliary definition for `MeasureTheory.Measure.toFinite`. -/
noncomputable def Measure.toFiniteAux (μ : Measure α) [SFinite μ] : Measure α :=
  Measure.sum (fun n ↦ (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ • sFiniteSeq μ n)

/-- A finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toFinite.withDensity μ.densityToFinite` (see `withDensity_densitytoFinite`).
If `μ` is non-zero, this is a probability measure. -/
noncomputable def Measure.toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  ProbabilityTheory.cond μ.toFiniteAux Set.univ

lemma toFiniteAux_apply (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.toFiniteAux s = ∑' n, (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ * sFiniteSeq μ n s := by
  rw [Measure.toFiniteAux, Measure.sum_apply_of_countable]; rfl

lemma toFinite_apply (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.toFinite s = (μ.toFiniteAux Set.univ)⁻¹ * μ.toFiniteAux s := by
  rw [Measure.toFinite, ProbabilityTheory.cond_apply _ MeasurableSet.univ, Set.univ_inter]

lemma toFiniteAux_zero : Measure.toFiniteAux (0 : Measure α) = 0 := by
  ext s
  simp [toFiniteAux_apply]

@[simp]
lemma toFinite_zero : Measure.toFinite (0 : Measure α) = 0 := by
  simp [Measure.toFinite, toFiniteAux_zero]

lemma toFiniteAux_eq_zero_iff [SFinite μ] : μ.toFiniteAux = 0 ↔ μ = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, toFiniteAux_zero]⟩
  ext s hs
  rw [Measure.ext_iff] at h
  specialize h s hs
  simp only [toFiniteAux_apply, Measure.coe_zero, Pi.zero_apply,
    ENNReal.tsum_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero] at h
  rw [← sum_sFiniteSeq μ, Measure.sum_apply _ hs]
  simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.tsum_eq_zero]
  intro n
  specialize h n
  simpa [ENNReal.mul_eq_top, measure_ne_top] using h

lemma toFiniteAux_univ_le_one (μ : Measure α) [SFinite μ] : μ.toFiniteAux Set.univ ≤ 1 := by
  rw [toFiniteAux_apply]
  have h_le_pow : ∀ n, (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ * sFiniteSeq μ n Set.univ
      ≤ (2 ^ (n + 1))⁻¹ := by
    intro n
    by_cases h_zero : sFiniteSeq μ n = 0
    · simp [h_zero]
    · rw [ENNReal.le_inv_iff_mul_le, mul_assoc, mul_comm (sFiniteSeq μ n Set.univ),
        ENNReal.inv_mul_cancel]
      · simp [h_zero]
      · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  refine (tsum_le_tsum h_le_pow ENNReal.summable ENNReal.summable).trans ?_
  simp [ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, ENNReal.inv_mul_cancel]

instance [SFinite μ] : IsFiniteMeasure μ.toFiniteAux :=
  ⟨(toFiniteAux_univ_le_one μ).trans_lt ENNReal.one_lt_top⟩

@[simp]
lemma toFinite_eq_zero_iff [SFinite μ] : μ.toFinite = 0 ↔ μ = 0 := by
  simp [Measure.toFinite, measure_ne_top μ.toFiniteAux Set.univ, toFiniteAux_eq_zero_iff]

instance [SFinite μ] : IsFiniteMeasure μ.toFinite := by
  rw [Measure.toFinite]
  infer_instance

instance [SFinite μ] [h_zero : NeZero μ] : IsProbabilityMeasure μ.toFinite := by
  refine ProbabilityTheory.cond_isProbabilityMeasure μ.toFiniteAux ?_
  simp [toFiniteAux_eq_zero_iff, h_zero.out]

lemma sFiniteSeq_absolutelyContinuous_toFiniteAux (μ : Measure α) [SFinite μ] (n : ℕ) :
    sFiniteSeq μ n ≪ μ.toFiniteAux := by
  refine Measure.absolutelyContinuous_sum_right n (Measure.absolutelyContinuous_smul ?_)
  simp only [ne_eq, ENNReal.inv_eq_zero]
  exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)

lemma toFiniteAux_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] :
    μ.toFiniteAux ≪ μ.toFinite := ProbabilityTheory.absolutelyContinuous_cond_univ

lemma sFiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : ℕ) :
    sFiniteSeq μ n ≪ μ.toFinite :=
  (sFiniteSeq_absolutelyContinuous_toFiniteAux μ n).trans
    (toFiniteAux_absolutelyContinuous_toFinite μ)

lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite := by
  conv_lhs => rw [← sum_sFiniteSeq μ]
  exact Measure.absolutelyContinuous_sum_left (sFiniteSeq_absolutelyContinuous_toFinite μ)

lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ := by
  conv_rhs => rw [← sum_sFiniteSeq μ]
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  simp only [Measure.sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  simp [toFinite_apply, toFiniteAux_apply, hs0]

/-- A measurable function such that `μ.toFinite.withDensity μ.densityToFinite = μ`.
See `withDensity_densitytoFinite`. -/
noncomputable
def Measure.densityToFinite (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  ∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite a

lemma densityToFinite_def (μ : Measure α) [SFinite μ] :
    μ.densityToFinite = fun a ↦ ∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite a := rfl

lemma measurable_densityToFinite (μ : Measure α) [SFinite μ] : Measurable μ.densityToFinite :=
  Measurable.ennreal_tsum fun _ ↦ Measure.measurable_rnDeriv _ _

theorem withDensity_densitytoFinite (μ : Measure α) [SFinite μ] :
    μ.toFinite.withDensity μ.densityToFinite = μ := by
  have : (μ.toFinite.withDensity fun a ↦ ∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite a)
      = μ.toFinite.withDensity (∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite) := by
    congr with a
    rw [ENNReal.tsum_apply]
  rw [densityToFinite_def, this, withDensity_tsum (fun i ↦ Measure.measurable_rnDeriv _ _)]
  conv_rhs => rw [← sum_sFiniteSeq μ]
  congr with n
  rw [Measure.withDensity_rnDeriv_eq]
  exact sFiniteSeq_absolutelyContinuous_toFinite μ n

lemma densityToFinite_ae_lt_top (μ : Measure α) [SigmaFinite μ] :
    ∀ᵐ x ∂μ, μ.densityToFinite x < ∞ := by
  refine ae_of_forall_measure_lt_top_ae_restrict _ (fun s _ hμs ↦ ?_)
  suffices ∀ᵐ x ∂μ.toFinite.restrict s, μ.densityToFinite x < ∞ from
    (absolutelyContinuous_toFinite μ).restrict _ this
  refine ae_lt_top (measurable_densityToFinite μ) ?_
  rw [← withDensity_apply', withDensity_densitytoFinite]
  exact hμs.ne

lemma densityToFinite_ae_ne_top (μ : Measure α) [SigmaFinite μ] :
    ∀ᵐ x ∂μ, μ.densityToFinite x ≠ ∞ :=
  (densityToFinite_ae_lt_top μ).mono (fun _ hx ↦ hx.ne)

section SigmaFiniteSet

variable {s t : Set α}

/-- A measurable set such that `μ.restrict μ.sigmaFiniteSet` is sigma-finite,
  and for all measurable sets `s ⊆ μ.sigmaFiniteSetᶜ`, either `μ s = 0` or `μ s = ∞`. -/
def Measure.sigmaFiniteSet (μ : Measure α) [SFinite μ] : Set α := {x | μ.densityToFinite x ≠ ∞}

lemma measurableSet_sigmaFiniteSet (μ : Measure α) [SFinite μ] :
    MeasurableSet μ.sigmaFiniteSet :=
  (measurable_densityToFinite μ (measurableSet_singleton ∞)).compl

lemma restrict_compl_sigmaFiniteSet [SFinite μ] :
    μ.restrict μ.sigmaFiniteSetᶜ = ∞ • μ.toFinite.restrict μ.sigmaFiniteSetᶜ := by
  ext t ht
  have : μ.restrict μ.sigmaFiniteSetᶜ
      = (μ.toFinite.withDensity μ.densityToFinite).restrict μ.sigmaFiniteSetᶜ := by
    rw [withDensity_densitytoFinite μ]
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [this, Measure.restrict_apply ht,
    withDensity_apply _ (ht.inter (measurableSet_sigmaFiniteSet μ).compl),
    Measure.restrict_apply ht]
  calc ∫⁻ a in t ∩ μ.sigmaFiniteSetᶜ, μ.densityToFinite a ∂μ.toFinite
  _ = ∫⁻ _ in t ∩ μ.sigmaFiniteSetᶜ, ∞ ∂μ.toFinite := by
        refine set_lintegral_congr_fun (ht.inter (measurableSet_sigmaFiniteSet μ).compl)
          (ae_of_all _ (fun x hx ↦ ?_))
        simpa [Measure.sigmaFiniteSet] using ((Set.inter_subset_right _ _) hx)
  _ = ∞ * μ.toFinite (t ∩ μ.sigmaFiniteSetᶜ) := by simp

/-- The measure `μ.restrict μ.sigmaFiniteSetᶜ` takes only two values: 0 and ∞ . -/
lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s = ∞ := by
  rw [restrict_compl_sigmaFiniteSet]
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero, ENNReal.top_ne_zero,
    false_or]
  rw [Measure.restrict_apply' (measurableSet_sigmaFiniteSet μ).compl]
  by_cases h_zero : μ.toFinite (s ∩ μ.sigmaFiniteSetᶜ) = 0
  · exact Or.inl h_zero
  · exact Or.inr (ENNReal.top_mul h_zero)

lemma measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ]
    (ht_subset : t ⊆ μ.sigmaFiniteSetᶜ) :
    μ t = 0 ∨ μ t = ∞ := by
  have : μ t = μ.restrict μ.sigmaFiniteSetᶜ t := by
    rw [Measure.restrict_apply' (measurableSet_sigmaFiniteSet μ).compl,
      Set.inter_eq_left.mpr ht_subset]
  rw [this]
  exact restrict_compl_sigmaFiniteSet_eq_zero_or_top μ t

lemma toFinite_withDensity_restrict_sigmaFiniteSet (μ : Measure α) [SFinite μ] :
    (μ.toFinite.withDensity
        (fun x ↦ if μ.densityToFinite x ≠ ∞ then μ.densityToFinite x else 1)).restrict
        μ.sigmaFiniteSet
      = μ.restrict μ.sigmaFiniteSet := by
  have : μ.restrict μ.sigmaFiniteSet
      = (μ.toFinite.withDensity μ.densityToFinite).restrict μ.sigmaFiniteSet := by
    rw [withDensity_densitytoFinite μ]
  rw [this]
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    withDensity_apply _ (hs.inter (measurableSet_sigmaFiniteSet μ)),
    withDensity_apply _ (hs.inter (measurableSet_sigmaFiniteSet μ))]
  refine set_lintegral_congr_fun (hs.inter (measurableSet_sigmaFiniteSet μ))
    (ae_of_all _ (fun x hx ↦ Eq.symm ?_))
  simp only [Measure.sigmaFiniteSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
    ne_eq] at hx
  rw [if_pos hx.2]

/-- The restriction of an s-finite measure `μ` to `μ.sigmaFiniteSet` is sigma-finite. -/
instance (μ : Measure α) [SFinite μ] : SigmaFinite (μ.restrict μ.sigmaFiniteSet) := by
  rw [← toFinite_withDensity_restrict_sigmaFiniteSet]
  have : SigmaFinite (μ.toFinite.withDensity
      (fun x ↦ if μ.densityToFinite x ≠ ∞ then μ.densityToFinite x else 1)) := by
    refine SigmaFinite.withDensity_of_ne_top ?_ ?_
    · exact (Measurable.ite (measurable_densityToFinite μ (measurableSet_singleton _)).compl
        (measurable_densityToFinite μ) measurable_const).aemeasurable
    · refine ae_of_all _ (fun x ↦ ?_)
      split_ifs with h <;> simp [h]
  exact Restrict.sigmaFinite _ _

lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero [SFinite μ]
    (h : μ μ.sigmaFiniteSetᶜ = 0) :
    SigmaFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet μ),
    Measure.restrict_eq_zero.mpr h, add_zero]
  infer_instance

@[simp]
lemma measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0 :=
  densityToFinite_ae_ne_top μ

/-- An s-finite measure `μ` is sigma-finite iff `μ μ.sigmaFiniteSetᶜ = 0`. -/
lemma measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite (μ : Measure α) [SFinite μ] :
    μ μ.sigmaFiniteSetᶜ = 0 ↔ SigmaFinite μ :=
  ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ ↦ measure_compl_sigmaFiniteSet μ⟩

end SigmaFiniteSet

end MeasureTheory
