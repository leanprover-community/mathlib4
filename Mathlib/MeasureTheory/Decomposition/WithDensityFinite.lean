/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
# s-finite measures can be written as withDensity of a finite measure

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

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Set α}

open Classical in
/-- A finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toFinite.withDensity (densityToFinite μ)` (see `withDensity_densitytoFinite`). -/
@[pp_dot]
noncomputable def toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  Measure.sum (fun n ↦ if sFiniteSeq μ n ≠ 0
    then (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ • sFiniteSeq μ n
    else 0)

lemma toFinite_apply (μ : Measure α) [SFinite μ] [∀ n, Decidable (sFiniteSeq μ n ≠ 0)]
    (hs : MeasurableSet s) :
    μ.toFinite s
      = ∑' n, if sFiniteSeq μ n ≠ 0
        then (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ * sFiniteSeq μ n s else 0 := by
  rw [toFinite, sum_apply _ hs]
  congr with n
  split_ifs with h <;> congr

lemma sFiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : ℕ) :
    sFiniteSeq μ n ≪ μ.toFinite := by
  refine absolutelyContinuous_sum_right n ?_
  split_ifs with h0
  · refine absolutelyContinuous_smul ?_
    simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · rw [ne_eq, not_not] at h0
    simp [h0]

lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] :
    μ ≪ μ.toFinite := by
  conv_lhs => rw [← sum_sFiniteSeq μ]
  exact absolutelyContinuous_sum_left (sFiniteSeq_absolutelyContinuous_toFinite μ)

lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] :
    μ.toFinite ≪ μ := by
  conv_rhs => rw [← sum_sFiniteSeq μ]
  refine AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  classical simp [toFinite_apply _ hs, hs0]

lemma toFinite_univ_le_one (μ : Measure α) [SFinite μ] :
    μ.toFinite Set.univ ≤ 1 := by
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

instance instIsFiniteMeasureToFinite [SFinite μ] : IsFiniteMeasure μ.toFinite :=
  ⟨(toFinite_univ_le_one μ).trans_lt ENNReal.one_lt_top⟩

/-- A function such that `μ.toFinite.withDensity (densityToFinite μ) = μ`.
See `withDensity_densitytoFinite`. -/
noncomputable
def densityToFinite (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  ∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite a

lemma densityToFinite_def (μ : Measure α) [SFinite μ] :
    densityToFinite μ = fun a ↦ ∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite a := rfl

lemma measurable_densityToFinite (μ : Measure α) [SFinite μ] :
    Measurable (densityToFinite μ) := by
  rw [densityToFinite_def]
  exact Measurable.ennreal_tsum (fun n ↦ measurable_rnDeriv _ _)

theorem withDensity_densitytoFinite (μ : Measure α) [SFinite μ] :
    μ.toFinite.withDensity (densityToFinite μ) = μ := by
  have : (μ.toFinite.withDensity fun a ↦ ∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite a)
      = μ.toFinite.withDensity (∑' n, (sFiniteSeq μ n).rnDeriv μ.toFinite) := by
    congr with a
    rw [ENNReal.tsum_apply]
  rw [densityToFinite_def, this, withDensity_tsum (fun i ↦ measurable_rnDeriv _ _)]
  conv_rhs => rw [← sum_sFiniteSeq μ]
  congr with n
  rw [withDensity_rnDeriv_eq]
  exact sFiniteSeq_absolutelyContinuous_toFinite μ n

lemma densityToFinite_ae_lt_top (μ : Measure α) [SigmaFinite μ] :
    ∀ᵐ x ∂μ, densityToFinite μ x < ∞ := by
  refine ae_of_forall_measure_lt_top_ae_restrict _ (fun s _ hμs ↦ ?_)
  suffices ∀ᵐ x ∂μ.toFinite.restrict s, densityToFinite μ x < ∞ by
    have h : μ.restrict s ≪ μ.toFinite.restrict s := (absolutelyContinuous_toFinite μ).restrict _
    exact h this
  refine ae_lt_top (measurable_densityToFinite μ) ?_
  rw [← withDensity_apply', withDensity_densitytoFinite]
  exact hμs.ne

lemma densityToFinite_ae_ne_top (μ : Measure α) [SigmaFinite μ] :
    ∀ᵐ x ∂μ, densityToFinite μ x ≠ ∞ :=
  (densityToFinite_ae_lt_top μ).mono (fun _ hx ↦ hx.ne)

/-- A function such that `μ.toSigmaFinite.withDensity (densityToSigmaFinite μ) = μ`.
See `withDensity_densityToSigmaFinite`.
This function takes only two values, `1` and `∞`. -/
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

lemma densityToSigmaFinite_ae_eq_one (μ : Measure α) [SigmaFinite μ] :
    densityToSigmaFinite μ =ᵐ[μ] fun _ ↦ 1 := by
  filter_upwards [densityToFinite_ae_ne_top μ] with x hx
  rwa [densityToSigmaFinite_eq_one_iff]

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

/-- A sigma-finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toSigmaFinite.withDensity (densityToSigmaFinite μ)`. The function `densityToSigmaFinite μ`
takes only two values, `1` and `∞`. -/
@[pp_dot]
noncomputable def toSigmaFinite (μ : Measure α) [SFinite μ] : Measure α :=
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

@[simp]
lemma toSigmaFinite_eq_self (μ : Measure α) [SigmaFinite μ] :
    μ.toSigmaFinite = μ := by
  ext s
  suffices μ.toSigmaFinite.withDensity (densityToSigmaFinite μ) s = μ.toSigmaFinite s by
    rw [← this, withDensity_densityToSigmaFinite μ]
  have h : densityToSigmaFinite μ =ᵐ[μ.toSigmaFinite] 1 :=
    toSigmaFinite_absolutelyContinuous μ (densityToSigmaFinite_ae_eq_one μ)
  rw [withDensity_congr_ae h, withDensity_one]

lemma toSigmaFinite_eq_self_iff (μ : Measure α) [SFinite μ] :
    μ.toSigmaFinite = μ ↔ SigmaFinite μ :=
  ⟨fun h ↦ h.symm ▸ inferInstance, fun _ ↦ toSigmaFinite_eq_self μ⟩
