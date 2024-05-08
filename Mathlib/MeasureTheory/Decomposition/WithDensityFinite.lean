/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
# s-finite measures can be written as `withDensity` of a finite measure

If `μ` is an s-finite measure, then there exists a finite measure `μ.toFinite` and a measurable
function `densityToFinite μ` such that `μ = μ.toFinite.withDensity μ.densityToFinite`.

That measure is not unique, and in particular our implementation lead to `μ.toFinite ≠ μ` even if
`μ` is finite.

## Main definitions

In all these definitions and the results below, `μ` is an s-finite measure (`SFinite μ`).

* `MeasureTheory.Measure.toFinite`: a finite measure with `μ ≪ μ.toFinite` and `μ.toFinite ≪ μ`.
* `MeasureTheory.Measure.densityToFinite`: a measurable function such that
  `μ = μ.toFinite.withDensity μ.densityToFinite`.
* `MeasureTheory.Measure.toSigmaFinite`: a sigma-finite measure with `μ ≪ μ.toSigmaFinite` and
  `μ.toSigmaFinite ≪ μ`. If `μ` is sigma-finite, `μ.toSigmaFinite = μ`.
* `MeasureTheory.Measure.densityToSigmaFinite`: a measurable function such that
  `μ = μ.toSigmaFinite.withDensity μ.densityToSigmaFinite`. This function takes only two values,
  `1` and `∞`.
* `MeasureTheory.Measure.densitySigmaFiniteToFinite`: a measurable function such that
  `μ.toSigmaFinite = μ.toFinite.withDensity μ.densitySigmaFiniteToFinite`.

## Main statements

* `absolutelyContinuous_toFinite`: `μ ≪ μ.toFinite`.
* `toFinite_absolutelyContinuous`: `μ.toFinite ≪ μ`.
* `withDensity_densitytoFinite`: `μ.toFinite.withDensity μ.densityToFinite = μ`.
* `withDensity_densityToSigmaFinite`: `μ.toSigmaFinite.withDensity μ.densityToSigmaFinite = μ`.
* `toSigmaFinite_eq_self_iff`: `μ.toSigmaFinite = μ ↔ SigmaFinite μ`.

-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- A finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toFinite.withDensity μ.densityToFinite` (see `withDensity_densitytoFinite`). -/
noncomputable def Measure.toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  Measure.sum (fun n ↦ (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ • sFiniteSeq μ n)

lemma toFinite_apply (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.toFinite s = ∑' n, (2 ^ (n + 1) * sFiniteSeq μ n Set.univ)⁻¹ * sFiniteSeq μ n s := by
  rw [Measure.toFinite, Measure.sum_apply_of_countable]; rfl

lemma sFiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : ℕ) :
    sFiniteSeq μ n ≪ μ.toFinite := by
  refine Measure.absolutelyContinuous_sum_right n (Measure.absolutelyContinuous_smul ?_)
  simp only [ne_eq, ENNReal.inv_eq_zero]
  exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)

lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite := by
  conv_lhs => rw [← sum_sFiniteSeq μ]
  exact Measure.absolutelyContinuous_sum_left (sFiniteSeq_absolutelyContinuous_toFinite μ)

lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ := by
  conv_rhs => rw [← sum_sFiniteSeq μ]
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  simp only [Measure.sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  simp [toFinite_apply _ s, hs0]

lemma toFinite_univ_le_one (μ : Measure α) [SFinite μ] : μ.toFinite Set.univ ≤ 1 := by
  rw [toFinite_apply]
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

instance instIsFiniteMeasureToFinite {μ : Measure α} [SFinite μ] : IsFiniteMeasure μ.toFinite :=
  ⟨(toFinite_univ_le_one μ).trans_lt ENNReal.one_lt_top⟩

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

/-- A measurable function such that `μ.toSigmaFinite.withDensity μ.densityToSigmaFinite = μ`.
See `withDensity_densityToSigmaFinite`.
This function takes only two values, `1` and `∞`. -/
noncomputable
def Measure.densityToSigmaFinite (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  if μ.densityToFinite a = ∞ then μ.densityToFinite a else 1

lemma densityToSigmaFinite_def (μ : Measure α) [SFinite μ] :
    μ.densityToSigmaFinite = fun a ↦ if μ.densityToFinite a = ∞ then μ.densityToFinite a else 1 :=
  rfl

lemma measurable_densityToSigmaFinite (μ : Measure α) [SFinite μ] :
    Measurable μ.densityToSigmaFinite :=
  Measurable.ite (measurable_densityToFinite μ (measurableSet_singleton _))
    (measurable_densityToFinite μ) measurable_const

lemma densityToSigmaFinite_eq_one_or_top (μ : Measure α) [SFinite μ] (a : α) :
    μ.densityToSigmaFinite a = 1 ∨ μ.densityToSigmaFinite a = ∞ := by
  rw [Measure.densityToSigmaFinite]
  split_ifs with h <;> simp [h]

lemma densityToSigmaFinite_eq_top_iff (μ : Measure α) [SFinite μ] (a : α) :
    μ.densityToSigmaFinite a = ∞ ↔ μ.densityToFinite a = ∞ := by
  rw [Measure.densityToSigmaFinite]
  split_ifs with h <;> simp [h]

lemma densityToSigmaFinite_eq_one_iff (μ : Measure α) [SFinite μ] (a : α) :
    μ.densityToSigmaFinite a = 1 ↔ μ.densityToFinite a ≠ ∞ := by
  rw [Measure.densityToSigmaFinite]
  split_ifs with h <;> simp [h]

lemma densityToSigmaFinite_ae_eq_one (μ : Measure α) [SigmaFinite μ] :
    μ.densityToSigmaFinite =ᵐ[μ] fun _ ↦ 1 := by
  filter_upwards [densityToFinite_ae_ne_top μ] with x hx
  rwa [densityToSigmaFinite_eq_one_iff]

/-- A measurable function such that
`μ.toFinite.withDensity μ.densitySigmaFiniteToFinite = μ.toSigmaFinite` (by definition of
`μ.toSigmaFinite`). -/
noncomputable
def Measure.densitySigmaFiniteToFinite (μ : Measure α) [SFinite μ] (a : α) : ℝ≥0∞ :=
  if μ.densityToFinite a ≠ ∞ then μ.densityToFinite a else 1

lemma densitySigmaFiniteToFinite_def (μ : Measure α) [SFinite μ] :
    μ.densitySigmaFiniteToFinite
      = fun a ↦ if μ.densityToFinite a ≠ ∞ then μ.densityToFinite a else 1 := rfl

lemma measurable_densitySigmaFiniteToFinite (μ : Measure α) [SFinite μ] :
    Measurable μ.densitySigmaFiniteToFinite :=
  Measurable.ite (measurable_densityToFinite μ (measurableSet_singleton _)).compl
    (measurable_densityToFinite μ) measurable_const

lemma densitySigmaFiniteToFinite_lt_top (μ : Measure α) [SFinite μ] (a : α) :
    μ.densitySigmaFiniteToFinite a < ∞ := by
  rw [Measure.densitySigmaFiniteToFinite]
  split_ifs with h <;> simp [lt_top_iff_ne_top, h]

lemma densitySigmaFiniteToFinite_ne_top (μ : Measure α) [SFinite μ] (a : α) :
    μ.densitySigmaFiniteToFinite a ≠ ∞ := (densitySigmaFiniteToFinite_lt_top μ a).ne

lemma densitySigmaFiniteToFinite_mul_densityToSigmaFinite (μ : Measure α) [SFinite μ] (a : α) :
    μ.densitySigmaFiniteToFinite a * μ.densityToSigmaFinite a = μ.densityToFinite a := by
  rw [Measure.densitySigmaFiniteToFinite, Measure.densityToSigmaFinite]
  by_cases h : μ.densityToFinite a = ∞ <;> simp [h]

lemma densitySigmaFiniteToFinite_mul_densityToSigmaFinite' (μ : Measure α) [SFinite μ] :
    μ.densitySigmaFiniteToFinite * μ.densityToSigmaFinite = μ.densityToFinite := by
  ext a
  rw [Pi.mul_apply]
  exact densitySigmaFiniteToFinite_mul_densityToSigmaFinite μ a

/-- A sigma-finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toSigmaFinite.withDensity μ.densityToSigmaFinite`. The function `μ.densityToSigmaFinite`
takes only two values, `1` and `∞`. -/
noncomputable def Measure.toSigmaFinite (μ : Measure α) [SFinite μ] : Measure α :=
  μ.toFinite.withDensity μ.densitySigmaFiniteToFinite

instance instSigmaFiniteToSigmaFinite (μ : Measure α) [SFinite μ] : SigmaFinite μ.toSigmaFinite :=
  SigmaFinite.withDensity_of_ne_top' (measurable_densitySigmaFiniteToFinite μ).aemeasurable
    (densitySigmaFiniteToFinite_ne_top μ)

@[simp]
lemma withDensity_densityToSigmaFinite (μ : Measure α) [SFinite μ] :
    μ.toSigmaFinite.withDensity μ.densityToSigmaFinite = μ := by
  rw [Measure.toSigmaFinite, ← withDensity_mul]
  · rw [densitySigmaFiniteToFinite_mul_densityToSigmaFinite', withDensity_densitytoFinite]
  · exact measurable_densitySigmaFiniteToFinite μ
  · exact measurable_densityToSigmaFinite μ

lemma absolutelyContinuous_toSigmaFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toSigmaFinite := by
  nth_rewrite 1 [← withDensity_densityToSigmaFinite μ]
  exact withDensity_absolutelyContinuous _ _

lemma toSigmaFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toSigmaFinite ≪ μ :=
  (withDensity_absolutelyContinuous _ _).trans (toFinite_absolutelyContinuous μ)

@[simp]
lemma toSigmaFinite_eq_self (μ : Measure α) [SigmaFinite μ] : μ.toSigmaFinite = μ := by
  ext s
  suffices μ.toSigmaFinite.withDensity μ.densityToSigmaFinite s = μ.toSigmaFinite s by
    rw [← this, withDensity_densityToSigmaFinite μ]
  have h : μ.densityToSigmaFinite =ᵐ[μ.toSigmaFinite] 1 :=
    toSigmaFinite_absolutelyContinuous μ (densityToSigmaFinite_ae_eq_one μ)
  rw [withDensity_congr_ae h, withDensity_one]

lemma toSigmaFinite_eq_self_iff (μ : Measure α) [SFinite μ] :
    μ.toSigmaFinite = μ ↔ SigmaFinite μ :=
  ⟨fun h ↦ h.symm ▸ inferInstance, fun _ ↦ toSigmaFinite_eq_self μ⟩

end MeasureTheory
