/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Measures having no atoms

A measure `μ` has no atoms if the measure of each singleton is zero.

## TODO

Should `NoAtoms` be redefined as `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`?
-/

namespace MeasureTheory

open Set Measure

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- Measure `μ` *has no atoms* if the measure of each singleton is zero.

NB: Wikipedia assumes that for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class NoAtoms {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : ∀ x, μ {x} = 0

export MeasureTheory.NoAtoms (measure_singleton)

attribute [simp] measure_singleton

variable [NoAtoms μ]

theorem _root_.Set.Subsingleton.measure_zero (hs : s.Subsingleton) (μ : Measure α) [NoAtoms μ] :
    μ s = 0 :=
  hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton

theorem Measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 := by
  simp only [measure_singleton, Measure.restrict_eq_zero]

instance Measure.restrict.instNoAtoms (s : Set α) : NoAtoms (μ.restrict s) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null inter_subset_left ht2

theorem _root_.Set.Countable.measure_zero (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    μ s = 0 := by
  rw [← biUnion_of_singleton s, measure_biUnion_null_iff h]
  simp

theorem _root_.Set.Countable.ae_notMem (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    ∀ᵐ x ∂μ, x ∉ s := by
  simpa only [ae_iff, Classical.not_not] using h.measure_zero μ

@[deprecated (since := "2025-05-23")]
alias _root_.Set.Countable.ae_not_mem := _root_.Set.Countable.ae_notMem

lemma _root_.Set.Countable.measure_restrict_compl (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    μ.restrict sᶜ = μ :=
  restrict_eq_self_of_ae_mem <| h.ae_notMem μ

@[simp]
lemma restrict_compl_singleton (a : α) : μ.restrict ({a}ᶜ) = μ :=
  (countable_singleton _).measure_restrict_compl μ

theorem _root_.Set.Finite.measure_zero (h : s.Finite) (μ : Measure α) [NoAtoms μ] : μ s = 0 :=
  h.countable.measure_zero μ

theorem _root_.Finset.measure_zero (s : Finset α) (μ : Measure α) [NoAtoms μ] : μ s = 0 :=
  s.finite_toSet.measure_zero μ

theorem insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s :=
  union_ae_eq_right.2 <| measure_mono_null diff_subset (measure_singleton _)

section

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
  Iio_ae_eq_Iic' (measure_singleton a)

theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  Ioi_ae_eq_Ici' (measure_singleton a)

theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ioc' (measure_singleton b)

theorem Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
  Ioc_ae_eq_Icc' (measure_singleton a)

theorem Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
  Ioo_ae_eq_Ico' (measure_singleton a)

theorem Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
  Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)

theorem Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
  Ico_ae_eq_Icc' (measure_singleton b)

theorem Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
  Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)

theorem restrict_Iio_eq_restrict_Iic : μ.restrict (Iio a) = μ.restrict (Iic a) :=
  restrict_congr_set Iio_ae_eq_Iic

theorem restrict_Ioi_eq_restrict_Ici : μ.restrict (Ioi a) = μ.restrict (Ici a) :=
  restrict_congr_set Ioi_ae_eq_Ici

theorem restrict_Ioo_eq_restrict_Ioc : μ.restrict (Ioo a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ioo_ae_eq_Ioc

theorem restrict_Ioc_eq_restrict_Icc : μ.restrict (Ioc a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioc_ae_eq_Icc

theorem restrict_Ioo_eq_restrict_Ico : μ.restrict (Ioo a b) = μ.restrict (Ico a b) :=
  restrict_congr_set Ioo_ae_eq_Ico

theorem restrict_Ioo_eq_restrict_Icc : μ.restrict (Ioo a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioo_ae_eq_Icc

theorem restrict_Ico_eq_restrict_Icc : μ.restrict (Ico a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ico_ae_eq_Icc

theorem restrict_Ico_eq_restrict_Ioc : μ.restrict (Ico a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ico_ae_eq_Ioc

end

open Interval

open scoped Interval in
theorem uIoc_ae_eq_interval [LinearOrder α] {a b : α} : Ι a b =ᵐ[μ] [[a, b]] :=
  Ioc_ae_eq_Icc

end MeasureTheory
