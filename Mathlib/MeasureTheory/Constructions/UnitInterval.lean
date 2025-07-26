/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Gaëtan Serré
-/
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The canonical measure on the unit interval

This file provides a `MeasureTheory.MeasureSpace` instance on `unitInterval`,
and shows it is a probability measure.
-/
open scoped unitInterval
open MeasureTheory

namespace unitInterval

noncomputable instance : MeasureSpace I := Measure.Subtype.measureSpace

theorem volume_def : (volume : Measure I) = volume.comap Subtype.val := rfl

instance : IsProbabilityMeasure (volume : Measure I) where
  measure_univ := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one]

instance : NoAtoms (volume : Measure I) where
  measure_singleton x := by
    rw [volume_def, Measure.comap_apply _ Subtype.val_injective ?_ _ (measurableSet_singleton x)]
    · simp only [Set.image_singleton, measure_singleton]
    · intro s hs
      exact measurableSet_Icc.subtype_image hs

@[measurability]
theorem measurable_symm : Measurable symm := continuous_symm.measurable

open Set

@[simp]
lemma volume_Icc (x : I) : volume (Icc 0 x) = .ofReal x := by
  simp [← volume_image_subtype_coe measurableSet_Icc, Real.volume_Icc, sub_zero]

@[simp]
lemma volume_Ico (x : I) : volume (Ico 0 x) = .ofReal x := by
  suffices volume (Ico 0 x) = volume (Icc 0 x) by
    rw [this]
    exact volume_Icc x
  refine measure_eq_measure_of_null_diff Ico_subset_Icc_self ?_
  rw [Icc_diff_Ico_same nonneg']
  exact measure_singleton x

@[simp]
lemma volume_Ioc (x : I) : volume (Ioc 0 x) = .ofReal x := by
  suffices volume (Ioc 0 x) = volume (Icc 0 x) by
    rw [this]
    exact volume_Icc x
  refine measure_eq_measure_of_null_diff Ioc_subset_Icc_self ?_
  rw [Icc_diff_Ioc_same nonneg']
  exact measure_singleton 0

lemma volume_Ioo (x : I) : volume (Ioo 0 x) = .ofReal x := by
  by_cases hx : 0 < x
  · suffices volume (Ioo 0 x) = volume (Ico 0 x) by
      rw [this]
      exact volume_Ico x
    refine measure_eq_measure_of_null_diff Ioo_subset_Ico_self ?_
    rw [Ico_diff_Ioo_same hx]
    exact measure_singleton 0
  · rw [le_zero_iff.mp (not_lt.mp hx)]
    simp only [lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, measure_empty, Icc.coe_zero,
      ENNReal.ofReal_zero]

@[simp]
lemma volume_Iic (x : I) : volume (Iic x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iic,
    Real.volume_Icc, sub_zero]

@[simp]
lemma volume_Iio (x : I) : volume (Iio x) = .ofReal x := by
  suffices volume (Iio x) = volume (Iic x) by
    rw [this]
    exact volume_Iic x
  refine measure_eq_measure_of_null_diff (Iio_subset_Iic_self) ?_
  rw [Iic_diff_Iio_same, measure_singleton x]


end unitInterval
