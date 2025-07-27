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

variable (x : I)

@[simp]
lemma volume_Iic : volume (Iic x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iic,
    Real.volume_Icc, sub_zero]

@[simp]
lemma volume_Iio : volume (Iio x) = .ofReal x := by
  suffices volume (Iio x) = volume (Iic x) by
    rw [this]
    exact volume_Iic x
  refine measure_eq_measure_of_null_diff (Iio_subset_Iic_self) ?_
  rw [Iic_diff_Iio_same, measure_singleton x]

variable (y : I)

example (a b : ℝ) : edist a b = .ofReal (|a - b|) := by
  exact edist_dist a b

@[simp]
lemma volume_Icc : volume (Icc x y) = .ofReal (y - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc, Real.volume_Icc]

@[simp]
lemma volume_uIcc : volume (uIcc x y) = edist y x := by
  by_cases h : x ≤ y
  · simp only [uIcc_of_le h, volume_Icc]
    suffices |y.1 - x| = y - x by
      rw [←this]
      exact (edist_dist y x).symm
    exact abs_of_nonneg <| sub_nonneg_of_le h
  · simp only [uIcc_of_gt (not_le.mp h), volume_Icc]
    rw [edist_comm]
    suffices |x - y.1| = x - y by
      rw [←this]
      exact (edist_dist x y).symm
    exact abs_of_pos <| sub_pos.mpr (not_le.mp h)

@[simp]
lemma volume_Ico : volume (Ico x y) = .ofReal (y - x) := by
  by_cases hx : x < y
  · suffices volume (Ico x y) = volume (Icc x y) by
      rw [this]
      exact volume_Icc x y
    refine measure_eq_measure_of_null_diff Ico_subset_Icc_self ?_
    rw [Icc_diff_Ico_same hx.le]
    exact measure_singleton y
  · rw [Ico_eq_empty hx, measure_empty]
    apply Eq.symm
    rw [ENNReal.ofReal_eq_zero]
    exact tsub_nonpos.mpr (not_lt.mp hx)

@[simp]
lemma volume_Ioc : volume (Ioc x y) = .ofReal (y - x) := by
  by_cases hx : x < y
  · suffices volume (Ioc x y) = volume (Icc x y) by
      rw [this]
      exact volume_Icc x y
    refine measure_eq_measure_of_null_diff Ioc_subset_Icc_self ?_
    rw [Icc_diff_Ioc_same hx.le]
    exact measure_singleton x
  · rw [Ioc_eq_empty hx, measure_empty]
    apply Eq.symm
    rw [ENNReal.ofReal_eq_zero]
    exact tsub_nonpos.mpr (not_lt.mp hx)

@[simp]
lemma volume_uIoc : volume (uIoc x y) = edist y x := by
  by_cases h : x ≤ y
  · simp only [uIoc_of_le h, volume_Ioc]
    suffices |y.1 - x| = y - x by
      rw [←this]
      exact (edist_dist y x).symm
    exact abs_of_nonneg <| sub_nonneg_of_le h
  · simp only [uIoc_of_ge (not_le.mp h).le, volume_Ioc]
    rw [edist_comm]
    suffices |x - y.1| = x - y by
      rw [←this]
      exact (edist_dist x y).symm
    exact abs_of_pos <| sub_pos.mpr (not_le.mp h)

@[simp]
lemma volume_Ioo : volume (Ioo x y) = .ofReal (y - x) := by
  by_cases hx : x < y
  · suffices volume (Ioo x y) = volume (Ico x y) by
      rw [this]
      exact volume_Ico x y
    refine measure_eq_measure_of_null_diff Ioo_subset_Ico_self ?_
    rw [Ico_diff_Ioo_same hx]
    exact measure_singleton x
  · rw [Ioo_eq_empty hx, measure_empty]
    apply Eq.symm
    rw [ENNReal.ofReal_eq_zero]
    exact tsub_nonpos.mpr (not_lt.mp hx)

@[simp]
lemma volume_uIoo : volume (uIoo x y) = edist y x := by
  by_cases h : x ≤ y
  · simp only [uIoo_of_le h, volume_Ioo]
    suffices |y.1 - x| = y - x by
      rw [←this]
      exact (edist_dist y x).symm
    exact abs_of_nonneg <| sub_nonneg_of_le h
  · simp only [uIoo_of_ge (not_le.mp h).le, volume_Ioo]
    rw [edist_comm]
    suffices |x - y.1| = x - y by
      rw [←this]
      exact (edist_dist x y).symm
    exact abs_of_pos <| sub_pos.mpr (not_le.mp h)

end unitInterval
