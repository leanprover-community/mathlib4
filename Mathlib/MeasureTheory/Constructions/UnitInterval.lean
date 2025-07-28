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
and shows it is a probability measure with no atoms.

It also contains some basic results on the volume of various interval sets.
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
    · exact fun _ hs ↦ measurableSet_Icc.subtype_image hs

@[measurability]
theorem measurable_symm : Measurable symm := continuous_symm.measurable

open Set

lemma measure_preserving_symm : volume = volume.map symm := by
  refine (volume : Measure I).ext_of_Ici ?_ ?_
  intro a
  rw [volume.map_apply measurable_symm measurableSet_Ici]
  have : σ ⁻¹' Ici a = Iic ⟨1 - a, mem_iff_one_sub_mem.mp a.2⟩ := by
    ext x
    constructor
    · intro (h : a.1 ≤ 1 - x)
      exact le_sub_comm.mp h
    · intro (h : x.1 ≤ 1 - a.1)
      exact le_sub_comm.mp h
  simp only [this, ← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Ici,
  image_subtype_val_Icc_Iic, Real.volume_Icc, sub_zero]

variable (x : I)

@[simp]
lemma volume_Iic : volume (Iic x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iic,
    Real.volume_Icc, sub_zero]

@[simp]
lemma volume_Iio : volume (Iio x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iio,
    Real.volume_Ico, sub_zero]

@[simp]
lemma volume_Ici : volume (Ici x) = .ofReal (1 - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Ici,
    Real.volume_Icc]

@[simp]
lemma volume_Ioi : volume (Ioi x) = .ofReal (1 - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Ioi,
    Real.volume_Ioc]

variable (y : I)

@[simp]
lemma volume_Icc : volume (Icc x y) = .ofReal (y - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc, Real.volume_Icc]

@[simp]
lemma volume_uIcc : volume (uIcc x y) = edist y x := by
  by_cases h : x ≤ y
  · rw [uIcc_of_le h, edist_dist y x, show dist y x = |y.1 - x| by rfl]
    replace h : x.1 ≤ y.1 := h
    simp only [volume_Icc, abs_of_nonneg <| sub_nonneg_of_le h]
  · rw [uIcc_of_gt (not_le.mp h), edist_comm, edist_dist x y, show dist x y = |x.1 - y| by rfl]
    replace h : y.1 < x.1 := not_le.mp h
    simp only [volume_Icc, abs_of_pos <| sub_pos.mpr h]

@[simp]
lemma volume_Ico : volume (Ico x y) = .ofReal (y - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Ico, Real.volume_Ico]

@[simp]
lemma volume_Ioc : volume (Ioc x y) = .ofReal (y - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Ioc, Real.volume_Ioc]

@[simp]
lemma volume_uIoc : volume (uIoc x y) = edist y x := by
  by_cases h : x ≤ y
  · rw [uIoc_of_le h, edist_dist y x, show dist y x = |y.1 - x| by rfl]
    replace h : x.1 ≤ y.1 := h
    simp only [volume_Ioc, abs_of_nonneg <| sub_nonneg_of_le h]
  · rw [uIoc_of_ge (not_le.mp h).le, edist_comm, edist_dist x y, show dist x y = |x.1 - y| by rfl]
    replace h : y.1 < x.1 := not_le.mp h
    simp only [volume_Ioc, abs_of_pos <| sub_pos.mpr h]

@[simp]
lemma volume_Ioo : volume (Ioo x y) = .ofReal (y - x) := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Ioo, Real.volume_Ioo]

@[simp]
lemma volume_uIoo : volume (uIoo x y) = edist y x := by
  by_cases h : x ≤ y
  · rw [uIoo_of_le h, edist_dist y x, show dist y x = |y.1 - x| by rfl]
    replace h : x.1 ≤ y.1 := h
    simp only [volume_Ioo, abs_of_nonneg <| sub_nonneg_of_le h]
  · rw [uIoo_of_ge (not_le.mp h).le, edist_comm, edist_dist x y, show dist x y = |x.1 - y| by rfl]
    replace h : y.1 < x.1 := not_le.mp h
    simp only [volume_Ioo, abs_of_pos <| sub_pos.mpr h]

end unitInterval
