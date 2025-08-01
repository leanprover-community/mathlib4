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

lemma measurableEmbedding_coe : MeasurableEmbedding ((↑) : I → ℝ) where
  injective := Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Icc.subtype_image

lemma volume_apply {s : Set I} : volume s = volume (Subtype.val '' s) :=
  measurableEmbedding_coe.comap_apply ..

instance : NoAtoms (volume : Measure I) where
  measure_singleton x := by simp only [volume_apply, Set.image_singleton, measure_singleton]

@[measurability]
theorem measurable_symm : Measurable symm := continuous_symm.measurable

open Set

variable (x : I)

@[simp]
lemma volume_Iic : volume (Iic x) = .ofReal x := by
  simp only [volume_apply, image_subtype_val_Icc_Iic, Real.volume_Icc, sub_zero]

@[simp]
lemma volume_Iio : volume (Iio x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iio,
    Real.volume_Ico, sub_zero]

@[simp]
lemma volume_Ici : volume (Ici x) = .ofReal (1 - x) := by
  simp only [volume_apply, image_subtype_val_Icc_Ici, Real.volume_Icc]

@[simp]
lemma volume_Ioi : volume (Ioi x) = .ofReal (1 - x) := by
  simp only [volume_apply, image_subtype_val_Icc_Ioi, Real.volume_Ioc]

variable (y : I)

@[simp]
lemma volume_Icc : volume (Icc x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Icc, Real.volume_Icc]

@[simp]
lemma volume_uIcc : volume (uIcc x y) = edist y x := by
  simp only [uIcc, volume_apply, image_subtype_val_Icc, Icc.coe_inf, Icc.coe_sup, Real.volume_Icc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

@[simp]
lemma volume_Ico : volume (Ico x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ico, Real.volume_Ico]

@[simp]
lemma volume_Ioc : volume (Ioc x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ioc, Real.volume_Ioc]

@[simp]
lemma volume_uIoc : volume (uIoc x y) = edist y x := by
  simp only [uIoc, volume_apply, image_subtype_val_Ioc, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]


@[simp]
lemma volume_Ioo : volume (Ioo x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ioo, Real.volume_Ioo]

@[simp]
lemma volume_uIoo : volume (uIoo x y) = edist y x := by
  simp only [uIoo, volume_apply, image_subtype_val_Ioo, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioo,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

end unitInterval
