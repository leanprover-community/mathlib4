/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Gaëtan Serré
-/
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The canonical measure on the unit interval

This file provides a `MeasureTheory.MeasureSpace` instance on `unitInterval`,
and shows it is a probability measure with no atoms.

It also contains some basic results on the volume of various interval sets.
-/

open scoped unitInterval
open MeasureTheory Measure Set

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

lemma measurePreserving_coe : MeasurePreserving ((↑) : I → ℝ) volume (volume.restrict I) :=
  measurePreserving_subtype_coe measurableSet_Icc

instance : NoAtoms (volume : Measure I) where
  measure_singleton x := by simp [volume_apply]

@[measurability]
theorem measurable_symm : Measurable σ := continuous_symm.measurable

/-- `unitInterval.symm` bundled as a measurable equivalence. -/
@[simps]
def symmMeasurableEquiv : I ≃ᵐ I where
  toFun := σ
  invFun := σ
  left_inv := symm_symm
  right_inv := symm_symm
  measurable_toFun := measurable_symm
  measurable_invFun := measurable_symm

@[simp]
lemma symm_symmMeasurableEquiv : symmMeasurableEquiv.symm = symmMeasurableEquiv := rfl

@[simp]
lemma coe_symmMeasurableEquiv : symmMeasurableEquiv = σ := rfl

lemma measurePreserving_symm : MeasurePreserving symm volume volume where
  measurable := measurable_symm
  map_eq := by
    ext s hs
    apply symmMeasurableEquiv.map_apply _ |>.trans
    conv_lhs => rw [coe_symmMeasurableEquiv, volume_apply, image_coe_preimage_symm,
      ← map_apply (by fun_prop) (measurableSet_Icc.subtype_image hs),
      volume.measurePreserving_sub_left 1 |>.map_eq, ← volume_apply]

end unitInterval
