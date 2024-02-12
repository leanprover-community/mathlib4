/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Topology.UnitInterval
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
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one]

theorem measurable_symm : Measurable symm := (measurable_subtype_coe.const_sub _).subtype_mk

/-- `unitInterval.symm` as a `MeasurableEquiv`. -/
@[simps]
def symm_measurableEquiv : I ≃ᵐ I where
  toFun := σ
  invFun := σ
  left_inv := symm_symm
  right_inv := symm_symm
  measurable_toFun := measurable_symm
  measurable_invFun := measurable_symm

end unitInterval
