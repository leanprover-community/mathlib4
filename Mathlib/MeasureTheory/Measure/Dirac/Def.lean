/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`.
See the file `Dirac.Basic` for the basic properties.
-/

@[expose] public section

/-- The dirac measure. -/
noncomputable def MeasureTheory.Measure.dirac {α : Type*} [MeasurableSpace α] (a : α) : Measure α :=
    (OuterMeasure.dirac a).toMeasure (by simp)
