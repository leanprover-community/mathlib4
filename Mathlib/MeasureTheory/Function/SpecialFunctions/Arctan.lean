/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.arctan
! leanprover-community/mathlib commit bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of arctan

-/


namespace Real

@[measurability]
theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.measurable
#align real.measurable_arctan Real.measurable_arctan

end Real

section RealComposition

open Real

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

@[measurability]
theorem Measurable.arctan : Measurable fun x => arctan (f x) :=
  measurable_arctan.comp hf
#align measurable.arctan Measurable.arctan

end RealComposition
