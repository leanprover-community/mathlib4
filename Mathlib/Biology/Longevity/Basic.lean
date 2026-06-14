/-
Copyright (c) 2026 Peter Jang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Jang
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Mathlib.Biology.Longevity

Common types for biological age and longevity algorithm contracts.
-/

namespace Mathlib.Biology.Longevity

/-- A biologically valid age lies in the interval [0, 150]. -/
def ValidAge (age : ℝ) : Prop := 0 ≤ age ∧ age ≤ 150

/-- Age acceleration: the difference between estimated biological age and chronological age. -/
noncomputable def ageAcceleration (bioAge chronoAge : ℝ) : ℝ := bioAge - chronoAge

end Mathlib.Biology.Longevity
