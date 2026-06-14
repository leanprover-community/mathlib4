/-
Copyright (c) 2026 Kenosian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Jang (Kenosian Protocol Platform)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Biology.Longevity -- Basic types and utilities

Common primitives for biological age and longevity algorithm contracts.
-/

namespace Mathlib.Biology.Longevity

/-- Age is a real number in [0, 150]. -/
def ValidAge (age : ℝ) : Prop := 0 ≤ age ∧ age ≤ 150

/-- Age acceleration: difference between biological and chronological age. -/
noncomputable def ageAcceleration (bioAge chronoAge : ℝ) : ℝ := bioAge - chronoAge

end Mathlib.Biology.Longevity
