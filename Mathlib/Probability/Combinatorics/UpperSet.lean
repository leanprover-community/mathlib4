/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib

/-!
# TODO

-/

open MeasureTheory ProbabilityTheory Measure

variable {ι : Type*}

example {𝓕 : Set (Set ι)} (h𝓕 : IsUpperSet 𝓕) (h𝓕_nonempty : Nonempty 𝓕) :
  Set.univ ∈ 𝓕 := by aesop

-- ∅ ∉ 𝓕

-- Prove existence of threshold, define threshold

-- Define coupling + show monotonicity
