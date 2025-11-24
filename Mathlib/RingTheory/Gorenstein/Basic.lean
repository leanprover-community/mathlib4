/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Gorenstein.Defs

/-!

# Basic Properties of Gorenstein Local Ring

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

section

lemma isGoresteinLocalRing_localization [IsGorensteinLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsGorensteinLocalRing (Localization.AtPrime p) := by
  sorry

lemma isGoresteinLocalRing_of_isLocalization [IsGorensteinLocalRing R] (p : Ideal R) [p.IsPrime]
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] :
    IsGorensteinLocalRing Rₚ := by
  sorry

end
