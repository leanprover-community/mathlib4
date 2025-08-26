/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.Basic
import Mathlib.RingTheory.GlobalDimension

/-!

# Global Dimension of Regular Local Ring is equal to Krull Dimension

-/

universe u

variable (R : Type u) [CommRing R]

open IsLocalRing

lemma projectiveDimension_residueField_eq_ringKrullDim [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) = ringKrullDim R := by
  sorry

theorem globalDimension_eq_ringKrullDim [IsRegularLocalRing R] :
    globalDimension R = ringKrullDim R := by
  sorry
