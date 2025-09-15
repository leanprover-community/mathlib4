/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
import Mathlib.RingTheory.RegularLocalRing.RegularRing.Basic
/-!

# Global Dimension of Regular Ring is equal to Krull Dimension

-/

universe u v

variable {R : Type u} [CommRing R]

open IsLocalRing CategoryTheory

variable (R) in
theorem globalDimension_eq_ringKrullDim [Small.{v} R] [IsRegularRing R] :
    globalDimension.{v} R = ringKrullDim R := by
  sorry
