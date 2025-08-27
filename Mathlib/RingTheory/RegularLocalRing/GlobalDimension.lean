/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.Basic
import Mathlib.RingTheory.GlobalDimension
import Mathlib.RingTheory.CohenMacaulay.Maximal
/-!

# Global Dimension of Regular Local Ring is equal to Krull Dimension

-/

--set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory

lemma finite_projectiveDimension_of_isRegularLocalRing [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : ∃ n, HasProjectiveDimensionLE M n := by
  sorry

/- have some universe problem
lemma projectiveDimension_residueField_eq_ringKrullDim [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) = ringKrullDim R := by
  --follows from AB thm and above easily
  sorry
-/

theorem globalDimension_eq_ringKrullDim [IsRegularLocalRing R] :
    globalDimension.{u, v} R = ringKrullDim R := by

  sorry
