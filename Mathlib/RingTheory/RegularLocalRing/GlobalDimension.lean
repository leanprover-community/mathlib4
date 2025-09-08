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

set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory

lemma finite_projectiveDimension_of_isRegularLocalRing_aux [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (i : ℕ) : IsLocalRing.depth M + i ≥ ringKrullDim R →
    ∃ n, HasProjectiveDimensionLE M n := by
  induction' i with i ih generalizing M
  · simp only [CharP.cast_eq_zero, add_zero, ge_iff_le]
    intro le
    by_cases ntr : Nontrivial M
    · let _ := (isMaximalCohenMacaulay_def M).mpr (le_antisymm (depth_le_ringKrullDim M) le)
      let _ := free_of_isMaximalCohenMacaulay_of_isRegularLocalRing M
      use 0
      exact instHasProjectiveDimensionLTOfNatNatOfProjective M
    · have := ModuleCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp ntr)
      have := CategoryTheory.Limits.IsZero.hasProjectiveDimensionLT_zero this
      use 0
      exact CategoryTheory.instHasProjectiveDimensionLTSucc M 0
  · simp only [Nat.cast_add, Nat.cast_one, ge_iff_le, ← add_assoc]
    intro le
    rcases Module.Finite.exists_fin' R M with ⟨n, f', hf'⟩
    --fix the universe problem of `f`
    /-let S : ShortComplex (ModuleCat.{v} R) := {
      f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
      g := ModuleCat.ofHom.{v} f
      zero := by
        ext x
        simp }-/
    sorry

lemma finite_projectiveDimension_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : ∃ n, HasProjectiveDimensionLE M n := by
  rcases exist_nat_eq R with ⟨m, hm⟩
  apply finite_projectiveDimension_of_isRegularLocalRing_aux R M m
  simpa [hm] using WithBot.coe_le_coe.mpr le_add_self

/- have some universe problem
lemma projectiveDimension_residueField_eq_ringKrullDim [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) = ringKrullDim R := by
  --follows from AB thm and above easily
  sorry
-/

theorem globalDimension_eq_ringKrullDim [IsRegularLocalRing R] :
    globalDimension.{u, v} R = ringKrullDim R := by

  sorry
