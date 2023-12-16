/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.Selmer

#align_import wiedijk_100_theorems.abel_ruffini from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
# Construction of an algebraic number that is not solvable by radicals.

This file shows that the roots of `X ^ 5 - X - 1` are not solvable by radicals.

The main ingredients are:
 * `Polynomial.X_pow_sub_X_sub_one_irreducible_rat` and `Polynomial.X_pow_sub_X_sub_one_gal` in
  `RingTheory/Polynomial/Selmer.lean`: `X ^ 5 - X - 1` is irreducible and has full Galois group
 * `solvableByRad.isSolvable'` in `FieldTheory/AbelRuffini.lean`: an irreducible polynomial with
  an `IsSolvableByRad` root has solvable Galois group
 * `Equiv.Perm.not_solvable` in `GroupTheory/Solvable.lean`: the symmetric group is not solvable

-/


namespace AbelRuffini

set_option linter.uppercaseLean3 false

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

/-- A quintic polynomial that we will show is not solvable by radicals -/
noncomputable def quintic : ℚ[X] := X ^ 5 - X - 1

theorem degree_quintic : quintic.degree = 5 := by rw [quintic]; compute_degree; norm_num

theorem irreducible_quintic : Irreducible quintic :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

theorem gal_quintic : Bijective (galActionHom quintic ℂ) := X_pow_sub_X_sub_one_gal

theorem not_solvable_by_rad (x : ℂ) (hx : aeval x quintic = 0) : ¬IsSolvableByRad ℚ x := by
  apply mt (solvableByRad.isSolvable' irreducible_quintic hx)
  refine' fun h ↦ Equiv.Perm.not_solvable _ _ (solvable_of_surjective gal_quintic.2)
  rw [Cardinal.mk_fintype, card_rootSet_eq_natDegree irreducible_quintic.separable
    (IsAlgClosed.splits_codomain quintic), natDegree_eq_of_degree_eq_some degree_quintic]
  norm_num
#align abel_ruffini.not_solvable_by_rad AbelRuffini.not_solvable_by_rad

/-- **Abel-Ruffini Theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x := by
  have h1 : quintic.degree > 0 := by rw [degree_quintic]; norm_num
  have h2 : quintic ≠ 0 := fun h ↦ by simp [h] at h1
  obtain ⟨x, hx⟩ := exists_root_of_splits (algebraMap ℚ ℂ) (IsAlgClosed.splits_codomain quintic)
    h1.ne'
  exact ⟨x, ⟨quintic, h2, hx⟩, not_solvable_by_rad x hx⟩
#align abel_ruffini.exists_not_solvable_by_rad AbelRuffini.exists_not_solvable_by_rad

end AbelRuffini
