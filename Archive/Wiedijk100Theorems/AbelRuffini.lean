/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kim Morrison
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.Hex.Irreducible
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.IsolateRoots
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhaus.FactorTactic
public meta import HexBerlekampZassenhaus.FactorTactic

/-!
# Construction of an algebraic number that is not solvable by radicals

The polynomial `X ^ 5 - 4 * X + 2` is irreducible and has exactly three real roots.
Hex certifies these two computations using `irreducibility` and `isolate_roots`.
Its Galois group is therefore the symmetric group on five letters, which is not solvable.
The Abel–Ruffini theorem implies that none of its roots is solvable by radicals.
-/

public section

namespace AbelRuffini

open Function Polynomial Polynomial.Gal

attribute [local instance] splits_ℚ_ℂ

/-- The quintic used to construct an algebraic number not solvable by radicals. -/
noncomputable def quintic (R : Type*) [CommRing R] : R[X] := X ^ 5 - 4 * X + 2

private theorem quintic_monic (R : Type*) [CommRing R] [Nontrivial R] :
    (quintic R).Monic := by
  dsimp [quintic]
  monicity <;> norm_num

private theorem quintic_irreducible : Irreducible (quintic ℚ) := by
  have hc : Hex.ZPoly.Irreducible (Hex.DensePoly.ofCoeffs #[2, -4, 0, 0, 0, 1]) :=
    irreducibility (Hex.DensePoly.ofCoeffs #[2, -4, 0, 0, 0, 1])
  have h : Irreducible (quintic ℤ) := by
    convert (Hex.ZPoly.irreducible_iff _).mp hc using 1
    simp [quintic, HexPolyZMathlib.toPolynomial, HexPolyMathlib.toPolynomial,
      show (Hex.DensePoly.ofCoeffs #[2, -4, 0, 0, 0, 1] : Hex.ZPoly).size = 6 from rfl,
      Finset.sum_range_succ, Hex.DensePoly.coeff_ofCoeffs, ← C_mul_X_pow_eq_monomial]
    ring
  simpa [quintic] using
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (quintic_monic ℤ).isPrimitive).mp h

private noncomputable def quintic_isolation : Hex.IsolatedRealRoots (quintic ℚ) 3 :=
  isolate_roots (X ^ 5 - 4 * X + 2 : ℚ[X])

private theorem quintic_real_roots : Fintype.card ((quintic ℚ).rootSet ℝ) = 3 :=
  quintic_isolation.card_rootSet (quintic_monic ℚ).ne_zero

private theorem quintic_natDegree : (quintic ℚ).natDegree = 5 := by
  dsimp [quintic]
  compute_degree <;> norm_num

private theorem quintic_complex_roots : Fintype.card ((quintic ℚ).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree quintic_irreducible.separable (IsAlgClosed.splits _)).trans
    quintic_natDegree

private theorem quintic_gal : Bijective (galActionHom (quintic ℚ) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' quintic_irreducible
  · rw [quintic_natDegree]
    decide
  · rw [quintic_real_roots, quintic_complex_roots]
    decide
  · rw [quintic_real_roots, quintic_complex_roots]
    decide

/-- No complex root of `X ^ 5 - 4 * X + 2` is solvable by radicals over `ℚ`. -/
theorem not_solvable_by_rad (x : ℂ) (hx : aeval x (quintic ℚ) = 0) :
    x ∉ solvableByRad ℚ ℂ := by
  apply mt (isSolvable_gal_of_irreducible · quintic_irreducible hx)
  intro h
  refine Equiv.Perm.not_isSolvable _ (le_of_eq ?_)
    (Group.isSolvable_of_surjective quintic_gal.2)
  rw_mod_cast [Cardinal.mk_fintype, quintic_complex_roots]

/-- **Abel–Ruffini theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ x ∉ solvableByRad ℚ ℂ := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ (quintic ℚ)
    (by rw [degree_eq_natDegree (quintic_monic ℚ).ne_zero, quintic_natDegree]; norm_num)
  exact ⟨x, ⟨quintic ℚ, (quintic_monic ℚ).ne_zero, hx⟩, not_solvable_by_rad x hx⟩

end AbelRuffini
