/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kim Morrison
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.RealRootCount

/-!
# Construction of an algebraic number that is not solvable by radicals

The polynomial `X ^ 5 - 4 * X + 2` is irreducible and has exactly three real roots.
Eisenstein’s criterion proves irreducibility; `real_root_count` checks a Sturm
chain proposed by Hex to count the real roots.
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
  have h : Irreducible (quintic ℤ) := by
    have hd : (quintic ℤ).degree = 5 := by
      dsimp [quintic]
      compute_degree!
    apply irreducible_of_eisenstein_criterion (P := Ideal.span {2})
    · rw [Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)]
      norm_num [Int.prime_iff_natAbs_prime]
      decide
    · rw [(quintic_monic ℤ).leadingCoeff, Ideal.mem_span_singleton]
      norm_num
    · intro n hn
      rw [hd] at hn
      have hn : n < 5 := by exact_mod_cast hn
      rw [Ideal.mem_span_singleton]
      interval_cases n <;> norm_num [quintic, coeff_add, coeff_sub, coeff_mul, coeff_X_pow, coeff_X]
    · rw [hd]; norm_num
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num [quintic]
    · exact (quintic_monic ℤ).isPrimitive
  simpa [quintic] using
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (quintic_monic ℤ).isPrimitive).mp h

private theorem quintic_real_roots : Fintype.card ((quintic ℚ).rootSet ℝ) = 3 :=
  real_root_count (quintic ℚ)

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
