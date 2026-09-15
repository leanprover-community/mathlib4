/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Tactic.RealRootCount

/-!
# Construction of an algebraic number that is not solvable by radicals

The main ingredients are:

* `isSolvable_gal_of_irreducible` in `Mathlib/FieldTheory/AbelRuffini.lean`:
  an irreducible polynomial with an `IsSolvableByRad` root has solvable Galois group.
* `galActionHom_bijective_of_prime_degree'` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group.
* `Equiv.Perm.not_solvable` in `Mathlib/GroupTheory/Solvable.lean` : the symmetric group is not
  solvable.

The general family `Φ R a b = X ^ 5 - C a * X + C b` supplies such examples.
For the concrete witness `Φ ℚ 4 2`, `real_root_count` checks a Sturm chain proposed
by Hex and proves there are exactly three real roots.
-/

@[expose] public section

namespace AbelRuffini

open Function Polynomial Polynomial.Gal Ideal

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- A quintic polynomial that we will show is irreducible -/
noncomputable def Φ : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)

variable {R}

@[simp]
theorem map_Phi {S : Type*} [CommRing S] (f : R →+* S) : (Φ R a b).map f = Φ S a b := by simp [Φ]

@[simp]
theorem coeff_zero_Phi : (Φ R a b).coeff 0 = (b : R) := by simp [Φ, coeff_X_pow]

@[simp]
theorem coeff_five_Phi : (Φ R a b).coeff 5 = 1 := by
  simp [Φ, -map_natCast]

variable [Nontrivial R]

theorem degree_Phi : (Φ R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [Φ, degree_add_eq_left_of_degree_lt]
    convert! (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by simp))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by simp))

theorem natDegree_Phi : (Φ R a b).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some (degree_Phi a b)

theorem leadingCoeff_Phi : (Φ R a b).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_Phi, coeff_five_Phi]

theorem monic_Phi : (Φ R a b).Monic :=
  leadingCoeff_Phi a b

theorem irreducible_Phi (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    Irreducible (Φ ℚ a b) := by
  rw [← map_Phi a b (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion
    · rwa [span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero), Int.prime_iff_natAbs_prime]
    · rw [leadingCoeff_Phi, mem_span_singleton]
      exact mod_cast mt Nat.dvd_one.mp hp.ne_one
    · intro n hn
      rw [mem_span_singleton]
      rw [degree_Phi] at hn; norm_cast at hn
      interval_cases n <;>
      simp +decide only [Φ, coeff_X_pow, coeff_C, Int.natCast_dvd_natCast.mpr,
        hpb, ite_true, coeff_C_mul, ite_false, coeff_X_zero, hpa, coeff_add, zero_add, mul_zero,
        coeff_sub, add_zero, zero_sub, dvd_neg, neg_zero, dvd_mul_of_dvd_left]
    · simp only [degree_Phi, ← WithBot.coe_zero]
      decide
    · rw [coeff_zero_Phi, span_singleton_pow, mem_span_singleton]
      exact mt Int.natCast_dvd_natCast.mp hp2b
  all_goals exact Monic.isPrimitive (monic_Phi a b)

theorem complex_roots_Phi (h : (Φ ℚ a b).Separable) : Fintype.card ((Φ ℚ a b).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree h (IsAlgClosed.splits _)).trans (natDegree_Phi a b)

theorem gal_Phi (h_irred : Irreducible (Φ ℚ a b))
    (hreal : Fintype.card ((Φ ℚ a b).rootSet ℝ) = 3) :
    Bijective (galActionHom (Φ ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_Phi]; decide
  · rw [hreal, complex_roots_Phi a b h_irred.separable]; decide
  · rw [hreal, complex_roots_Phi a b h_irred.separable]; decide

theorem not_solvable_by_rad (p : ℕ) (x : ℂ) (hx : aeval x (Φ ℚ a b) = 0)
    (hreal : Fintype.card ((Φ ℚ a b).rootSet ℝ) = 3) (hp : p.Prime)
    (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : x ∉ solvableByRad ℚ ℂ := by
  have h_irred := irreducible_Phi a b p hp hpa hpb hp2b
  apply mt (isSolvable_gal_of_irreducible · h_irred hx)
  intro h
  refine Equiv.Perm.not_isSolvable _ (le_of_eq ?_)
    (Group.isSolvable_of_surjective (gal_Phi a b h_irred hreal).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_Phi a b h_irred.separable]

theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) : x ∉ solvableByRad ℚ ℂ := by
  apply not_solvable_by_rad 4 2 2 x hx (by real_root_count) <;> decide

/-- **Abel-Ruffini Theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ x ∉ solvableByRad ℚ ℂ := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩

end AbelRuffini
