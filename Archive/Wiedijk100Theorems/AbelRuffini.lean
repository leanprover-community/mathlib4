/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.EisensteinCriterion

#align_import wiedijk_100_theorems.abel_ruffini from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
# Construction of an algebraic number that is not solvable by radicals.

The main ingredients are:
 * `solvableByRad.isSolvable'` in `Mathlib/FieldTheory/AbelRuffini.lean` :
  an irreducible polynomial with an `IsSolvableByRad` root has solvable Galois group
 * `galActionHom_bijective_of_prime_degree'` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group
 * `Equiv.Perm.not_solvable` in `Mathlib/GroupTheory/Solvable.lean` : the symmetric group is not
  solvable

Then all that remains is the construction of a specific polynomial satisfying the conditions of
`galActionHom_bijective_of_prime_degree'`, which is done in this file.

-/


namespace AbelRuffini

set_option linter.uppercaseLean3 false

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- A quintic polynomial that we will show is irreducible -/
noncomputable def Φ : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)
#align abel_ruffini.Φ AbelRuffini.Φ

variable {R}

@[simp]
theorem map_Phi {S : Type*} [CommRing S] (f : R →+* S) : (Φ R a b).map f = Φ S a b := by simp [Φ]
#align abel_ruffini.map_Phi AbelRuffini.map_Phi

@[simp]
theorem coeff_zero_Phi : (Φ R a b).coeff 0 = (b : R) := by simp [Φ, coeff_X_pow]
#align abel_ruffini.coeff_zero_Phi AbelRuffini.coeff_zero_Phi

@[simp]
theorem coeff_five_Phi : (Φ R a b).coeff 5 = 1 := by
  simp [Φ, coeff_X, coeff_C, -map_natCast]
#align abel_ruffini.coeff_five_Phi AbelRuffini.coeff_five_Phi

variable [Nontrivial R]

theorem degree_Phi : (Φ R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [Φ, degree_add_eq_left_of_degree_lt]
    convert (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by norm_num))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by norm_num))
#align abel_ruffini.degree_Phi AbelRuffini.degree_Phi

theorem natDegree_Phi : (Φ R a b).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some (degree_Phi a b)
#align abel_ruffini.nat_degree_Phi AbelRuffini.natDegree_Phi

theorem leadingCoeff_Phi : (Φ R a b).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_Phi, coeff_five_Phi]
#align abel_ruffini.leading_coeff_Phi AbelRuffini.leadingCoeff_Phi

theorem monic_Phi : (Φ R a b).Monic :=
  leadingCoeff_Phi a b
#align abel_ruffini.monic_Phi AbelRuffini.monic_Phi

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
      simp (config := {decide := true}) only [Φ, coeff_X_pow, coeff_C, Int.natCast_dvd_natCast.mpr,
        hpb, if_true, coeff_C_mul, if_false, coeff_X_zero, hpa, coeff_add, zero_add, mul_zero,
        coeff_sub, add_zero, zero_sub, dvd_neg, neg_zero, dvd_mul_of_dvd_left]
    · simp only [degree_Phi, ← WithBot.coe_zero, WithBot.coe_lt_coe, Nat.succ_pos']
      decide
    · rw [coeff_zero_Phi, span_singleton_pow, mem_span_singleton]
      exact mt Int.natCast_dvd_natCast.mp hp2b
  all_goals exact Monic.isPrimitive (monic_Phi a b)
#align abel_ruffini.irreducible_Phi AbelRuffini.irreducible_Phi

set_option tactic.skipAssignedInstances false in
theorem real_roots_Phi_le : Fintype.card ((Φ ℚ a b).rootSet ℝ) ≤ 3 := by
  rw [← map_Phi a b (algebraMap ℤ ℚ), Φ, ← one_mul (X ^ 5), ← C_1]
  apply (card_rootSet_le_derivative _).trans
    (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
  suffices (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton by
    norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
    exact this
  rw [rootSet_C_mul_X_pow] <;>
  norm_num
#align abel_ruffini.real_roots_Phi_le AbelRuffini.real_roots_Phi_le

set_option tactic.skipAssignedInstances false in
theorem real_roots_Phi_ge_aux (hab : b < a) :
    ∃ x y : ℝ, x ≠ y ∧ aeval x (Φ ℚ a b) = 0 ∧ aeval y (Φ ℚ a b) = 0 := by
  let f : ℝ → ℝ := fun x : ℝ => aeval x (Φ ℚ a b)
  have hf : f = fun x : ℝ => x ^ 5 - a * x + b := by simp [f, Φ]
  have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (Φ ℚ a b).continuousOn_aeval
  have ha : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr (Nat.one_le_of_lt hab)
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hf0 : 0 ≤ f 0 := by simp [hf]
  by_cases hb : (1 : ℝ) - a + b < 0
  · have hf1 : f 1 < 0 := by simp [hf, hb]
    have hfa : 0 ≤ f a := by
      simp_rw [hf, ← sq]
      refine add_nonneg (sub_nonneg.mpr (pow_le_pow_right ha ?_)) ?_ <;> norm_num
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' hle (hc _) (Set.mem_Ioc.mpr ⟨hf1, hf0⟩)
    obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc ha (hc _) (Set.mem_Ioc.mpr ⟨hf1, hfa⟩)
    exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩
  · replace hb : (b : ℝ) = a - 1 := by linarith [show (b : ℝ) + 1 ≤ a from mod_cast hab]
    have hf1 : f 1 = 0 := by simp [hf, hb]
    have hfa :=
      calc
        f (-a) = (a : ℝ) ^ 2 - (a : ℝ) ^ 5 + b := by
          norm_num [hf, ← sq, sub_eq_add_neg, add_comm, Odd.neg_pow (by decide : Odd 5)]
        _ ≤ (a : ℝ) ^ 2 - (a : ℝ) ^ 3 + (a - 1) := by
          refine add_le_add (sub_le_sub_left (pow_le_pow_right ha ?_) _) ?_ <;> linarith
        _ = -((a : ℝ) - 1) ^ 2 * (a + 1) := by ring
        _ ≤ 0 := by nlinarith
    have ha' := neg_nonpos.mpr (hle.trans ha)
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Icc ha' (hc _) (Set.mem_Icc.mpr ⟨hfa, hf0⟩)
    exact ⟨x, 1, (hx1.trans_lt zero_lt_one).ne, hx2, hf1⟩
#align abel_ruffini.real_roots_Phi_ge_aux AbelRuffini.real_roots_Phi_ge_aux

theorem real_roots_Phi_ge (hab : b < a) : 2 ≤ Fintype.card ((Φ ℚ a b).rootSet ℝ) := by
  have q_ne_zero : Φ ℚ a b ≠ 0 := (monic_Phi a b).ne_zero
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_Phi_ge_aux a b hab
  have key : ↑({x, y} : Finset ℝ) ⊆ (Φ ℚ a b).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
  convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_not_mem (mt Finset.mem_singleton.mp hxy)]
#align abel_ruffini.real_roots_Phi_ge AbelRuffini.real_roots_Phi_ge

theorem complex_roots_Phi (h : (Φ ℚ a b).Separable) : Fintype.card ((Φ ℚ a b).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree h (IsAlgClosed.splits_codomain _)).trans (natDegree_Phi a b)
#align abel_ruffini.complex_roots_Phi AbelRuffini.complex_roots_Phi

theorem gal_Phi (hab : b < a) (h_irred : Irreducible (Φ ℚ a b)) :
    Bijective (galActionHom (Φ ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_Phi]; decide
  · rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact (real_roots_Phi_le a b).trans (Nat.le_succ 3)
  · simp_rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact real_roots_Phi_ge a b hab
#align abel_ruffini.gal_Phi AbelRuffini.gal_Phi

theorem not_solvable_by_rad (p : ℕ) (x : ℂ) (hx : aeval x (Φ ℚ a b) = 0) (hab : b < a)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : ¬IsSolvableByRad ℚ x := by
  have h_irred := irreducible_Phi a b p hp hpa hpb hp2b
  apply mt (solvableByRad.isSolvable' h_irred hx)
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (gal_Phi a b hab h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_Phi a b h_irred.separable]
#align abel_ruffini.not_solvable_by_rad AbelRuffini.not_solvable_by_rad

theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) : ¬IsSolvableByRad ℚ x := by
  apply not_solvable_by_rad 4 2 2 x hx <;> decide
#align abel_ruffini.not_solvable_by_rad' AbelRuffini.not_solvable_by_rad'

/-- **Abel-Ruffini Theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x := by
  obtain ⟨x, hx⟩ := exists_root_of_splits (algebraMap ℚ ℂ) (IsAlgClosed.splits_codomain (Φ ℚ 4 2))
    (ne_of_eq_of_ne (degree_Phi 4 2) (mt WithBot.coe_eq_coe.mp (show 5 ≠ 0 by norm_num)))
  exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩
#align abel_ruffini.exists_not_solvable_by_rad AbelRuffini.exists_not_solvable_by_rad

end AbelRuffini
