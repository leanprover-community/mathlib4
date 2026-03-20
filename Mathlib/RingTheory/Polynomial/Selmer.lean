/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Polynomial.Morse

/-!
# Irreducibility and Galois Groups of Selmer Polynomials

This file shows that the Selmer polynomial `X ^ n - X - 1` is irreducible with Galois group `S_n`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.
- `X_pow_sub_X_sub_one_gal`: The Selmer polynomial `X ^ n - X - 1` has Galois group `S_n`.
-/

public section

namespace Polynomial

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [pow_zero, pow_one, or_true, true_or]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, right_eq_add] at h1)
  · exact one_ne_zero (by rwa [key, left_eq_add] at h1)
  · exact z_ne_zero (eq_zero_of_pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ, Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp ▸ (trinomial_monic zero_lt_one hn).isPrimitive

open Equiv Pointwise

open IntermediateField

attribute [local instance] Gal.splits_ℚ_ℂ

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  rcases le_or_gt n 1 with hn | hn
  · have : Subsingleton ((X ^ n - X - 1 : ℚ[X]).rootSet ℂ) := by
      apply Finset.card_le_one_iff_subsingleton_coe.mp
      grw [Multiset.toFinset_card_le, card_roots', natDegree_map_le, natDegree_sub_le,
        natDegree_sub_le, natDegree_X_pow, natDegree_X, natDegree_one, hn, max_self, Nat.max_zero]
    have : Unique ((X ^ n - X - 1 : ℚ[X]).Gal) := by
      refine Gal.uniqueGalOfSplits _ (Splits.of_natDegree_le_one (by compute_degree!))
    apply Unique.bijective
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have h := tada'' (X ^ n - X - 1) (hp ▸ trinomial_monic zero_lt_one hn)
    (X_pow_sub_X_sub_one_irreducible hn.ne') ?_
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · classical
    intro F _ hF
    have := hF.natDegree_eq_card_roots
    rw [Monic.natDegree_map (hp ▸ trinomial_monic zero_lt_one hn)] at this
    rw [this]
    rw [rootSet_def, aroots_def, Set.ncard_coe_finset]
    rw [Multiset.card_le_card_toFinset_add_one_iff]
    have h : ∀ x : F, 1 < (map (algebraMap ℤ F) (X ^ n - X - 1)).roots.count x →
        x = n / (1 - n) ∧ x ≠ 0 := by
      intro x hx
      rw [count_roots, one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
        (Monic.map _ (hp ▸ trinomial_monic zero_lt_one hn)).ne_zero] at hx
      have hx0 := hx 0 one_pos.le
      have hx1 := hx 1 le_rfl
      replace hx0 : x ^ n = 1 + x := by simpa [derivative_X_pow, sub_eq_iff_eq_add] using hx0
      replace hx1 : n * x ^ (n - 1) = 1 := by simpa [derivative_X_pow, sub_eq_iff_eq_add] using hx1
      rw [pow_sub_of_lt x hn, pow_one, hx0] at hx1
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx1
      rw [← mul_assoc, mul_inv_eq_one₀ hx0] at hx1
      rw [mul_add, mul_one, eq_comm, ← sub_eq_iff_eq_add, ← one_sub_mul, mul_comm] at hx1
      refine ⟨eq_div_of_mul_eq ?_ hx1, hx0⟩
      rw [sub_ne_zero]
      rintro hn0
      rw [← hn0] at hx1
      simp at hx1
    intro x y hx hy
    have hx' := h x hx
    replace hy := h y hy
    use hx'.1.trans hy.1.symm
    refine le_antisymm ?_ hx
    rw [count_roots]
    by_contra! hx''
    replace hx'' := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hx''
    simp [derivative_X_pow, Nat.cast_sub hn.le, sub_eq_zero, hx'.2] at hx''
    grind

end Polynomial
