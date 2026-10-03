/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Existence of intermediate fields of particular degrees

We prove the existence of intermediate fields of particular degrees in a Galois extension
using Sylow's first theorem.
-/

@[expose] public section

open Module

namespace IsGalois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_intermediateField_finrank_eq_pow_prime {p n : ℕ} (hp : p.Prime)
    (hn : p ^ n ∣ finrank K L) :
    ∃ M : IntermediateField K L, finrank M L = p ^ n := by
  have := Fact.mk hp
  rw [← IsGalois.card_aut_eq_finrank K L] at hn
  rcases Sylow.exists_subgroup_card_pow_prime p hn with ⟨H, hH⟩
  exact ⟨IntermediateField.fixedField H, by rwa [IntermediateField.finrank_fixedField_eq_card]⟩

theorem exists_intermediateField_finrank_eq_pow_prime_mul {p n a : ℕ} (hp : p.Prime)
    (hn : Module.finrank K L = p ^ n * a) {m : ℕ} (hm : m ≤ n) :
    ∃ M : IntermediateField K L, Module.finrank K M = p ^ m * a := by
  have : p ^ (n - m) ∣ Module.finrank K L := by
    simpa [hn] using Nat.pow_dvd_of_le_of_pow_dvd (n := n) (by simp) (by simp)
  rcases IsGalois.exists_intermediateField_finrank_eq_pow_prime hp this with ⟨M, hM⟩
  use M
  rw [← Module.finrank_div_finrank_cancel_right_of_nontrivial _ _ L, hn, hM,
      ← Nat.pow_sub_mul_pow _ hm, mul_assoc, Nat.mul_div_right _ (by positivity [hp.pos])]

theorem exists_intermediateField_ge_card_pow_prime_of_card_pow_prime {m n p : ℕ} (hp : p.Prime)
    {M : IntermediateField K L} (hM : Module.finrank M L = p ^ n) (hm : m ≤ n) :
    ∃ N ≥ M, Module.finrank N L = p ^ m := by
  rcases Sylow.exists_subgroup_le_card_pow_prime_of_le_pow (H := M.fixingSubgroup)
    hp (by rw [IsGalois.card_fixingSubgroup_eq_finrank, hM]) hm with
    ⟨H', hH'₁, hH'₂⟩
  exact ⟨IntermediateField.fixedField H',
        by simpa [IntermediateField.le_iff_le] using hH'₁,
        by simpa [IntermediateField.finrank_fixedField_eq_card] using hH'₂⟩

theorem exists_intermediateField_ge_card_pow_prime_mul_of_card_pow_prime_mul
    {p n a : ℕ} (hp : p.Prime) (hL : Module.finrank K L = p ^ n * a)
    {m m' : ℕ} {M : IntermediateField K L} (hM : Module.finrank K M = p ^ m * a)
    (hm'₁ : m ≤ m') (hm'₂ : m' ≤ n) :
    ∃ N ≥ M, Module.finrank K N = p ^ m' * a := by
  by_cases a = 0
  · exact ⟨M, by simp, by simp_all⟩
  have : Module.finrank M L = p ^ (n - m) := by
    rw [← Module.finrank_div_finrank_cancel_left_of_nontrivial K, hM, hL,
        ← Nat.pow_sub_mul_pow _ (by lia : m ≤ n), mul_assoc,
        Nat.mul_div_left _ (by positivity [hp.pos])]
  rcases IsGalois.exists_intermediateField_ge_card_pow_prime_of_card_pow_prime hp (M := M)
    (n := n - m) (m := n - m') this (by lia) with ⟨N, hN, hNrk⟩
  refine ⟨N, hN, ?_⟩
  rw [← Module.finrank_div_finrank_cancel_right_of_nontrivial _ _ L, hL, hNrk,
      ← Nat.pow_sub_mul_pow _ hm'₂, mul_assoc, Nat.mul_div_right _ (by positivity [hp.pos])]

end IsGalois
