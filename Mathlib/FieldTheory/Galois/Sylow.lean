/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Existence of prime-power-index intermediate fields

We prove the existence of prime-power-index intermediate fields in a Galois extension
using Sylow's first theorem.
-/

public section

open Module

namespace IsGalois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_intermediateField_finrank_pow_prime_le_le {p : ℕ} (hp : p.Prime) {n : ℕ}
    {M N : IntermediateField K L} (hM : finrank M L ∣ p ^ n) (hN : p ^ n ∣ finrank N L)
    (hMN : N ≤ M) :
    ∃ O : IntermediateField K L, finrank O L = p ^ n ∧ N ≤ O ∧ O ≤ M := by
  rw [← IsGalois.card_fixingSubgroup_eq_finrank] at hM hN
  rcases Sylow.exists_subgroup_card_pow_prime_le_le hp hM hN
    (IntermediateField.fixingSubgroup_le hMN) with ⟨G, _⟩
  use IntermediateField.fixedField G
  grind [IntermediateField.le_fixedField_iff_le_fixingSubgroup,
    IntermediateField.finrank_fixedField_eq_card, fixedField_le_iff_fixingSubgroup_le]

theorem exists_intermediateField_finrank_pow_prime_le {p : ℕ} (hp : p.Prime) {n : ℕ}
    (h : p ^ n ∣ finrank K L) (M : IntermediateField K L) (hM : finrank M L ∣ p ^ n) :
    ∃ N ≤ M, finrank N L = p ^ n := by
  grind [exists_intermediateField_finrank_pow_prime_le_le hp hM (by simpa) bot_le]

theorem exists_intermediateField_finrank_pow_prime_ge {p : ℕ} (hp : p.Prime) {n : ℕ}
    (M : IntermediateField K L) (hM : p ^ n ∣ finrank M L) :
    ∃ N ≥ M, finrank N L = p ^ n := by
  grind [exists_intermediateField_finrank_pow_prime_le_le hp (by simp) hM le_top]

theorem exists_intermediateField_finrank_pow_prime {p : ℕ} (hp : p.Prime) {n : ℕ}
    (h : p ^ n ∣ finrank K L) :
    ∃ N : IntermediateField K L, finrank N L = p ^ n := by
  simpa using exists_intermediateField_finrank_pow_prime_le hp h ⊤ (by simp)

end IsGalois
