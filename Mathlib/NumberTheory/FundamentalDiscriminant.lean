/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Squarefree

/-!
# Fundamental discriminants

A fundamental discriminant is an integer `D ≡ 0, 1 [ZMOD 4]` that is primitive, i.e. not a proper
square multiple of a smaller discriminant. These are exactly the discriminants of quadratic
fields.

## Main definitions

* `Int.IsFundamentalDiscr`: `D` is a fundamental discriminant.

## Main results

* `Int.isFundamentalDiscr_iff_squarefree`: the concrete squarefree characterization, `D ≡ 1 mod 4`
  squarefree or `D = 4m` with `m` squarefree and `m ≡ 2, 3 mod 4`.
-/

@[expose] public section

namespace Int

/-- `D` is a fundamental discriminant: it is a discriminant (`D % 4 = 0 ∨ 1`) and primitive, i.e.
`D / 4 ≢ 0, 1 [ZMOD 4]` when `4 ∣ D`, and no odd prime square divides `D`. -/
def IsFundamentalDiscr (D : ℤ) : Prop :=
  (D % 4 = 0 ∨ D % 4 = 1) ∧
    (∀ x : ℤ, D = 4 * x → ¬ 4 ∣ x ∧ ¬ x % 4 = 1) ∧
    ∀ p : ℕ, Nat.Prime p → Odd p → ¬ (p : ℤ) ^ 2 ∣ D

theorem isFundamentalDiscr_def {D : ℤ} :
    IsFundamentalDiscr D ↔
      (D % 4 = 0 ∨ D % 4 = 1) ∧
        (∀ x : ℤ, D = 4 * x → ¬ 4 ∣ x ∧ ¬ x % 4 = 1) ∧
        ∀ p : ℕ, Nat.Prime p → Odd p → ¬ (p : ℤ) ^ 2 ∣ D := Iff.rfl

/-- The definition, restated with `p ≠ 2` for `Odd p` and the `∀ x` clause as a `¬ ∃ e`. -/
theorem isFundamentalDiscr_iff_forall_prime {D : ℤ} :
    IsFundamentalDiscr D ↔
      (D % 4 = 0 ∨ D % 4 = 1) ∧
        (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ 2 ∣ D) ∧
        ¬ ∃ e : ℤ, D = 4 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  rw [isFundamentalDiscr_def]
  refine and_congr_right fun _ => ⟨fun ⟨hB, hC⟩ =>
      ⟨fun p hp hp2 => hC p hp (hp.odd_of_ne_two hp2), ?_⟩,
    fun ⟨hC', hB'⟩ => ⟨fun x hx => ?_, fun p hp hpo => hC' p hp ?_⟩⟩
  · rintro ⟨e, rfl, he | he⟩
    · exact (hB e rfl).1 (EuclideanDomain.mod_eq_zero.mp he)
    · exact (hB e rfl).2 he
  · exact ⟨fun h4 => hB' ⟨x, hx, Or.inl (EuclideanDomain.mod_eq_zero.mpr h4)⟩,
      fun h1 => hB' ⟨x, hx, Or.inr h1⟩⟩
  · rintro rfl; exact (by decide : ¬ Odd 2) hpo

/-- Concrete squarefree characterization: `D ≡ 1 mod 4` squarefree, or `D = 4m` with `m`
squarefree and `m ≡ 2, 3 mod 4`. -/
theorem isFundamentalDiscr_iff_squarefree {D : ℤ} :
    IsFundamentalDiscr D ↔
      (D % 4 = 1 ∧ Squarefree D) ∨
        (D % 4 = 0 ∧ Squarefree (D / 4) ∧ (D / 4 % 4 = 2 ∨ D / 4 % 4 = 3)) := by
  rw [isFundamentalDiscr_iff_forall_prime]
  refine Iff.symm ?_
  obtain hD | hD := Int.even_or_odd D
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hD
    have h₁ : ¬ 2 * k % 4 = 1 := by lia
    simp only [h₁, false_and, EuclideanDomain.mod_eq_zero, false_or, or_false, ne_eq, not_exists,
      not_and, not_or, and_congr_right_iff]
    rw [show (4 : ℤ) = 2 * 2 by norm_num, Int.mul_dvd_mul_iff_left two_ne_zero]
    rintro ⟨c, rfl⟩
    have h₂ {p : ℕ} {hp : p.Prime} {hp' : ¬p = 2} : ((p : ℤ) ^ 2 ∣ 4 * c ↔ (p : ℤ) ^ 2 ∣ c) := by
      refine ⟨fun h ↦ IsCoprime.dvd_of_dvd_mul_left ?_ h, fun h ↦ h.mul_left 4⟩
      rw [← Nat.cast_pow, show (4 : ℤ) = (2 ^ 2 : ℕ) by norm_num]
      exact (Nat.coprime_pow_primes 2 2 hp (Nat.prime_two) hp').isCoprime
    have h₃ : c % 4 = 2 ∨ c % 4 = 3 ↔ ¬4 ∣ c ∧ ¬c % 4 = 1 := by grind
    simp +contextual only [← mul_assoc, Int.reduceMul, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_div_cancel_left₀, Int.squarefree_iff_forall_prime, h₃, h₂,
      mul_eq_mul_left_iff, forall_eq', and_congr_left_iff, and_imp]
    refine fun hc _ ↦ ⟨by tauto, fun h p hp ↦ ?_⟩
    obtain rfl | hp' := eq_or_ne p 2
    · lia
    · exact h p hp hp'
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hD
    have h₁ : ¬ (2 * k + 1) % 4 = 0 := by lia
    have h₂ {x : ℤ} : ¬ (2 * k + 1) = 4 * x := by lia
    simp only [Int.squarefree_iff_forall_prime, h₁, false_and, or_false, false_or, ne_eq, h₂,
      EuclideanDomain.mod_eq_zero, exists_const, not_false_eq_true, and_true, and_congr_right_iff]
    refine fun _ ↦  ⟨by tauto, fun h p hp ↦ ?_⟩
    obtain rfl | hp' := eq_or_ne p 2
    · lia
    · exact h p hp hp'

end Int
