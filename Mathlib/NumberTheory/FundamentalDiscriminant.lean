/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.Nat.Squarefree

/-!
# Fundamental discriminants

A fundamental discriminant is an integer `D ≡ 0, 1 mod 4` that is primitive, i.e. not a proper
square multiple of a smaller discriminant. These are exactly the discriminants of quadratic fields.

The definition and the results below are elementary arithmetic on `ℤ`, so this file is kept
independent of the theory of quadratic fields.

## Main definitions

* `Int.IsFundamentalDiscr`: `D` is a fundamental discriminant.

## Main results

* `Int.isFundamentalDiscr_iff_squarefree`: the concrete squarefree characterization, `D ≡ 1 mod 4`
  squarefree or `D = 4m` with `m` squarefree and `m ≡ 2, 3 mod 4`.
* `Int.isFundamentalDiscr_four_mul_add_one`: `4m + 1` is a fundamental discriminant if and only if
  it is squarefree.
* `Int.isFundamentalDiscr_four_mul`: `4m` is a fundamental discriminant if and only if `m` is
  squarefree and `m ≡ 2, 3 mod 4`.
* `Int.isFundamentalDiscr_iff_forall_prime`: the characterization uniform in the prime `p`, where
  the clause singling out `p = 2` in the definition disappears.
-/

@[expose] public section

namespace Int

/-- `D` is a fundamental discriminant: it is a discriminant (`D ≡ 0, 1 mod 4`) and primitive,
i.e. `D / 4 ≢ 0, 1 mod 4` when `4 ∣ D`, and no odd prime square divides `D`. -/
def IsFundamentalDiscr (D : ℤ) : Prop :=
  (D % 4 = 0 ∨ D % 4 = 1) ∧ (∀ x, D = 4 * x → ¬ 4 ∣ x ∧ x % 4 ≠ 1) ∧
    ∀ p : ℕ, p.Prime → Odd p → ¬ (p : ℤ) ^ 2 ∣ D

variable {D : ℤ}

theorem isFundamentalDiscr_def :
    IsFundamentalDiscr D ↔
      (D % 4 = 0 ∨ D % 4 = 1) ∧ (∀ x, D = 4 * x → ¬ 4 ∣ x ∧ x % 4 ≠ 1) ∧
        ∀ p : ℕ, p.Prime → Odd p → ¬ (p : ℤ) ^ 2 ∣ D := Iff.rfl

theorem IsFundamentalDiscr.ne_zero (h : IsFundamentalDiscr D) : D ≠ 0 := by
  grind [isFundamentalDiscr_def]

theorem IsFundamentalDiscr.emod_four_eq_zero_or_one (h : IsFundamentalDiscr D) :
    D % 4 = 0 ∨ D % 4 = 1 := h.1

/-- `D` is a fundamental discriminant if and only if either `D ≡ 1 mod 4` and `D` is squarefree,
or `D = 4 * d` with `d` squarefree and `d ≡ 2, 3 mod 4`. -/
theorem isFundamentalDiscr_iff_squarefree :
    IsFundamentalDiscr D ↔
      (D % 4 = 1 ∧ Squarefree D) ∨
        (D % 4 = 0 ∧ Squarefree (D / 4) ∧ (D / 4 % 4 = 2 ∨ D / 4 % 4 = 3)) := by
  -- The two `have`s below are picked up from the context by the `grind` calls at the end.
  have {m} : Squarefree m ↔ ¬ 4 ∣ m ∧ ∀ p : ℕ, p.Prime → Odd p → ¬ (p : ℤ) ^ 2 ∣ m := by
    rw [squarefree_iff_prime_sq_not_dvd, Nat.forall_prime_iff_two_and_odd]
    simp
  have {m p : ℤ} (hp : Odd p) : p ^ 2 ∣ 4 * m ↔ p ^ 2 ∣ m := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact (IsCoprime.pow hp.isCoprime_two).dvd_mul_left_iff
  by_cases h : 4 ∣ D
  · obtain ⟨d, rfl⟩ := h
    simp +contextual only [Int.mul_ediv_cancel_left d four_ne_zero]
    grind [isFundamentalDiscr_def]
  · grind [isFundamentalDiscr_def]

/-- Prime-by-prime characterisation of fundamental discriminants, uniform in `p`. Unlike the
definition, which singles out `p = 2`, the second clause is the same for every prime. -/
theorem isFundamentalDiscr_iff_forall_prime :
    IsFundamentalDiscr D ↔ (D % 4 = 0 ∨ D % 4 = 1) ∧
      ∀ p : ℕ, p.Prime → ¬ ∃ e : ℤ, D = (p : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  rw [Nat.forall_prime_iff_two_and_odd, isFundamentalDiscr_def]
  simp only [Int.dvd_iff_emod_eq_zero, not_exists, ne_eq, Nat.cast_ofNat, reducePow,
    not_and, not_or, and_congr_right_iff]
  refine fun h₁ _ ↦ forall_congr' fun p ↦ imp_congr_right fun _ ↦ imp_congr_right fun hp ↦ ?_
  rw [← Int.dvd_iff_emod_eq_zero, dvd_def, not_exists]
  refine forall_congr' fun x ↦ imp_congr_right fun hD ↦ (iff_false_left not_false).mpr ?_
  rw [hD, Int.mul_emod, Int.sq_emod_four, Int.odd_iff.mp hp.natCast, one_mul, Int.emod_emod] at h₁
  rwa [not_and_or, not_not, not_not]

theorem isFundamentalDiscr_four_mul_add_one {m : ℤ} :
    IsFundamentalDiscr (4 * m + 1) ↔ Squarefree (4 * m + 1) := by
  simp [isFundamentalDiscr_iff_squarefree]

theorem isFundamentalDiscr_four_mul {m : ℤ} :
    IsFundamentalDiscr (4 * m) ↔ Squarefree m ∧ (m % 4 = 2 ∨ m % 4 = 3) := by
  simp [isFundamentalDiscr_iff_squarefree]

end Int
