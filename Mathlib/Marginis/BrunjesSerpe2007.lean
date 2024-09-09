/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Nat.Prime.Defs

/-!

Marginis:
Formal marginalia for
Enlargements of schemes
by
Lars Brünjes and Christian Serpé, JLA 2007.

We prove that by a certain definition,
√2 exists mod 1 and mod 2, but not mod 0, 3, 4, or 5.

-/

/-- The equation 2 = 0 mod p -/
def φ (p:ℕ) := 2 % p = 0 % p

/-- The equation holds mod p for some primes p, but not for all primes p -/
theorem proof_of_concept : ¬ ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → (φ p ↔ φ q) := by
  intro hcontra
  have : φ 2 → φ 3 := (hcontra 2 3 Nat.prime_two Nat.prime_three).mp
  have h3 : φ 3 := this rfl
  have : ¬φ 3 := Nat.ne_of_beq_eq_false rfl
  exact this h3


/-- `x` is a square root mod `p`. -/
def isSqrt2Mod (p x:ℕ) := (x*x) % p = 2 % p

/-- √2 is not a natural number. -/
theorem sqrt2_not_natural (x : ℕ) (h : x * x = 2) : False := by
  by_cases H : x < 2
  have : x = 0 ∨ x = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp <| Nat.le_of_lt_succ H
  cases this <;> simp_all
  have : 2 ≤ x := Nat.le_of_not_lt H
  have : 4 ≤ 2 := calc
    4 = 2 * 2 := rfl
    _ ≤ 2 * x := Nat.mul_le_mul_left 2 this
    _ ≤ x * x := Nat.mul_le_mul_right x this
    _ = 2 := h
  simp at this

/-- There is no √2 mod 0. -/
theorem sqrt_mod0 : ¬ ∃ x :ℕ, isSqrt2Mod 0 x  := by
  push_neg
  intro x h
  unfold isSqrt2Mod at h
  simp_all
  exact sqrt2_not_natural x h


/-- There is a √2 mod 1, namely 0. -/
theorem sqrt_mod1 : ∃ x :ℕ, isSqrt2Mod 1 x  := by exists 0


/-- There is a √2 mod 2, namely 0. -/
theorem sqrt_mod2 : ∃ x :ℕ, isSqrt2Mod 2 x  := by exists 0

/-- There is no √2 mod 3. -/
theorem sqrt_mod3 : ¬ ∃ x :ℕ, isSqrt2Mod 3 x  := by
  intro hcontra
  rcases hcontra with ⟨x,hx⟩
  have : x % 3 < 3 := Nat.mod_lt x (Nat.succ_pos 2)
  have : x % 3 < 2 ∨ x % 3 = 2 := Nat.lt_succ_iff_lt_or_eq.mp this
  rcases this with hl | he
  have : x % 3 < 1 ∨ x % 3 = 1 := Nat.lt_succ_iff_lt_or_eq.mp hl
  rcases this with Hl | He
  have hz : x % 3 = 0 := Nat.lt_one_iff.mp Hl
  have : (x*x) % 3 = 2 % 3 := hx
  have hzt : 0 = 2 := calc
    0 = (0 * 0) % 3:= by rfl
    _ = ((x % 3) * (x % 3)) % 3 := by rw [hz.symm]
    _ = (x*x) % 3 := (Nat.mul_mod x x 3).symm
    _ = 2 % 3 := by rw [this]
  have : ¬ 0 = Nat.succ 1 := Nat.ne_of_beq_eq_false rfl
  exact this hzt

  have hzt : 1 = 2 := calc
    1 = (1 * 1) % 3 := by rfl
    _ = ((x % 3) * (x % 3)) % 3 := by rw [He.symm]
    _ = (x*x) % 3 := (Nat.mul_mod x x 3).symm
    _ = 2 % 3 := hx
  have : ¬ 1 = Nat.succ 1 := Nat.ne_of_beq_eq_false rfl
  exact this hzt

  have hzt : 1 = 2 := calc
    1 = (2 * 2) % 3 := by rfl
    _ = ((x % 3) * (x % 3)) % 3 := by rw [he.symm]
    _ = (x*x) % 3 := (Nat.mul_mod x x 3).symm
    _ = 2 % 3 := hx
  have : ¬ 1 = Nat.succ 1 := Nat.ne_of_beq_eq_false rfl
  exact this hzt


/-- There is no √2 mod 4. -/
theorem sqrt_mod4 : ¬ ∃ x :ℕ, isSqrt2Mod 4 x  := by
  push_neg
  unfold isSqrt2Mod
  intro x
  have : (x * x) % 4 = ((x % 4) * (x % 4)) % 4 := Nat.mul_mod x x 4
  rw [this]
  have : x % 4 < 4 := Nat.mod_lt x <| Nat.zero_lt_succ 3
  have : x % 4 < 3 ∨ x % 4 = 3 := Nat.lt_succ_iff_lt_or_eq.mp this
  cases this with
  | inl h =>
    have : x % 4 < 2 ∨ x % 4 = 2 := Nat.lt_succ_iff_lt_or_eq.mp h
    cases this with
    | inl h =>
      have : x % 4 = 0 ∨ x % 4 = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ h)
      cases this <;> simp_all
    | inr h =>rw [h];simp
  | inr h => rw [h];simp



/-- There is no √2 mod 5. -/
theorem sqrt_mod5 : ¬ ∃ x :ℕ, isSqrt2Mod 5 x  := by
  push_neg
  unfold isSqrt2Mod
  intro x
  have : (x * x) % 5 = ((x % 5) * (x % 5)) % 5 := Nat.mul_mod x x 5
  rw [this]
  have : x % 5 < 5 := Nat.mod_lt x <| Nat.zero_lt_succ 4
  have : x % 5 < 4 ∨ x % 5 = 4 := Nat.lt_succ_iff_lt_or_eq.mp this
  cases this with
  | inl h =>
    have : x % 5 < 3 ∨ x % 5 = 3 := Nat.lt_succ_iff_lt_or_eq.mp h
    cases this with
    | inl h =>
      have : x % 5 < 2 ∨ x % 5 = 2 := Nat.lt_succ_iff_lt_or_eq.mp h
      cases this with
      | inl h =>
        have : x % 5 = 0 ∨ x % 5 = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ h)
        cases this <;> simp_all
      | inr h =>rw [h];simp
    | inr h =>rw [h];simp
  | inr h => rw [h];simp
