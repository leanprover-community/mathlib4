/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Clark Eggerman
-/
import Mathlib.Data.Nat.Prime.Defs

/-!

Marginis:
Formal marginalia for
Enlargements of schemes
by
Lars Brünjes and Christian Serpé, JLA 2007.

-/

/- The equation 2 = 0 mod p -/
def φ (p:ℕ) := 2 % p = 0 % p

/- The equation holds mod p for some primes p, but not for all primes p -/
theorem proof_of_concept : ¬ ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → (φ p ↔ φ q) := by
  intro hcontra
  have : φ 2 → φ 3 := (hcontra 2 3 Nat.prime_two Nat.prime_three).mp
  have h3 : φ 3 := this rfl
  have : ¬φ 3 := Nat.ne_of_beq_eq_false rfl
  exact this h3


/- Now we consider the existence of a square root of two.
We show it exists for p=2 but not for p=3.
-/
def isSqrtMod (p x:ℕ) := (x*x) % p = 2 % p

theorem sqrt_mod2 : ∃ x :ℕ, isSqrtMod 2 x  := by exists 0

theorem sqrt_mod3 : ¬ ∃ x :ℕ, isSqrtMod 3 x  := by
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
