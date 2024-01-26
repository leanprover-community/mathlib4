/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.GroupPower.Order

#align_import data.nat.pow from "leanprover-community/mathlib"@"3e00d81bdcbf77c8188bbd18f5524ddc3ed8cac6"

/-! # `Nat.pow`

Results on the power operation on natural numbers.
-/


namespace Nat
variable {m n x y : ℕ}

/-! ### `pow` -/

-- Porting note: the next two lemmas have moved into `Std`.
-- TODO: Rename `Nat.pow_le_pow_of_le_left` to `Nat.pow_le_pow_left`, protect it, remove the alias
-- TODO: Rename `Nat.pow_le_pow_of_le_right` to `Nat.pow_le_pow_right`, protect it, remove the alias

-- The global `pow_le_pow_left` needs an extra hypothesis `0 ≤ x`.

protected alias pow_le_pow_left := pow_le_pow_of_le_left
protected alias pow_le_pow_right := pow_le_pow_of_le_right
#align nat.pow_le_pow_of_le_left Nat.pow_le_pow_left
#align nat.pow_le_pow_of_le_right Nat.pow_le_pow_right

protected theorem pow_lt_pow_left (h : x < y) (hn : n ≠ 0) : x ^ n < y ^ n :=
  pow_lt_pow_left h (zero_le _) hn
#align nat.pow_lt_pow_of_lt_left Nat.pow_lt_pow_left

#align nat.pow_lt_pow_of_lt_right pow_lt_pow_right

theorem pow_lt_pow_succ {p : ℕ} (h : 1 < p) (n : ℕ) : p ^ n < p ^ (n + 1) :=
  pow_lt_pow_right h n.lt_succ_self
#align nat.pow_lt_pow_succ Nat.pow_lt_pow_succ

theorem le_self_pow {n : ℕ} (hn : n ≠ 0) : ∀ m : ℕ, m ≤ m ^ n
  | 0 => zero_le _
  | (_ + 1) => _root_.le_self_pow (le_add_left _ _) hn
#align nat.le_self_pow Nat.le_self_pow

theorem lt_pow_self {p : ℕ} (h : 1 < p) : ∀ n : ℕ, n < p ^ n
  | 0 => by simp [zero_lt_one]
  | n + 1 =>
    calc
      n + 1 < p ^ n + 1 := Nat.add_lt_add_right (lt_pow_self h _) _
      _ ≤ p ^ (n + 1) := pow_lt_pow_succ h _
#align nat.lt_pow_self Nat.lt_pow_self

theorem lt_two_pow (n : ℕ) : n < 2 ^ n :=
  lt_pow_self (by decide) n
#align nat.lt_two_pow Nat.lt_two_pow

theorem one_le_pow (n m : ℕ) (h : 0 < m) : 1 ≤ m ^ n := by
  rw [← one_pow n]
  exact Nat.pow_le_pow_of_le_left h n
#align nat.one_le_pow Nat.one_le_pow

theorem one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n :=
  one_le_pow n (m + 1) (succ_pos m)
#align nat.one_le_pow' Nat.one_le_pow'

theorem one_le_two_pow (n : ℕ) : 1 ≤ 2 ^ n :=
  one_le_pow n 2 (by decide)
#align nat.one_le_two_pow Nat.one_le_two_pow

theorem one_lt_pow (n m : ℕ) (h₀ : n ≠ 0) (h₁ : 1 < m) : 1 < m ^ n := by
  rw [← one_pow n]
  exact Nat.pow_lt_pow_left h₁ h₀
#align nat.one_lt_pow Nat.one_lt_pow

theorem two_pow_pos (n : ℕ) : 0 < 2^n := Nat.pos_pow_of_pos _ (by decide)

theorem two_pow_succ (n : ℕ) : 2^(n + 1) = 2^n + 2^n := by simp [pow_succ, mul_two]

theorem one_lt_pow' (n m : ℕ) : 1 < (m + 2) ^ (n + 1) :=
  one_lt_pow (n + 1) (m + 2) n.succ_ne_zero (Nat.lt_of_sub_eq_succ rfl)
#align nat.one_lt_pow' Nat.one_lt_pow'

@[simp]
theorem one_lt_pow_iff {k n : ℕ} (h : k ≠ 0) : 1 < n ^ k ↔ 1 < n :=
  one_lt_pow_iff_of_nonneg (zero_le _) h
#align nat.one_lt_pow_iff Nat.one_lt_pow_iff

theorem one_lt_two_pow (n : ℕ) (h₀ : n ≠ 0) : 1 < 2 ^ n := one_lt_pow n 2 h₀ (by decide)
#align nat.one_lt_two_pow Nat.one_lt_two_pow

theorem one_lt_two_pow' (n : ℕ) : 1 < 2 ^ (n + 1) :=
  one_lt_pow (n + 1) 2 n.succ_ne_zero (by decide)
#align nat.one_lt_two_pow' Nat.one_lt_two_pow'

#align nat.pow_right_strict_mono pow_right_strictMono
#align nat.pow_le_iff_lt_right pow_le_pow_iff_right
#align nat.pow_lt_iff_lt_right pow_lt_pow_iff_right

protected lemma pow_right_injective (hx : 2 ≤ x) : Function.Injective (x ^ ·) :=
  StrictMono.injective (pow_right_strictMono hx)
#align nat.pow_right_injective Nat.pow_right_injective

/-- See also `pow_left_strictMonoOn`. -/
protected theorem pow_left_strictMono (hn : n ≠ 0) : StrictMono (. ^ n : ℕ → ℕ) :=
  fun _ _ h ↦ Nat.pow_lt_pow_left h hn
#align nat.pow_left_strict_mono Nat.pow_left_strictMono

theorem mul_lt_mul_pow_succ {n a q : ℕ} (a0 : 0 < a) (q1 : 1 < q) : n * q < a * q ^ (n + 1) := by
  rw [pow_succ, ← mul_assoc, mul_lt_mul_right (zero_lt_one.trans q1)]
  exact lt_mul_of_one_le_of_lt (Nat.succ_le_iff.mpr a0) (Nat.lt_pow_self q1 n)
#align nat.mul_lt_mul_pow_succ Nat.mul_lt_mul_pow_succ

theorem _root_.StrictMono.nat_pow {n : ℕ} (hn : n ≠ 0) {f : ℕ → ℕ} (hf : StrictMono f) :
    StrictMono fun m => f m ^ n :=
  (Nat.pow_left_strictMono hn).comp hf
#align strict_mono.nat_pow StrictMono.nat_pow

protected theorem pow_le_pow_iff_left (hm : m ≠ 0) : x ^ m ≤ y ^ m ↔ x ≤ y :=
  pow_le_pow_iff_left (zero_le _) (zero_le _) hm
#align nat.pow_le_iff_le_left Nat.pow_le_pow_iff_left

protected theorem pow_lt_pow_iff_left (hm : m ≠ 0) : x ^ m < y ^ m ↔ x < y :=
  pow_lt_pow_iff_left (zero_le _) (zero_le _) hm
#align nat.pow_lt_iff_lt_left Nat.pow_lt_pow_iff_left

theorem pow_left_injective (hm : m ≠ 0) : Function.Injective fun x : ℕ => x ^ m :=
  (Nat.pow_left_strictMono hm).injective
#align nat.pow_left_injective Nat.pow_left_injective

theorem sq_sub_sq (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq]
  exact Nat.mul_self_sub_mul_self_eq a b
#align nat.sq_sub_sq Nat.sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq
#align nat.pow_two_sub_pow_two Nat.pow_two_sub_pow_two

lemma pow_eq_one_iff {m n : ℕ} : m ^ n = 1 ↔ m = 1 ∨ n = 0 := by
  refine ⟨fun H ↦ (eq_or_ne n 0).elim Or.inr fun h ↦ Or.inl ?_, fun H ↦ ?_⟩
  · rcases m.eq_zero_or_pos with rfl | hm
    · simp [h] at H
    by_contra! hm'
    exact (H ▸ (one_lt_pow_iff h).mpr <| lt_of_le_of_ne hm hm'.symm).false
  · rcases H with rfl | rfl <;> simp

/-! ### `pow` and `mod` / `dvd` -/


theorem pow_mod (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n := by
  induction' b with b ih
  rfl; simp [pow_succ, Nat.mul_mod, ih]
#align nat.pow_mod Nat.pow_mod

theorem mod_pow_succ {b : ℕ} (w m : ℕ) : m % b ^ succ w = b * (m / b % b ^ w) + m % b := by
  by_cases b_h : b = 0
  · simp [b_h, pow_succ]
  have b_pos := Nat.pos_of_ne_zero b_h
  induction m using Nat.strong_induction_on with
    | h p IH =>
      cases' lt_or_ge p (b ^ succ w) with h₁ h₁
      · -- base case: p < b^succ w
        have h₂ : p / b < b ^ w := by
          rw [div_lt_iff_lt_mul b_pos]
          simpa [pow_succ] using h₁
        rw [mod_eq_of_lt h₁, mod_eq_of_lt h₂]
        simp [div_add_mod]
      · -- step: p ≥ b^succ w
        -- Generate condition for induction hypothesis
        have h₂ : p - b ^ succ w < p :=
          tsub_lt_self ((pow_pos b_pos _).trans_le h₁) (pow_pos b_pos _)
        -- Apply induction
        rw [mod_eq_sub_mod h₁, IH _ h₂]
        -- Normalize goal and h1
        simp only [pow_succ']
        simp only [GE.ge, pow_succ'] at h₁
        -- Pull subtraction outside mod and div
        rw [sub_mul_mod h₁, sub_mul_div _ _ _ h₁]
        -- Cancel subtraction inside mod b^w
        have p_b_ge : b ^ w ≤ p / b := by
          rw [le_div_iff_mul_le b_pos, mul_comm]
          exact h₁
        rw [Eq.symm (mod_eq_sub_mod p_b_ge)]
#align nat.mod_pow_succ Nat.mod_pow_succ

theorem pow_dvd_pow_iff_pow_le_pow {k l : ℕ} : ∀ {x : ℕ}, 0 < x → (x ^ k ∣ x ^ l ↔ x ^ k ≤ x ^ l)
  | x + 1, w => by
    constructor
    · intro a
      exact le_of_dvd (pow_pos (succ_pos x) l) a
    · intro a
      cases' x with x
      · simp
      · have le := (pow_le_pow_iff_right <| by simp).mp a
        use (x + 2) ^ (l - k)
        rw [← pow_add, add_comm k, tsub_add_cancel_of_le le]
#align nat.pow_dvd_pow_iff_pow_le_pow Nat.pow_dvd_pow_iff_pow_le_pow

/-- If `1 < x`, then `x^k` divides `x^l` if and only if `k` is at most `l`. -/
theorem pow_dvd_pow_iff_le_right {x k l : ℕ} (w : 1 < x) : x ^ k ∣ x ^ l ↔ k ≤ l := by
  rw [pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w), pow_le_pow_iff_right w]
#align nat.pow_dvd_pow_iff_le_right Nat.pow_dvd_pow_iff_le_right

theorem pow_dvd_pow_iff_le_right' {b k l : ℕ} : (b + 2) ^ k ∣ (b + 2) ^ l ↔ k ≤ l :=
  pow_dvd_pow_iff_le_right (Nat.lt_of_sub_eq_succ rfl)
#align nat.pow_dvd_pow_iff_le_right' Nat.pow_dvd_pow_iff_le_right'

theorem not_pos_pow_dvd : ∀ {p k : ℕ} (_ : 1 < p) (_ : 1 < k), ¬p ^ k ∣ p
  | succ p, succ k, hp, hk, h =>
    have : succ p * succ p ^ k ∣ succ p * 1 := by simpa [pow_succ'] using h
    have : succ p ^ k ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (succ_pos _) this
    have he : succ p ^ k = 1 := eq_one_of_dvd_one this
    have : k < succ p ^ k := lt_pow_self hp k
    have : k < 1 := by rwa [he] at this
    have : k = 0 := Nat.eq_zero_of_le_zero <| le_of_lt_succ this
    have : 1 < 1 := by rwa [this] at hk
    absurd this (by decide)
#align nat.not_pos_pow_dvd Nat.not_pos_pow_dvd

theorem pow_dvd_of_le_of_pow_dvd {p m n k : ℕ} (hmn : m ≤ n) (hdiv : p ^ n ∣ k) : p ^ m ∣ k :=
  (pow_dvd_pow _ hmn).trans hdiv
#align nat.pow_dvd_of_le_of_pow_dvd Nat.pow_dvd_of_le_of_pow_dvd

theorem dvd_of_pow_dvd {p k m : ℕ} (hk : 1 ≤ k) (hpk : p ^ k ∣ m) : p ∣ m := by
  rw [← pow_one p]; exact pow_dvd_of_le_of_pow_dvd hk hpk
#align nat.dvd_of_pow_dvd Nat.dvd_of_pow_dvd

theorem pow_div {x m n : ℕ} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) := by
  rw [Nat.div_eq_iff_eq_mul_left (pow_pos hx n) (pow_dvd_pow _ h), pow_sub_mul_pow _ h]
#align nat.pow_div Nat.pow_div

theorem lt_of_pow_dvd_right {p i n : ℕ} (hn : n ≠ 0) (hp : 2 ≤ p) (h : p ^ i ∣ n) : i < n := by
  rw [← pow_lt_pow_iff_right (succ_le_iff.1 hp)]
  exact lt_of_le_of_lt (le_of_dvd hn.bot_lt h) (lt_pow_self (succ_le_iff.mp hp) n)
#align nat.lt_of_pow_dvd_right Nat.lt_of_pow_dvd_right

end Nat

/-!
### Deprecated lemmas

Those lemmas have been deprecated on 2023-12-23.
-/

@[deprecated] alias Nat.pow_lt_pow_of_lt_left := Nat.pow_lt_pow_left
@[deprecated] alias Nat.pow_le_iff_le_left := Nat.pow_le_pow_iff_left
@[deprecated] alias Nat.pow_lt_pow_of_lt_right := pow_lt_pow_right
@[deprecated] protected alias Nat.pow_right_strictMono := pow_right_strictMono
@[deprecated] alias Nat.pow_le_iff_le_right := pow_le_pow_iff_right
@[deprecated] alias Nat.pow_lt_iff_lt_right := pow_lt_pow_iff_right
