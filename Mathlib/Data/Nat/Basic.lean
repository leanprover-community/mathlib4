/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Tactic.GCongr.Core

/-!
# Basic operations on the natural numbers

This file builds on `Mathlib/Data/Nat/Init.lean` by adding basic lemmas on natural numbers
depending on Mathlib definitions.

See note [foundational algebra order theory].
-/

public section

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d m n k : ℕ} {p : ℕ → Prop}

-- TODO: Move the `LinearOrder ℕ` instance to `Order.Nat` (https://github.com/leanprover-community/mathlib4/pull/13092).
instance instLinearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_ge := @Nat.lt_iff_le_and_not_ge

-- Shortcut instances
instance : Preorder ℕ := inferInstance
instance : PartialOrder ℕ := inferInstance

instance instNontrivial : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

attribute [gcongr] Nat.succ_le_succ Nat.div_le_div_right Nat.div_le_div

/-! ### `succ`, `pred` -/

lemma succ_injective : Injective Nat.succ := @succ.inj

/-! ### `div` -/

protected theorem div_right_comm (a b c : ℕ) : a / b / c = a / c / b := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/-!
### `pow`
-/

lemma pow_left_injective (hn : n ≠ 0) : Injective (fun a : ℕ ↦ a ^ n) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

protected lemma pow_right_injective (ha : 2 ≤ a) : Injective (a ^ ·) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

protected theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) :
    x ^ (a - 1) = x ^ a / x := by
  rw [← Nat.pow_div (one_le_iff_ne_zero.mpr ha) (Nat.pos_iff_ne_zero.mpr hx), Nat.pow_one]

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

lemma leRecOn_injective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
    exact ih (Hnext _ H)

lemma leRecOn_surjective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]


/-- A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n ≥ k`. -/
lemma set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk

/-- A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`. -/
lemma set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)

/-! ### `mod`, `dvd` -/

/-- `dvd` is injective in the left argument -/
lemma dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

@[simp]
protected lemma dvd_sub_self_left {n m : ℕ} :
    n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  rcases le_or_gt n m with h | h
  · simp [h]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [hm, h.not_ge, or_self, iff_false]
      refine not_dvd_of_pos_of_lt ?_ ?_ <;>
      grind

@[simp]
protected lemma dvd_sub_self_right {n m : ℕ} :
    n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  rcases le_or_gt m n with h | h
  · simp [h]
  · simp [dvd_sub_iff_left (le_of_lt h) (Nat.dvd_refl _), h.not_ge]

/-! ### Miscellaneous -/

lemma mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) :
    a * b ≤ a ^ b := by
  cases b with
  | zero => exact Nat.zero_le _
  | succ b =>
      obtain rfl | ha0 : a = 0 ∨ a > 0 := a.eq_zero_or_pos
      · rw [Nat.zero_mul]; exact Nat.zero_le _
      · have ha1 : a > 1 := Nat.lt_of_le_of_ne ha0 ha.symm
        rw [Nat.pow_succ']; exact Nat.mul_le_mul_left a (Nat.lt_pow_self ha1)

lemma two_mul_sq_add_one_le_two_pow_two_mul (k : ℕ) : 2 * k ^ 2 + 1 ≤ 2 ^ (2 * k) := by
  obtain rfl | hk : k = 0 ∨ k > 0 := k.eq_zero_or_pos
  · decide
  · have hk0 : 0 < 2 * k ^ 2 := Nat.mul_pos Nat.two_pos (Nat.pow_pos hk)
    calc 2 * k ^ 2
      _ < 2 * k ^ 2 + 2 * k ^ 2 := Nat.lt_add_of_pos_left hk0
      _ = (2 * k) ^ 2 := by rw [Nat.mul_pow, ← Nat.add_mul]
      _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_pow (by decide : 2 ≠ 1) _) 2
      _ = 2 ^ (2 * k) := (Nat.pow_mul' _ _ _).symm

end Nat
