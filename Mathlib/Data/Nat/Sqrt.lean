/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Basic
import Batteries.Data.Nat.Basic

/-!
# Properties of the natural number square root function.
-/

namespace Nat

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

variable {m n a : ℕ}

/-!
### `sqrt`

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/

private lemma iter_fp_bound (n k : ℕ) :
    let iter_next (n guess : ℕ) := (guess + n / guess) / 2;
    sqrt.iter n k ≤ iter_next n (sqrt.iter n k) := by
  intro iter_next
  unfold sqrt.iter
  if h : (k + n / k) / 2 < k then
    simpa [if_pos h] using iter_fp_bound _ _
  else
    grind

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

-- These two lemmas seem like they belong to `Batteries.Data.Nat.Basic`.

lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [next, dif_pos h] using sqrt.iter_sq_le n next
  else
    apply Nat.mul_le_of_le_div
    grind

lemma sqrt.lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- m was `next`
  let m := (guess + n / guess) / 2
  dsimp
  split_ifs with h
  · suffices n < (m + 1) * (m + 1) by
      simpa only [dif_pos h] using sqrt.lt_iter_succ_sq n m this
    refine Nat.lt_of_mul_lt_mul_left ?_ (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_lemma {a : ℕ} : a ≤ 2 * ((a + 1) / 2) := by omega
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_lemma)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left (lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le m) h)) _
  · exact hn

private def IsSqrt (n q : ℕ) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)

/-
Sketch of proof:
Up to rounding, in terms of the definition of `sqrt.iter`,

* By AM-GM inequality, `next² ≥ n` giving one of the bounds.
* When we terminated, we have `guess ≥ next` from which we deduce the other bound `n ≥ next²`.

To turn this into a lean proof we need to manipulate, use properties of natural number division etc.
-/
private lemma sqrt_isSqrt (n : ℕ) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp [IsSqrt, sqrt]
  | 1 => simp [IsSqrt, sqrt]
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le _ _, sqrt.lt_iter_succ_sq _ _ ?_⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
    rw [Nat.lt_add_one_iff, Nat.add_assoc, ← Nat.mul_two]
    refine le_trans (Nat.le_of_eq (div_add_mod' (n + 2) 2).symm) ?_
    rw [show (n + 2) / 2 * 2 + (n + 2) % 2 = n + 2 by grind]
    simp only [shiftLeft_eq, Nat.one_mul]
    refine Nat.le_of_lt (Nat.le_trans lt_log2_self (le_add_right_of_le ?_))
    rw [← Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide)
    grind

lemma sqrt_le (n : ℕ) : sqrt n * sqrt n ≤ n := (sqrt_isSqrt n).left

lemma sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n := by simpa [Nat.pow_two] using sqrt_le n

lemma lt_succ_sqrt (n : ℕ) : n < succ (sqrt n) * succ (sqrt n) := (sqrt_isSqrt n).right

lemma lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n

lemma sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

lemma le_sqrt : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩

lemma le_sqrt' : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [Nat.pow_two] using le_sqrt

lemma sqrt_lt : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt]

lemma sqrt_lt' : sqrt m < n ↔ m < n ^ 2 := by simp only [← not_le, le_sqrt']

lemma sqrt_le_self (n : ℕ) : sqrt n ≤ n := le_trans (le_mul_self _) (sqrt_le n)

@[gcongr]
lemma sqrt_le_sqrt (h : m ≤ n) : sqrt m ≤ sqrt n := le_sqrt.2 (le_trans (sqrt_le _) h)

@[simp, grind =] lemma sqrt_zero : sqrt 0 = 0 := rfl

@[simp, grind =] lemma sqrt_one : sqrt 1 = 1 := rfl

lemma sqrt_eq_zero : sqrt n = 0 ↔ n = 0 :=
  ⟨fun h ↦ have := @sqrt_lt n 1; by grind, by grind⟩

lemma eq_sqrt : a = sqrt n ↔ a * a ≤ n ∧ n < (a + 1) * (a + 1) :=
  ⟨fun e ↦ e.symm ▸ sqrt_isSqrt n,
   fun ⟨h₁, h₂⟩ ↦ le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩

lemma eq_sqrt' : a = sqrt n ↔ a ^ 2 ≤ n ∧ n < (a + 1) ^ 2 := by
  simpa only [Nat.pow_two] using eq_sqrt

lemma le_three_of_sqrt_eq_one (h : sqrt n = 1) : n ≤ 3 :=
  le_of_lt_succ <| (@sqrt_lt n 2).1 <| by grind

lemma sqrt_lt_self (h : 1 < n) : sqrt n < n :=
  sqrt_lt.2 <| by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); grind

@[grind =]
lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
  le_sqrt

lemma sqrt_add_eq (n : ℕ) (h : a ≤ n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <| sqrt_lt.2 <| by grind)
    (le_sqrt.2 <| by grind)

lemma sqrt_add_eq' (n : ℕ) (h : a ≤ n + n) : sqrt (n ^ 2 + a) = n := by
  simpa [Nat.pow_two] using sqrt_add_eq n h

@[simp]
lemma sqrt_eq (n : ℕ) : sqrt (n * n) = n := sqrt_add_eq n (zero_le _)

@[simp]
lemma sqrt_eq' (n : ℕ) : sqrt (n ^ 2) = n := sqrt_add_eq' n (zero_le _)

lemma sqrt_succ_le_succ_sqrt (n : ℕ) : sqrt n.succ ≤ n.sqrt.succ :=
  le_of_lt_succ <| sqrt_lt.2 <| (have := sqrt_le_add n; by grind)

@[simp]
lemma log2_two : (2 : ℕ).log2 = 1 := rfl

@[simp]
lemma sqrt_two : sqrt 2 = 1 := by simp [sqrt, sqrt.iter]

lemma add_one_sqrt_le_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (n + 1).sqrt ≤ n :=
  le_induction (by simp) (fun n _ ih ↦ le_trans n.succ.sqrt_succ_le_succ_sqrt (succ_le_succ ih)) n
    (Nat.pos_of_ne_zero hn)

lemma exists_mul_self (x : ℕ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ ↦ by rw [← hn, sqrt_eq], fun h ↦ ⟨sqrt x, h⟩⟩

lemma exists_mul_self' (x : ℕ) : (∃ n, n ^ 2 = x) ↔ sqrt x ^ 2 = x := by
  simpa only [Nat.pow_two] using exists_mul_self x

lemma sqrt_mul_sqrt_lt_succ (n : ℕ) : sqrt n * sqrt n < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le _)

lemma sqrt_mul_sqrt_lt_succ' (n : ℕ) : sqrt n ^ 2 < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le' _)

lemma succ_le_succ_sqrt (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt _)

lemma succ_le_succ_sqrt' (n : ℕ) : n + 1 ≤ (sqrt n + 1) ^ 2 :=
  le_of_pred_lt (lt_succ_sqrt' _)

/-- There are no perfect squares strictly between m² and (m+1)² -/
lemma not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ t, t * t = n := by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.1 hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.1 hr
  grind

lemma not_exists_sq' : m ^ 2 < n → n < (m + 1) ^ 2 → ¬∃ t, t ^ 2 = n := by
  simpa only [Nat.pow_two] using not_exists_sq

lemma le_sqrt_of_eq_mul {a b c : ℕ} (h : a = b * c) : b ≤ a.sqrt ∨ c ≤ a.sqrt := by
  rcases le_total b c with bc | cb
  · exact Or.inl <| le_sqrt.mpr <| h ▸ mul_le_mul_left b bc
  · exact Or.inr <| le_sqrt.mpr <| h ▸ mul_le_mul_right c cb

end Nat
