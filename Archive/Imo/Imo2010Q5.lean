/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Data.Fintype.Basic

/-!
# IMO 2010 Q5

Each of the six boxes $B_1, B_2, B_3, B_4, B_5, B_6$ initially contains one coin.
The following two types of operations are allowed:

1. Choose a non-empty box $B_j, 1 ≤ j ≤ 5$, remove one coin from $B_j$ and
add two coins to $B_{j+1}$;
2. Choose a non-empty box $B_k, 1 ≤ k ≤ 4$, remove one coin from $B_k$ and swap
the contents (possibly empty) of the boxes $B_{k+1}$ and $B_{k+2}$.

Determine if there exists a finite sequence of operations of the allowed types, such
that the five boxes $B_1, B_2, B_3, B_4, B_5$ become empty, while box $B_6$ contains exactly
$2010^{2010^{2010}}$ coins.

# Solution

We follow the solution from https://web.evanchen.cc/exams/IMO-2010-notes.pdf.

From the initial state we can reach `(0, 0, 5, 11, 0, 0)`; we now ignore the first two boxes.
On any three adjacent boxes reading `(n, 0, 0)` with `n > 0` we can change them to `(0, 2^n, 0)`:
```
(n, 0, 0) →(move 1) (n-1, 2, 0)
          →(2× move 1) (n-1, 0, 4) →(move 2) (n-2, 4, 0)
          →(4× move 1) (n-2, 0, 8) →(move 2) (n-3, 8, 0)
          → ...
          →(2^(n-1)× move 1) (1, 0, 2^n) →(move 2) (0, 2^n, 0)
```
Thus we can get more than enough coins, all in box 4, as follows:
```
(5, 11, 0, 0) → (5, 0, 2^11, 0) →(move 2) (4, 2^11, 0, 0)
              → (4, 0, 2^2^11, 0) →(move 2) (3, 2^2^11, 0, 0)
              → ...
              → (1, 0, 2^2^2^2^2^11, 0) →(move 2) (0, 2^2^2^2^2^11, 0, 0)
```
We now ignore the third box. Let `T = 2010^2010^2010` be the target number of coins;
since `T < 2^2^2^2^2^11` and `T` is divisible by 4 we can drop coins from box 4 by using move 2
to swap the empty boxes 5 and 6 until we have `(T/4, 0, 0)`. Then we can repeatedly use move 1
to get `(0, T/2, 0)` and finally `(0, 0, T)`.
-/

open Pi Equiv Function

namespace Imo2010Q5

/-- The predicate defining states of boxes reachable by the given moves. -/
inductive Reachable : (Fin 6 → ℕ) → Prop
  /-- The starting position with one coin in each box -/
  | base : Reachable 1
  /-- Remove a coin from $B_j$ and add two coins to $B_{j+1}$ -/
  | move1 {B i} (rB : Reachable B) (hi : i < 5) (pB : 0 < B i) :
      Reachable (B - single i 1 + single (i + 1) 2)
  /-- Remove a coin from $B_k$ and swap $B_{k+1}$ and $B_{k+2}$ -/
  | move2 {B i} (rB : Reachable B) (hi : i < 4) (pB : 0 < B i) :
      Reachable (B ∘ swap (i + 1) (i + 2) - single i 1)

lemma single_succ {k : ℕ} {i : Fin 6} : (single (i + 1) k : Fin 6 → ℕ) i = 0 := by simp

lemma single_succ' {k : ℕ} {i : Fin 6} : (single i k : Fin 6 → ℕ) (i + 1) = 0 := by simp

lemma single_add_two {k : ℕ} {i : Fin 6} : (single (i + 2) k : Fin 6 → ℕ) i = 0 := by simp

namespace Reachable

/-- Empty $B_i$ and add twice its coins to $B_{i+1}$ by repeatedly applying move 1. -/
lemma push {B : Fin 6 → ℕ} {i : Fin 6} (rB : Reachable B) (hi : i < 5) :
    Reachable (B - single i (B i) + single (i + 1) (2 * B i)) := by
  obtain hc | hc := (B i).eq_zero_or_pos
  · rwa [hc, mul_zero, single_zero, single_zero, add_zero, tsub_zero]
  · convert (rB.move1 hi hc).push hi using 1
    ext k; simp only [add_apply, sub_apply]
    rcases eq_or_ne k i with rfl | hk
    · simp_rw [single_eq_same, tsub_self, single_succ]
    · simp_rw [single_eq_of_ne hk, tsub_zero]
      rcases eq_or_ne k (i + 1) with rfl | hk'
      · simp_rw [single_eq_same, single_succ]; grind
      · simp_rw [single_eq_of_ne hk', add_zero]
termination_by B i

/-- `(0, 0, 5, 11, 0, 0)` is reachable. -/
lemma five_eleven : Reachable (single 2 5 + single 3 11) := by
  have R : Reachable (single 1 3 + single 2 1 + single 3 1 + single 4 1 + single 5 1) := by
    convert base.push (show 0 < 5 by decide) using 1; decide
  replace R : Reachable (single 2 7 + single 3 1 + single 4 1 + single 5 1) := by
    convert R.push (show 1 < 5 by decide) using 1; decide
  replace R : Reachable (single 2 7 + single 4 3 + single 5 1) := by
    convert R.push (show 3 < 5 by decide) using 1; decide
  replace R : Reachable (single 2 7 + single 5 7) := by
    convert R.push (show 4 < 5 by decide) using 1; decide
  replace R : Reachable (single 2 6 + single 3 2 + single 5 7) := by
    convert R.move1 (show 2 < 5 by decide) (by decide) using 1; decide
  replace R : Reachable (single 2 6 + single 3 1 + single 4 2 + single 5 7) := by
    convert R.move1 (show 3 < 5 by decide) (by decide) using 1; decide
  replace R : Reachable (single 2 6 + single 3 1 + single 5 11) := by
    convert R.push (show 4 < 5 by decide) using 1; decide
  replace R : Reachable (single 2 6 + single 4 11) := by
    convert R.move2 (show 3 < 4 by decide) (by decide) using 1; decide
  convert R.move2 (show 2 < 4 by decide) (by decide) using 1; decide

/-- Decrement $B_i$ and double $B_{i+1}$, assuming $B_{i+2} = 0$, by doing `push, move2`. -/
lemma double {B : Fin 6 → ℕ} {i : Fin 6}
    (rB : Reachable B) (hi : i < 4) (pB : 0 < B i) (zB : B (i + 2) = 0) :
    Reachable (B + single (i + 1) (B (i + 1)) - single i 1) := by
  convert (rB.push (show i + 1 < 5 by grind)).move2 hi (by
    rw [add_apply, sub_apply, single_succ]; grind)
  ext k; simp only [comp_apply, add_apply, sub_apply]
  have (j : Fin 6) : j + 1 + 1 = j + 2 := by grind
  rcases eq_or_ne k i with rfl | hk
  · rw [swap_apply_of_ne_of_ne (by simp) (by simp), single_succ, this, single_add_two]; grind
  · rcases eq_or_ne k (i + 1) with rfl | hk'
    · grind [swap_apply_left, single_eq_same]
    · rw [single_eq_of_ne hk']
      rcases eq_or_ne k (i + 2) with rfl | hk''
      · grind [swap_apply_right, single_eq_same, single_succ]
      · rw [swap_apply_of_ne_of_ne hk' hk'', single_eq_of_ne hk', this, single_eq_of_ne hk'']
        grind

/-- `double` as many times as possible, emptying $B_i$ and doubling $B_{i+1}$ that many times. -/
lemma doubles {B : Fin 6 → ℕ} {i : Fin 6} (rB : Reachable B) (hi : i < 4) (zB : B (i + 2) = 0) :
    Reachable (update (B - single i (B i)) (i + 1) (B (i + 1) * 2 ^ B i)) := by
  obtain hc | hc := (B i).eq_zero_or_pos
  · rwa [hc, single_zero, tsub_zero, pow_zero, mul_one, update_eq_self]
  · convert (rB.double hi hc zB).doubles hi (by
      rw [sub_apply, add_apply, single_eq_of_ne (by simp), zB, zero_add, zero_tsub]) using 1
    ext k
    simp_rw [sub_apply, add_apply, single_eq_same, single_succ, single_succ', add_zero, tsub_zero,
      ← two_mul, ← mul_rotate, ← pow_succ, Nat.sub_add_cancel hc]
    rcases eq_or_ne k (i + 1) with rfl | hk'
    · simp only [mul_comm, update_self]
    · simp_rw [update_of_ne hk', sub_apply, add_apply, single_eq_of_ne hk', add_zero]
      rcases eq_or_ne k i with rfl | hk
      · simp_rw [single_eq_same, tsub_self]
      · simp_rw [single_eq_of_ne hk, tsub_zero]
termination_by B i

/-- Empty $B_i$ and set $B_{i+1} = 2^{B_i}$, assuming $B_{i+1} = B_{i+2} = 0$. -/
lemma exp {B : Fin 6 → ℕ} {i : Fin 6}
    (rB : Reachable B) (hi : i < 4) (pB : 0 < B i) (zB : B (i + 1) = 0) (zB' : B (i + 2) = 0) :
    Reachable (B - single i (B i) + single (i + 1) (2 ^ B i)) := by
  convert (rB.move1 (show i < 5 by grind) pB).doubles hi (by
    rw [add_apply, sub_apply, zB', single_eq_of_ne (by simp), tsub_zero,
      single_eq_of_ne (by simp), zero_add]) using 1
  simp_rw [add_apply, sub_apply, single_eq_same, single_succ, single_succ', zB, zero_tsub, zero_add,
    add_zero, ← pow_succ', Nat.sub_add_cancel pB]
  ext k; simp only [add_apply, sub_apply]
  rcases eq_or_ne k (i + 1) with rfl | hk'
  · grind [update_self, single_eq_same]
  · simp only [update_of_ne hk', sub_apply, add_apply, single_eq_of_ne hk', add_zero]
    rcases eq_or_ne k i with rfl | hk
    · simp_rw [single_eq_same, tsub_self]
    · simp_rw [single_eq_of_ne hk, tsub_zero]

/-- From `(0, 0, k+1, n, 0, 0)` with `n > 0` we can reach `(0, 0, k, 2^n, 0, 0)`. -/
lemma exp_mid {k n : ℕ} (h : Reachable (single 2 (k + 1) + single 3 n)) (hn : 0 < n) :
    Reachable (single 2 k + single 3 (2 ^ n)) := by
  have md := h.exp (show 3 < 4 by decide) (by simp [hn])
    (by simp [add_apply, single_eq_of_ne]) (by simp [add_apply, single_eq_of_ne])
  convert md.move2 (show 2 < 4 by decide) (by
    simp only [add_apply, sub_apply, single_eq_same]
    iterate 3 rw [single_eq_of_ne (by decide)]
    simp) using 1
  ext i; simp only [add_apply, sub_apply, comp_apply, Fin.reduceAdd]
  rcases eq_or_ne i 2 with rfl | i2
  · simp only [Fin.isValue, single_eq_same, ne_eq, Fin.reduceEq, not_false_eq_true,
      single_eq_of_ne, add_zero, zero_add, add_tsub_cancel_right]
    rw [swap_apply_of_ne_of_ne (by decide) (by decide), single_eq_same, single_eq_of_ne (by decide)]
    simp
  · simp only [Fin.isValue, single_eq_same, ne_eq, Fin.reduceEq, not_false_eq_true,
      single_eq_of_ne, zero_add, add_tsub_cancel_right, i2, tsub_zero]
    rcases eq_or_ne i 3 with rfl | i3
    · rw [swap_apply_left, single_eq_same, single_eq_same, single_eq_of_ne (by decide), zero_add]
    · rw [single_eq_of_ne i3]
      rcases eq_or_ne i 4 with rfl | i4
      · rw [swap_apply_right, single_eq_of_ne (by decide), single_eq_of_ne (by decide), zero_add]
      · rw [swap_apply_of_ne_of_ne i3 i4, single_eq_of_ne i2, single_eq_of_ne i4, zero_add]

/-- If all coins are in box 4, their number can be reduced by any desired amount. -/
lemma reduce {m n : ℕ} (h : Reachable (single 3 n)) (hmn : m ≤ n) : Reachable (single 3 m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    apply ih
    convert h.move2 (show 3 < 4 by decide) k.succ_pos
    ext i; simp only [sub_apply, comp_apply]
    rcases eq_or_ne i 3 with rfl | i3
    · rw [swap_apply_of_ne_of_ne (by decide) (by decide)]
      simp_rw [single_eq_same, add_tsub_cancel_right]
    · simp_rw [single_eq_of_ne i3, tsub_zero]; rw [single_eq_of_ne]
      rw [swap_apply_def]; split_ifs <;> grind

/-- The key power tower inequality in the solution. -/
lemma tower_inequality {m n : ℕ} (hm : m = 2010) (hn : n = 11) :
    2010 ^ 2010 ^ m ≤ 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ n := by
  calc
    _ ≤ 2 ^ (11 * 2010 ^ m) := by rw [pow_mul]; gcongr <;> lia
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two ?_
  calc
    _ ≤ 2 ^ (4 + 11 * m) := by rw [pow_add, pow_mul]; gcongr <;> lia
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two ?_
  calc
    _ ≤ 2 ^ 2 ^ 2 ^ 2 := by rw [hm]; lia
    _ ≤ _ := by
      iterate 3 apply Nat.pow_le_pow_right Nat.zero_lt_two
      lia

/-- `(0, 0, 0, 2010 ^ 2010 ^ 2010 / 4, 0, 0)` is reachable. -/
lemma quarter_target {m : ℕ} (hm : m = 2010) : Reachable (single 3 (2010 ^ 2010 ^ m / 4)) := by
  have R := five_eleven.exp_mid (by lia)
  set n : ℕ := 11
  iterate 4 replace R := R.exp_mid (Nat.two_pow_pos _)
  rw [single_zero, zero_add] at R
  exact R.reduce ((Nat.div_le_self ..).trans (tower_inequality hm rfl))

end Reachable

open Reachable in
theorem result : Reachable (single 5 (2010 ^ 2010 ^ 2010)) := by
  -- `m` is defined to avoid deep recursion in the kernel.
  -- See https://github.com/leanprover/lean4/issues/11713
  set m : ℕ := 2010
  have hm : m = 2010 := by rfl
  convert ((quarter_target hm).push (show 3 < 5 by decide)).push (show 4 < 5 by decide)
  simp only [single_eq_same, tsub_self, Fin.reduceAdd, zero_add, single_inj]
  rw [← mul_assoc, show 2 * 2 = 4 by rfl, mul_comm, Nat.div_mul_cancel]
  trans 2010 ^ 2
  · lia
  · apply pow_dvd_pow
    trans 2010 ^ 1
    · lia
    · gcongr <;> lia

end Imo2010Q5
