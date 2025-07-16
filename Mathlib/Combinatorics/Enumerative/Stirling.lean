/-
Copyright (c) 2025 Beibei Xiong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beibei Xiong, Yu Shao, Weijie Jiang
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Stirling Numbers

This file defines Stirling numbers of the first and second kinds, proves their fundamental
recurrence relations, and establishes some of their key properties and identities.
-/

/-!
# The Stirling numbers of the first kind

The unsigned Stirling numbers of the first kind, represent the number of ways
to partition n distinct elements into k non-empty cycles.

# The Stirling numbers of the second kind

The Stirling numbers of the second kind, represent the number of ways to partition
n distinct elements into k non-empty subsets.

# Main definitions

* `Nat.stirlingFirst`: the number of ways to partition n distinct elements into k non-empty
  cycles, defined by the recursive relationship it satisfies.
* `Nat.stirlingSecond`: the number of ways to partition n distinct elements into k non-empty
  subsets, defined by the recursive relationship it satisfies.

# References:

* [Stirling Numbers of the First Kind – ProofWiki](https://proofwiki.org/wiki/Definition:Stirling_Numbers_of_the_First_Kind/Unsigned)
* [Stirling Numbers of the Second Kind – ProofWiki](https://proofwiki.org/wiki/Definition:Stirling_Numbers_of_the_Second_Kind)

-/

open Nat

namespace Nat

/--
`Nat.stirlingFirst n k` is the (unsigned) Stirling number of the first kind,
counting the number of permutations of `n` elements with exactly `k` disjoint cycles.
-/
def stirlingFirst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirlingFirst n (k + 1) + stirlingFirst n k

@[simp]
theorem stirlingFirst_zero: stirlingFirst 0 0 = 1 :=
  rfl

@[simp]
theorem stirlingFirst_zero_succ (k : ℕ) : stirlingFirst 0 (succ k) = 0 :=
  rfl

@[simp]
theorem stirlingFirst_succ_zero (n : ℕ) : stirlingFirst (succ n) 0 = 0 :=
  rfl

theorem stirlingFirst_succ_left (n k : ℕ) (hk : k ≠ 0) :
    stirlingFirst (n + 1) k = n * stirlingFirst n k + stirlingFirst n (k - 1) := by
  have hk : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

theorem stirlingFirst_succ_right (n k : ℕ) (hn : n ≠ 0) :
    stirlingFirst n (k + 1) =
      (n - 1) * stirlingFirst (n - 1) (k + 1) + stirlingFirst (n - 1) k := by
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

theorem stirlingFirst_succ_succ (n k : ℕ) :
    stirlingFirst (n + 1) (k + 1) = n * stirlingFirst n (k + 1) + stirlingFirst n k := by
  rfl

theorem stirlingFirst_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirlingFirst n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingFirst]
  | n + 1, k + 1, hk => by
    have hnk : n < k := Nat.lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := Nat.lt_of_succ_lt hk
    rw [stirlingFirst_succ_succ, stirlingFirst_eq_zero_of_lt hnk,
      stirlingFirst_eq_zero_of_lt hnk1, mul_zero]

theorem stirlingFirst_self (n : ℕ) : stirlingFirst n n = 1 := by
  induction n <;> simp only [*, stirlingFirst, stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self _),
    mul_zero]

theorem stirlingFirst_succ_self_left (n : ℕ) : stirlingFirst (n + 1) n = (n + 1).choose 2 := by
  induction' n with n ih
  · simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  · rw [stirlingFirst_succ_succ, ih, stirlingFirst_self, mul_one, Nat.choose_succ_succ (n + 1),
      Nat.choose_one_right]

theorem stirlingFirst_one_right (n : ℕ) : stirlingFirst (n + 1) 1 = n.factorial := by
  induction' n with n hn
  · rfl
  · rw [stirlingFirst_succ_succ, zero_add, hn, stirlingFirst_succ_zero]
    simp [Nat.factorial_succ]


/--
`Nat.stirlingSecond n k` is the Stirling number of the second kind,
counting the number of ways to partition a set of `n` elements into `k` nonempty subsets.
-/
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

@[simp]
theorem stirlingSecond_zero : stirlingSecond 0 0 = 1 :=
  rfl

@[simp]
theorem stirlingSecond_zero_succ (k : ℕ) : stirlingSecond 0 (succ k) = 0 :=
  rfl

@[simp]
theorem stirlingSecond_succ_zero (n : ℕ) : stirlingSecond (succ n) 0 = 0 :=
  rfl

theorem stirlingSecond_succ_left (n k : ℕ) (hk : k ≠ 0) :
    stirlingSecond (n + 1) k = k * stirlingSecond n k + stirlingSecond n (k - 1) := by
  have hk : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

theorem stirlingSecond_succ_right (n k : ℕ) (hn : n ≠ 0) :
    stirlingSecond n (k + 1) =
      (k + 1) * stirlingSecond (n - 1) (k + 1) + stirlingSecond (n - 1) k := by
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

theorem stirlingSecond_succ_succ (n k : ℕ) :
    stirlingSecond (n + 1) (k + 1) =
      (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k := rfl

theorem stirlingSecond_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirlingSecond n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingSecond]
  | n + 1, k + 1, hk => by
    have hnk : n < k := Nat.lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := Nat.lt_of_succ_lt hk
    simp only [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt hnk,
      stirlingSecond_eq_zero_of_lt hnk1, mul_zero]

theorem stirlingSecond_self (n : ℕ) : stirlingSecond n n = 1 := by
  induction n <;> simp only [*, stirlingSecond, stirlingSecond_eq_zero_of_lt (lt_succ_self _),
    mul_zero]

theorem stirlingSecond_one_right (n : ℕ) : stirlingSecond (n + 1) 1 = 1 := by
  induction' n with n ih
  · rfl
  · rw [stirlingSecond, stirlingSecond_succ_zero, ih]

theorem stirlingSecond_succ_self_left (n : ℕ) :
    stirlingSecond (n + 1) n = (n + 1).choose 2 := by
  induction' n with n ih
  · simp only [zero_add, stirlingSecond_succ_zero, choose_succ_self]
  · rw [stirlingSecond_succ_succ, ih, stirlingSecond_self, mul_one,
      Nat.choose_succ_succ (n + 1), Nat.choose_one_right]

end Nat
