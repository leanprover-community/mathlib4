/-
Copyright (c) 2025 Beibei Xiong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beibei Xiong, Shao Yu, Weijie Jiang
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.Basic


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

* `Nat.numStirling_fst`: the number of ways to partition n distinct elements into k non-empty
cycles, Defined by the recursive relationship it satisfies.
* `Nat.numStirling_snd`: the number of ways to partition n distinct elements into k non-empty
subsets, Defined by the recursive relationship it satisfies.


# References:

* [Stirling Numbers of the First Kind – MathWorld](https://mathworld.wolfram.com/StirlingNumberoftheFirstKind.html)
* [Stirling Numbers of the Second Kind – MathWorld](https://mathworld.wolfram.com/StirlingNumberoftheSecondKind.html)

-/



namespace Nat


/--
`Nat.numStirling_fst n k` is the (unsigned) Stirling number of the first kind,
counting the number of permutations of `n` elements with exactly `k` disjoint cycles.
-/
def numStirling_fst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * numStirling_fst n (k + 1) + numStirling_fst n k

@[simp]
theorem numStirling_fst_zero: numStirling_fst 0 0 = 1 := by simp [numStirling_fst]

@[simp]
theorem numStirling_fst_zero_succ (k : ℕ) : numStirling_fst 0 (succ k) = 0 := by
  simp [numStirling_fst]

@[simp]
theorem numStirling_fst_succ_zero (n : ℕ) : numStirling_fst (succ n) 0 = 0 := by
  simp [numStirling_fst]

theorem numStirling_fst_succ_left (n k : ℕ) (hk : 0 < k) :
    numStirling_fst (n + 1) k = n * numStirling_fst n k + numStirling_fst n (k - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

theorem numStirling_fst_succ_right (n k : ℕ) (hn : 0 < n) :
    numStirling_fst n (k + 1)
     = (n - 1) * numStirling_fst (n - 1) (k + 1) + numStirling_fst (n - 1) k := by
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

theorem numStirling_fst_succ_succ (n k : ℕ) :
    numStirling_fst (n + 1) (k + 1) = n * numStirling_fst n (k + 1) +  numStirling_fst n k := by
  rw [numStirling_fst]

theorem numStirling_fst_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → numStirling_fst n k= 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [numStirling_fst]
  | n + 1, k + 1, hk => by
    have hnk : n < k := Nat.lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := Nat.lt_of_succ_lt hk
    rw [numStirling_fst_succ_succ, numStirling_fst_eq_zero_of_lt hnk,
         numStirling_fst_eq_zero_of_lt hnk1]
    rfl

theorem numStirling_fst_self (n : ℕ) : numStirling_fst n n = 1 := by
  induction n <;> simp [*, numStirling_fst, numStirling_fst_eq_zero_of_lt (Nat.lt_succ_self _)]

theorem numStirling_fst_succ_self_left (n : ℕ) : numStirling_fst (n + 1) n = (n * (n + 1)) / 2 := by
  induction' n with n hn
  · simp [numStirling_fst]
  · have h₀ : (n + 1) = (2 * (n + 1)) / 2 := by
      rw [mul_comm, Nat.mul_div_assoc, Nat.div_self, mul_one]
      · omega
      · exact Nat.dvd_refl _
    rw [numStirling_fst_succ_succ, hn, numStirling_fst_self, mul_one]
    nth_rw 1 [h₀]
    rw [← Nat.add_div_of_dvd_left]
    · ring_nf
    · suffices h₁ : Even (n * (n + 1)) from by
        rw [even_iff_two_dvd] at h₁
        exact h₁
      exact Nat.even_mul_succ_self n

theorem numStirling_fst_one_right (n : ℕ) : numStirling_fst (n + 1) 1 = n.factorial := by
  induction' n with n hn
  · simp [numStirling_fst]
  · rw [numStirling_fst_succ_succ, zero_add, hn, numStirling_fst_succ_zero]
    simp [Nat.sub_self, Nat.factorial_succ]


/--
`Nat.numStirling_snd n k` is the Stirling number of the second kind,
counting the number of ways to partition a set of `n` elements into `k` nonempty subsets.
-/
def numStirling_snd : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    (k + 1) * numStirling_snd n (k + 1) + numStirling_snd n k

@[simp]
theorem numStirling_snd_zero : numStirling_snd 0 0 = 1 :=
  rfl

@[simp]
theorem numStirling_snd_zero_succ (k : ℕ) : numStirling_snd 0 (succ k) = 0 :=
  rfl

@[simp]
theorem numStirling_snd_zero_right' (n : ℕ) : numStirling_snd (succ n) 0 = 0 :=
  rfl

theorem numStirling_snd_succ_left (n k : ℕ) (hk : 0 < k) :
    numStirling_snd (n + 1) k = k * numStirling_snd n k + numStirling_snd n (k - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

theorem numStirling_snd_succ_right (n k : ℕ) (hn : 0 < n) :
    numStirling_snd n (k + 1) =
     (k + 1) * numStirling_snd (n - 1) (k + 1) + numStirling_snd (n - 1) k := by
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

theorem numStirling_snd_succ_succ (n k : ℕ) :
    numStirling_snd (n + 1) (k + 1) =
     (k + 1) * numStirling_snd n (k + 1) + numStirling_snd n k := by
  rw [numStirling_snd]

theorem numStirling_snd_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → numStirling_snd n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [numStirling_snd]
  | n + 1, k + 1, hk => by
    have hnk : n < k := Nat.lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := Nat.lt_of_succ_lt hk
    rw [numStirling_snd_succ_succ, numStirling_snd_eq_zero_of_lt hnk,
     numStirling_snd_eq_zero_of_lt hnk1]
    simp

theorem numStirling_snd_self (n : ℕ) : numStirling_snd n n = 1 := by
  induction n <;> simp [*, numStirling_snd, numStirling_snd_eq_zero_of_lt (lt_succ_self _)]

theorem numStirling_snd_one_right (n : ℕ) : numStirling_snd (n+1) 1 = 1 := by
  simp [numStirling_snd]
  induction' n with n ih
  · simp [numStirling_snd]
  · rw [numStirling_snd_zero_right']
    simp
    nth_rw 2 [ show 1 = 0 + 1 by ring ]
    rw [numStirling_snd_succ_succ]
    simp
    exact ih

theorem stirlning_second_succ_self_left (n : ℕ) :
    numStirling_snd (n + 1) n = (n * (n + 1)) / 2 := by
  induction' n with n hn
  · simp
  · rw [numStirling_snd_succ_succ, hn, numStirling_snd_self, mul_one, add_assoc n 1 1]
    simp only [reduceAdd]
    have : n + 1 = (2 * (n + 1)) / 2 := by
      rw [mul_comm, Nat.mul_div_assoc, Nat.div_self (by omega), mul_one]
      exact Nat.dvd_refl _
    nth_rw 1 [this]
    rw [← Nat.add_div_of_dvd_left]
    · ring_nf
    · suffices h₁ : Even (n * (n + 1)) from by
        rw [even_iff_two_dvd] at h₁
        exact h₁
      exact Nat.even_mul_succ_self n

end Nat
