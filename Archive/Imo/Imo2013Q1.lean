/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2013 Q1

Prove that for any pair of positive integers k and n, there exist k positive integers
m₁, m₂, ..., mₖ (not necessarily different) such that

  1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).

# Solution

Adaptation of the solution found in https://www.imo-official.org/problems/IMO2013SL.pdf

We prove a slightly more general version where k does not need to be strictly positive.
-/


namespace Imo2013Q1

theorem arith_lemma (k n : ℕ) : 0 < 2 * n + 2 ^ k.succ := by positivity

theorem prod_lemma (m : ℕ → ℕ+) (k : ℕ) (nm : ℕ+) :
    ∏ i ∈ Finset.range k, ((1 : ℚ) + 1 / ↑(if i < k then m i else nm)) =
      ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by
  suffices ∀ i, i ∈ Finset.range k → (1 : ℚ) + 1 / ↑(if i < k then m i else nm) = 1 + 1 / m i from
    Finset.prod_congr rfl this
  intro i hi
  simp [Finset.mem_range.mp hi]

end Imo2013Q1

open Imo2013Q1
theorem imo2013_q1 (n : ℕ+) (k : ℕ) :
    ∃ m : ℕ → ℕ+, (1 : ℚ) + (2 ^ k - 1) / n = ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by
  revert n
  induction k with
  | zero => intro n; use fun (_ : ℕ) => (1 : ℕ+); simp -- For the base case, any m works.
  | succ pk hpk =>
  intro n
  obtain ⟨t, ht : ↑n = t + t⟩ | ⟨t, ht : ↑n = 2 * t + 1⟩ := (n : ℕ).even_or_odd
  · -- even case
    rw [← two_mul] at ht
    rcases t with - | t
    -- Eliminate the zero case to simplify later calculations.
    · exfalso; rw [Nat.mul_zero] at ht; exact PNat.ne_zero n ht
    -- Now we have ht : ↑n = 2 * (t + 1).
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩
    obtain ⟨pm, hpm⟩ := hpk t_succ
    let m i := if i < pk then pm i else ⟨2 * t + 2 ^ pk.succ, arith_lemma pk t⟩
    use m
    have hmpk : (m pk : ℚ) = 2 * t + 2 ^ pk.succ := by
      have : m pk = ⟨2 * t + 2 ^ pk.succ, _⟩ := if_neg (irrefl pk); simp [this]
    calc
      ((1 : ℚ) + (2 ^ pk.succ - 1) / (n : ℚ) : ℚ)= 1 + (2 * 2 ^ pk - 1) / (2 * (t + 1) : ℕ) := by
        rw [ht, pow_succ']
      _ = (1 + 1 / (2 * t + 2 * 2 ^ pk)) * (1 + (2 ^ pk - 1) / (↑t + 1)) := by
        field_simp
        ring
      _ = (1 + 1 / (2 * t + 2 ^ pk.succ)) * (1 + (2 ^ pk - 1) / t_succ) := by
        simp [pow_succ', PNat.mk_coe, t_succ]
      _ = (∏ i ∈ Finset.range pk, (1 + 1 / (m i : ℚ))) * (1 + 1 / m pk) := by
        rw [prod_lemma, hpm, ← hmpk, mul_comm]
      _ = ∏ i ∈ Finset.range pk.succ, (1 + 1 / (m i : ℚ)) := by rw [← Finset.prod_range_succ _ pk]
  · -- odd case
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩
    obtain ⟨pm, hpm⟩ := hpk t_succ
    let m i := if i < pk then pm i else ⟨2 * t + 1, Nat.succ_pos _⟩
    use m
    have hmpk : (m pk : ℚ) = 2 * t + 1 := by
      have : m pk = ⟨2 * t + 1, _⟩ := if_neg (irrefl pk)
      simp [this]
    calc
      ((1 : ℚ) + (2 ^ pk.succ - 1) / ↑n : ℚ) = 1 + (2 * 2 ^ pk - 1) / (2 * t + 1 : ℕ) := by
        rw [ht, pow_succ']
      _ = (1 + 1 / (2 * t + 1)) * (1 + (2 ^ pk - 1) / (t + 1)) := by
        field_simp
        ring
      _ = (1 + 1 / (2 * t + 1)) * (1 + (2 ^ pk - 1) / t_succ) := by norm_cast
      _ = (∏ i ∈ Finset.range pk, (1 + 1 / (m i : ℚ))) * (1 + 1 / ↑(m pk)) := by
        rw [prod_lemma, hpm, ← hmpk, mul_comm]
      _ = ∏ i ∈ Finset.range pk.succ, (1 + 1 / (m i : ℚ)) := by rw [← Finset.prod_range_succ _ pk]
