/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

# Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `numDerangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_numDerangements`: Proof that `numDerangements` really does compute the
    number of derangements.
* `numDerangements_sum`: A lemma giving an expression for `numDerangements n` in terms of
    factorials.
-/


open derangements Equiv Fintype

variable {α : Type*} [DecidableEq α] [Fintype α]

instance : DecidablePred (derangements α) := fun _ => Fintype.decidableForallFintype

instance : Fintype (derangements α) :=
  inferInstanceAs <| Fintype { f : Perm α | ∀ x : α, f x ≠ x }


theorem card_derangements_invariant {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (h : card α = card β) : card (derangements α) = card (derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)

theorem card_derangements_fin_add_two (n : ℕ) :
    card (derangements (Fin (n + 2))) =
      (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n + 1))) := by
  -- get some basic results about the size of Fin (n+1) plus or minus an element
  have h1 : ∀ a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) := by
    intro a
    simp only
      [card_ofFinset (s := Finset.filter (fun x => x ∈ ({a}ᶜ : Set (Fin (n + 1)))) Finset.univ),
      Set.mem_compl_singleton_iff, Finset.filter_ne' _ a,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_fin, add_tsub_cancel_right,
      card_fin]
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp only [card_fin, card_option]
  -- rewrite the LHS and substitute in our fintype-level equivalence
  simp only [card_derangements_invariant h2,
    card_congr
      (@derangementsRecursionEquiv (Fin (n + 1))
        _),-- push the cardinality through the Σ and ⊕ so that we can use `card_n`
    card_sigma,
    card_sum, card_derangements_invariant (h1 _), Finset.sum_const, nsmul_eq_mul, Finset.card_fin,
    mul_add, Nat.cast_id]

/-- The number of derangements of an `n`-element set. -/
def numDerangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))

@[simp]
theorem numDerangements_zero : numDerangements 0 = 1 :=
  rfl

@[simp]
theorem numDerangements_one : numDerangements 1 = 0 :=
  rfl

theorem numDerangements_add_two (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  rfl

theorem numDerangements_succ (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) - (-1) ^ n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [numDerangements_add_two, hn, pow_succ, Int.natCast_mul, Int.natCast_add]
    ring

theorem card_derangements_fin_eq_numDerangements {n : ℕ} :
    card (derangements (Fin n)) = numDerangements n := by
  induction n using Nat.strongRecOn with | ind n hyp => _
  rcases n with _ | _ | n
  -- knock out cases 0 and 1
  · rfl
  · rfl
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two, card_derangements_fin_add_two, mul_add, hyp, hyp] <;> omega

theorem card_derangements_eq_numDerangements (α : Type*) [Fintype α] [DecidableEq α] :
    card (derangements α) = numDerangements (card α) := by
  rw [← card_derangements_invariant (card_fin _)]
  exact card_derangements_fin_eq_numDerangements

theorem numDerangements_sum (n : ℕ) :
    (numDerangements n : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.ascFactorial (k + 1) (n - k) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Finset.sum_range_succ, numDerangements_succ, hn, Finset.mul_sum, tsub_self,
      Nat.ascFactorial_zero, Int.ofNat_one, mul_one, pow_succ', neg_one_mul, sub_eq_add_neg,
      add_left_inj, Finset.sum_congr rfl]
    -- show that (n + 1) * (-1)^x * asc_fac x (n - x) = (-1)^x * asc_fac x (n.succ - x)
    intro x hx
    have h_le : x ≤ n := Finset.mem_range_succ_iff.mp hx
    rw [Nat.succ_sub h_le, Nat.ascFactorial_succ, add_right_comm, add_tsub_cancel_of_le h_le,
      Int.natCast_mul, Int.natCast_add, mul_left_comm, Nat.cast_one]
