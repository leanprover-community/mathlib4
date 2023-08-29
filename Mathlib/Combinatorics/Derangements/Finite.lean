/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

#align_import combinatorics.derangements.finite from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

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

open BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

instance : DecidablePred (derangements α) := fun _ => Fintype.decidableForallFintype

-- porting note: used to use the tactic delta_instance
instance : Fintype (derangements α) := Subtype.fintype (fun (_ : Perm α) => ∀ (x_1 : α), ¬_ = x_1)

theorem card_derangements_invariant {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (h : card α = card β) : card (derangements α) = card (derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)
#align card_derangements_invariant card_derangements_invariant

theorem card_derangements_fin_add_two (n : ℕ) :
    card (derangements (Fin (n + 2))) =
      (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n + 1))) := by
  -- get some basic results about the size of fin (n+1) plus or minus an element
  have h1 : ∀ a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) := by
    intro a
    simp only [Fintype.card_fin, Finset.card_fin, Fintype.card_ofFinset, Finset.filter_ne' _ a,
      Set.mem_compl_singleton_iff, Finset.card_erase_of_mem (Finset.mem_univ a),
      add_tsub_cancel_right]
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp only [card_fin, card_option]
  -- ⊢ card ↑(derangements (Fin (n + 2))) = (n + 1) * card ↑(derangements (Fin n))  …
  -- rewrite the LHS and substitute in our fintype-level equivalence
  simp only [card_derangements_invariant h2,
    card_congr
      (@derangementsRecursionEquiv (Fin (n + 1))
        _),-- push the cardinality through the Σ and ⊕ so that we can use `card_n`
    card_sigma,
    card_sum, card_derangements_invariant (h1 _), Finset.sum_const, nsmul_eq_mul, Finset.card_fin,
    mul_add, Nat.cast_id]
#align card_derangements_fin_add_two card_derangements_fin_add_two

/-- The number of derangements of an `n`-element set. -/
def numDerangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))
#align num_derangements numDerangements

@[simp]
theorem numDerangements_zero : numDerangements 0 = 1 :=
  rfl
#align num_derangements_zero numDerangements_zero

@[simp]
theorem numDerangements_one : numDerangements 1 = 0 :=
  rfl
#align num_derangements_one numDerangements_one

theorem numDerangements_add_two (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  rfl
#align num_derangements_add_two numDerangements_add_two

theorem numDerangements_succ (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) - (-1) ^ n := by
  induction' n with n hn
  -- ⊢ ↑(numDerangements (Nat.zero + 1)) = (↑Nat.zero + 1) * ↑(numDerangements Nat. …
  · rfl
    -- 🎉 no goals
  · simp only [numDerangements_add_two, hn, pow_succ, Int.ofNat_mul, Int.ofNat_add, Int.ofNat_succ]
    -- ⊢ (↑n + 1) * (↑(numDerangements n) + ((↑n + 1) * ↑(numDerangements n) - (-1) ^ …
    ring
    -- 🎉 no goals
#align num_derangements_succ numDerangements_succ

theorem card_derangements_fin_eq_numDerangements {n : ℕ} :
    card (derangements (Fin n)) = numDerangements n := by
  induction' n using Nat.strong_induction_on with n hyp
  -- ⊢ card ↑(derangements (Fin n)) = numDerangements n
  rcases n with _ | _ | n
  -- porting note: the two `convert_to` weren't necessary before.
  · convert_to card ↑{ f : Perm (Fin 0) | ∀ (x : Fin 0), f x ≠ x } = _ using 2; rfl
    -- ⊢ card ↑{f | ∀ (x : Fin 0), ↑f x ≠ x} = numDerangements Nat.zero
                                                                                -- 🎉 no goals
  · convert_to card ↑{ f : Perm (Fin 1) | ∀ (x : Fin 1), f x ≠ x } = _ using 2; rfl
    -- ⊢ card ↑{f | ∀ (x : Fin 1), ↑f x ≠ x} = numDerangements (Nat.succ Nat.zero)
                                                                                -- 🎉 no goals
  -- knock out cases 0 and 1
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two, card_derangements_fin_add_two, mul_add,
    hyp _ (Nat.lt_add_of_pos_right zero_lt_two), hyp _ (lt_add_one _)]
#align card_derangements_fin_eq_num_derangements card_derangements_fin_eq_numDerangements

theorem card_derangements_eq_numDerangements (α : Type*) [Fintype α] [DecidableEq α] :
    card (derangements α) = numDerangements (card α) := by
  rw [← card_derangements_invariant (card_fin _)]
  -- ⊢ card ↑(derangements (Fin (card α))) = numDerangements (card α)
  exact card_derangements_fin_eq_numDerangements
  -- 🎉 no goals
#align card_derangements_eq_num_derangements card_derangements_eq_numDerangements

theorem numDerangements_sum (n : ℕ) :
    (numDerangements n : ℤ) =
      ∑ k in Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.ascFactorial k (n - k) := by
  induction' n with n hn; · rfl
  -- ⊢ ↑(numDerangements Nat.zero) = ∑ k in Finset.range (Nat.zero + 1), (-1) ^ k * …
                            -- 🎉 no goals
  rw [Finset.sum_range_succ, numDerangements_succ, hn, Finset.mul_sum, tsub_self,
    Nat.ascFactorial_zero, Int.ofNat_one, mul_one, pow_succ, neg_one_mul, sub_eq_add_neg,
    add_left_inj, Finset.sum_congr rfl]
  -- show that (n + 1) * (-1)^x * asc_fac x (n - x) = (-1)^x * asc_fac x (n.succ - x)
  intro x hx
  -- ⊢ (↑n + 1) * ((-1) ^ x * ↑(Nat.ascFactorial x (n - x))) = (-1) ^ x * ↑(Nat.asc …
  have h_le : x ≤ n := Finset.mem_range_succ_iff.mp hx
  -- ⊢ (↑n + 1) * ((-1) ^ x * ↑(Nat.ascFactorial x (n - x))) = (-1) ^ x * ↑(Nat.asc …
  rw [Nat.succ_sub h_le, Nat.ascFactorial_succ, add_tsub_cancel_of_le h_le, Int.ofNat_mul,
    Int.ofNat_succ, mul_left_comm]
#align num_derangements_sum numDerangements_sum
