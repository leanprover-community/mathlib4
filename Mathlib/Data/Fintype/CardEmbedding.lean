/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Embedding

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

open Function

open Nat

namespace Fintype

theorem card_embedding_eq_of_unique {α β : Type*} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult

-- Establishes the cardinality of the type of all injections between two finite types.
-- Porting note: `induction α using Fintype.induction_empty_option` can't work with the `Fintype α`
-- instance so instead we make an ugly refine and `dsimp` a lot.
@[simp]
theorem card_embedding_eq {α β : Type*} [Fintype α] [Fintype β] [emb : Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  rw [Subsingleton.elim emb Embedding.fintype]
  refine Fintype.induction_empty_option (P := fun t ↦ ‖t ↪ β‖ = ‖β‖.descFactorial ‖t‖)
        (fun α₁ α₂ h₂ e ih ↦ ?_) (?_) (fun γ h ih ↦ ?_) α <;> dsimp only at * <;> clear! α
  · letI := Fintype.ofEquiv _ e.symm
    rw [← card_congr (Equiv.embeddingCongr e (Equiv.refl β)), ih, card_congr e]
  · rw [card_pempty, Nat.descFactorial_zero, card_eq_one_iff]
    exact ⟨Embedding.ofIsEmpty, fun x ↦ DFunLike.ext _ _ isEmptyElim⟩
  · classical
    rw [card_option, Nat.descFactorial_succ, card_congr (Embedding.optionEmbeddingEquiv γ β),
        card_sigma, ← ih]
    simp only [Fintype.card_compl_set, Fintype.card_range, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, mul_comm]

/-- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
theorem card_embedding_eq_of_infinite {α β : Type*} [Infinite α] [Finite β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = 0 :=
  card_eq_zero

end Fintype
