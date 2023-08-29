/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Logic.Embedding.Set

#align_import data.fintype.card_embedding from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

open Function

open Nat BigOperators

namespace Fintype

theorem card_embedding_eq_of_unique {α β : Type*} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult
#align fintype.card_embedding_eq_of_unique Fintype.card_embedding_eq_of_unique

-- Establishes the cardinality of the type of all injections between two finite types.
-- porting note: `induction'` is broken so instead we make an ugly refine and `dsimp` a lot.
@[simp]
theorem card_embedding_eq {α β : Type*} [Fintype α] [Fintype β] [emb : Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  rw [Subsingleton.elim emb Embedding.fintype]
  -- ⊢ ‖α ↪ β‖ = descFactorial ‖β‖ ‖α‖
  refine' Fintype.induction_empty_option (P := fun t ↦ ‖t ↪ β‖ = ‖β‖.descFactorial ‖t‖)
        (fun α₁ α₂ h₂ e ih ↦ ?_) (?_) (fun γ h ih ↦ ?_) α <;> dsimp only <;> clear! α
                                                              -- ⊢ ‖α₂ ↪ β‖ = descFactorial ‖β‖ ‖α₂‖
                                                              -- ⊢ ‖PEmpty ↪ β‖ = descFactorial ‖β‖ ‖PEmpty‖
                                                              -- ⊢ ‖Option γ ↪ β‖ = descFactorial ‖β‖ ‖Option γ‖
                                                                             -- ⊢ ‖α₂ ↪ β‖ = descFactorial ‖β‖ ‖α₂‖
                                                                             -- ⊢ ‖PEmpty ↪ β‖ = descFactorial ‖β‖ ‖PEmpty‖
                                                                             -- ⊢ ‖Option γ ↪ β‖ = descFactorial ‖β‖ ‖Option γ‖
  · letI := Fintype.ofEquiv _ e.symm
    -- ⊢ ‖α₂ ↪ β‖ = descFactorial ‖β‖ ‖α₂‖
    rw [← card_congr (Equiv.embeddingCongr e (Equiv.refl β)), ih, card_congr e]
    -- 🎉 no goals
  · rw [card_pempty, Nat.descFactorial_zero, card_eq_one_iff]
    -- ⊢ ∃ x, ∀ (y : PEmpty ↪ β), y = x
    exact ⟨Embedding.ofIsEmpty, fun x ↦ FunLike.ext _ _ isEmptyElim⟩
    -- 🎉 no goals
  · classical
    dsimp only at ih
    rw [card_option, Nat.descFactorial_succ, card_congr (Embedding.optionEmbeddingEquiv γ β),
        card_sigma, ←ih]
    simp only [Fintype.card_compl_set, Fintype.card_range, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
#align fintype.card_embedding_eq Fintype.card_embedding_eq

/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp]
theorem card_embedding_eq_of_infinite {α β : Type*} [Infinite α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = 0 :=
  card_eq_zero
#align fintype.card_embedding_eq_of_infinite Fintype.card_embedding_eq_of_infinite

end Fintype
