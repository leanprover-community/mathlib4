/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.fintype.card_embedding
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Embedding

set_option autoImplicit true -- **TODO** delete this later
-- set_option pp.explicit true -- **TODO** delete this later

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


-- mathport name: finset.card
local notation "|" x "|" => Finset.card x

-- mathport name: fintype.card
local notation "‖" x "‖" => Fintype.card x

open Function

open Nat BigOperators

namespace Fintype

theorem card_embedding_eq_of_unique {α β : Type _} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult
#align fintype.card_embedding_eq_of_unique Fintype.card_embedding_eq_of_unique


-- Establishes the cardinality of the type of all injections between two finite types.
@[simp]
theorem card_embedding_eq {α β : Type _} [a : Fintype α] [b : Fintype β] [emb: Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  classical
    -- letI := 1
    refine' Fintype.induction_empty_option _ _ _ α
    -- intro α₁ α₂ h₂ e ih

    -- induction' ‹Fintype α› using Fintype.induction_empty_option with α₁ α₂ h₂ e ih α h ih
    · intro α₁ α₂ h₂ e ih
      letI := Fintype.ofEquiv α₂ e.symm
      let v1 := (Equiv.refl β)
      let v2 := (Equiv.embeddingCongr e v1)
      let v3 := card_congr v2
      erw [←v3, ih, card_congr e]
    · rw [card_pempty, Nat.descFactorial_zero, card_eq_one_iff]
      exact ⟨embedding.of_is_empty, fun x => FunLike.ext _ _ isEmptyElim⟩
    · intro α₁ h₂ ih
      rw [card_option, Nat.descFactorial_succ, card_congr (embedding.option_embedding_equiv α β),
        card_sigma, ← ih]
      simp only [Fintype.card_compl_set, Fintype.card_range, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]

-- #align fintype.card_embedding_eq Fintype.card_embedding_eq

/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp]
theorem card_embedding_eq_of_infinite {α β : Type _} [Infinite α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = 0 :=
  card_eq_zero
#align fintype.card_embedding_eq_of_infinite Fintype.card_embedding_eq_of_infinite

end Fintype
