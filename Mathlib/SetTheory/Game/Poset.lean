/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.WellQuasiOrder
import Mathlib.SetTheory.Game.Impartial

variable {α : Type*} [Preorder α]

open Set

/-- A valid move in the poset game is to change set `t` to set `s`, whenever `s = t \ Ici a` for
some `a ∈ s`.

In a WQO, this relation is well-founded. -/
def posetMove (s t : Set α) : Prop :=
  ∃ a ∈ s, s = t \ Ici a

@[inherit_doc]
local infixl:50 " ≺ " => posetMove

theorem subrelation_posetMove : @Subrelation (Set α) (· ≺ ·) (· ⊂ ·) := by
  rintro x y ⟨a, ha, rfl⟩
  use diff_subset
  rw [not_subset]
  use a, mem_of_mem_diff ha
  simp

theorem subrelation_transGen_posetMove :
    @Subrelation (Set α) (Relation.TransGen (· ≺ ·)) (· ⊂ ·) :=
  subrelation_posetMove.transGen

theorem not_empty_posetMove (s : Set α) : ¬ ∅ ≺ s := by
  simp [posetMove]

theorem posetMove_irrefl (s : Set α) : ¬ s ≺ s :=
  fun h ↦ ssubset_irrefl s <| subrelation_posetMove h

instance : IsIrrefl (Set α) (· ≺ ·) where
  irrefl := posetMove_irrefl

theorem wellFounded_posetMove [WellQuasiOrderedLE α] : @WellFounded (Set α) (· ≺ ·) := by
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  have hf' := hf
  choose g hg using hf
  obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le g
  let f' := @RelEmbedding.natGT _ (· < ·) _ f fun n ↦ subrelation_posetMove (hf' n)
  have : g n ∈ f (m + 1) := (f'.map_rel_iff.2 (Nat.succ_lt_succ h)).le (hg n).1
  rw [(hg m).2, mem_diff] at this
  exact this.2 h'

instance [WellQuasiOrderedLE α] : IsWellFounded (Set α) (· ≺ ·) :=
  ⟨wellFounded_posetMove⟩

namespace SetTheory.PGame
open SetTheory

/-- A position in the poset game. A valid move in the poset game is to change set `t` to set `s`,
whenever `s = t \ Ici a` for some `a ∈ s`.

See also `posetMove`. -/
def posetPos [WellQuasiOrderedLE α] (t : Set α) : PGame :=
  PGame.mk {s // s ≺ t} {s // s ≺ t} (fun x ↦ posetPos x.1) (fun x ↦ posetPos x.1)
termination_by wellFounded_posetMove.wrap t
decreasing_by all_goals exact x.2

/-- The poset game, played on `α`. -/
def poset (α : Type*) [Preorder α] [WellQuasiOrderedLE α] : PGame :=
  posetPos (@univ α)

end SetTheory.PGame
