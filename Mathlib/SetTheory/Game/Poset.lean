/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.WellQuasiOrder
import Mathlib.SetTheory.Game.Impartial

/-!
# Poset games
-/

variable {α : Type*} [Preorder α]

open Set

/-- A valid move in the poset game is to change set `t` to set `s`, whenever `s = t \ Ici a` for
some `a ∈ s`.

In a WQO, this relation is well-founded. -/
def posetMove (s t : Set α) : Prop :=
  ∃ a ∈ t, s = t \ Ici a

@[inherit_doc]
local infixl:50 " ≺ " => posetMove

theorem subrelation_posetMove : @Subrelation (Set α) (· ≺ ·) (· ⊂ ·) := by
  rintro x y ⟨a, ha, rfl⟩
  refine ⟨diff_subset, not_subset.2 ⟨a, ha, ?_⟩⟩
  simp

theorem not_posetMove_empty (s : Set α) : ¬ s ≺ ∅ := by
  simp [posetMove]

theorem posetMove_irrefl (s : Set α) : ¬ s ≺ s :=
  fun h ↦ ssubset_irrefl s <| subrelation_posetMove h

instance : IsIrrefl (Set α) (· ≺ ·) where
  irrefl := posetMove_irrefl

theorem wellFounded_posetMove [WellQuasiOrderedLE α] : @WellFounded (Set α) (· ≺ ·) := by
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  have hf' := hf -- Is there a way to make `choose` not delete my hypothesis?
  choose g hg using hf
  obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le g
  let f' := @RelEmbedding.natGT _ (· < ·) _ f fun n ↦ subrelation_posetMove (hf' n)
  have : g n ∈ f (m + 1) := by
    obtain rfl | h := h.nat_succ_le.eq_or_lt
    · exact (hg _).1
    · exact (f'.map_rel_iff.2 h).le (hg n).1
  rw [(hg m).2, mem_diff] at this
  exact this.2 h'

instance [WellQuasiOrderedLE α] : IsWellFounded (Set α) (· ≺ ·) :=
  ⟨wellFounded_posetMove⟩

namespace SetTheory.PGame

variable [WellQuasiOrderedLE α]

/-- A position in the poset game. A valid move in the poset game is to change set `t` to set `s`,
whenever `s = t \ Ici a` for some `a ∈ t`.

See also `posetMove`. -/
def posetPos [WellQuasiOrderedLE α] (t : Set α) : PGame :=
  PGame.mk {s // s ≺ t} {s // s ≺ t} (fun x ↦ posetPos x.1) (fun x ↦ posetPos x.1)
termination_by wellFounded_posetMove.wrap t
decreasing_by all_goals exact x.2

/-- The poset game, played on `α`. -/
@[reducible]
def poset (α : Type*) [Preorder α] [WellQuasiOrderedLE α] : PGame :=
  posetPos (@univ α)

/-- Use `toLeftMovesPoset` to cast between these two types. -/
theorem leftMoves_posetPos (t : Set α) : (posetPos t).LeftMoves = {s // s ≺ t} := by
  rw [posetPos]; rfl

/-- Use `toRightMovesPoset` to cast between these two types. -/
theorem rightMoves_posetPos (t : Set α) : (posetPos t).RightMoves = {s // s ≺ t} := by
  rw [posetPos]; rfl

theorem moveLeft_poset_heq {t : Set α} :
    HEq (posetPos t).moveLeft fun i : {s // s ≺ t} ↦ posetPos i.1 := by
  rw [posetPos]; rfl

theorem moveRight_poset_heq {t : Set α} :
    HEq (posetPos t).moveRight fun i : {s // s ≺ t} ↦ posetPos i.1 := by
  rw [posetPos]; rfl

/-- Turns a set into a left move for a poset game and viceversa. -/
def toLeftMovesPoset {t : Set α} : {s // s ≺ t} ≃ (posetPos t).LeftMoves :=
  Equiv.cast (leftMoves_posetPos t).symm

/-- Turns a set into a left move for a poset game and viceversa. -/
def toRightMovesPoset {t : Set α} : {s // s ≺ t} ≃ (posetPos t).RightMoves :=
  Equiv.cast (rightMoves_posetPos t).symm

@[simp]
theorem toLeftMovesPoset_symm_prop {t : Set α} (i : (posetPos t).LeftMoves) :
    toLeftMovesPoset.symm i ≺ t :=
  (toLeftMovesPoset.symm i).prop

@[simp]
theorem toRightMovesPoset_symm_prop {t : Set α} (i : (posetPos t).RightMoves) :
    toRightMovesPoset.symm i ≺ t :=
  (toRightMovesPoset.symm i).prop

@[simp]
theorem moveLeft_poset {t : Set α} (i) :
    (posetPos t).moveLeft i = posetPos (toLeftMovesPoset.symm i).1 := by
  apply congr_heq moveLeft_poset_heq (cast_heq _ _).symm

@[simp]
theorem moveRight_poset {t : Set α} (i) :
    (posetPos t).moveRight i = posetPos (toRightMovesPoset.symm i).1 := by
  apply congr_heq moveRight_poset_heq (cast_heq _ _).symm

@[simp]
theorem neg_posetPos (s : Set α) : -posetPos s = posetPos s := by
  rw [posetPos, neg_def]
  congr <;> ext x <;> rw [neg_posetPos]
termination_by wellFounded_posetMove.wrap s
decreasing_by all_goals exact x.2

instance impartial_posetPos (s : Set α) : Impartial (posetPos s) := by
  rw [impartial_def, neg_posetPos]
  refine ⟨equiv_rfl, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [moveLeft_poset]
    exact impartial_posetPos _
  · rw [moveRight_poset]
    exact impartial_posetPos _
termination_by wellFounded_posetMove.wrap s
decreasing_by
· exact toLeftMovesPoset_symm_prop _
· exact toRightMovesPoset_symm_prop _

end SetTheory.PGame
