/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.game.ordinal
! leanprover-community/mathlib commit b90e72c7eebbe8de7c8293a80208ea2ba135c834
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.SetTheory.Game.Basic
import Mathlib.SetTheory.Ordinal.NaturalOps

/-!
# Ordinals as games

We define the canonical map `ordinal → pgame`, where every ordinal is mapped to the game whose left
set consists of all previous ordinals.

The map to surreals is defined in `ordinal.to_surreal`.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.
-/


universe u

open PGame

open scoped NaturalOps PGame

namespace Ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPGame : Ordinal.{u} → PGame.{u}
  | o =>
    ⟨o.out.α, PEmpty, fun x =>
      let hwf := Ordinal.typein_lt_self x
      (typein (· < ·) x).toPGame,
      PEmpty.elim⟩
#align ordinal.to_pgame Ordinal.toPGame

theorem toPGame_def (o : Ordinal) :
    o.toPGame = ⟨o.out.α, PEmpty, fun x => (typein (· < ·) x).toPGame, PEmpty.elim⟩ := by
  rw [to_pgame]
#align ordinal.to_pgame_def Ordinal.toPGame_def

@[simp]
theorem toPGame_leftMoves (o : Ordinal) : o.toPGame.LeftMoves = o.out.α := by
  rw [to_pgame, left_moves]
#align ordinal.to_pgame_left_moves Ordinal.toPGame_leftMoves

@[simp]
theorem toPGame_rightMoves (o : Ordinal) : o.toPGame.RightMoves = PEmpty := by
  rw [to_pgame, right_moves]
#align ordinal.to_pgame_right_moves Ordinal.toPGame_rightMoves

instance isEmpty_zero_toPGame_leftMoves : IsEmpty (toPGame 0).LeftMoves := by
  rw [to_pgame_left_moves]; infer_instance
#align ordinal.is_empty_zero_to_pgame_left_moves Ordinal.isEmpty_zero_toPGame_leftMoves

instance isEmpty_toPGame_rightMoves (o : Ordinal) : IsEmpty o.toPGame.RightMoves := by
  rw [to_pgame_right_moves]; infer_instance
#align ordinal.is_empty_to_pgame_right_moves Ordinal.isEmpty_toPGame_rightMoves

/-- Converts an ordinal less than `o` into a move for the `pgame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPgame {o : Ordinal} : Set.Iio o ≃ o.toPGame.LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (toPGame_leftMoves o).symm)
#align ordinal.to_left_moves_to_pgame Ordinal.toLeftMovesToPgame

@[simp]
theorem toLeftMovesToPgame_symm_lt {o : Ordinal} (i : o.toPGame.LeftMoves) :
    ↑(toLeftMovesToPgame.symm i) < o :=
  (toLeftMovesToPgame.symm i).Prop
#align ordinal.to_left_moves_to_pgame_symm_lt Ordinal.toLeftMovesToPgame_symm_lt

theorem toPGame_moveLeft_hEq {o : Ordinal} :
    HEq o.toPGame.moveLeft fun x : o.out.α => (typein (· < ·) x).toPGame := by rw [to_pgame]; rfl
#align ordinal.to_pgame_move_left_heq Ordinal.toPGame_moveLeft_hEq

@[simp]
theorem toPGame_move_left' {o : Ordinal} (i) :
    o.toPGame.moveLeft i = (toLeftMovesToPgame.symm i).val.toPGame :=
  (congr_heq toPGame_moveLeft_hEq.symm (cast_hEq _ i)).symm
#align ordinal.to_pgame_move_left' Ordinal.toPGame_move_left'

theorem toPGame_moveLeft {o : Ordinal} (i) :
    o.toPGame.moveLeft (toLeftMovesToPgame i) = i.val.toPGame := by simp
#align ordinal.to_pgame_move_left Ordinal.toPGame_moveLeft

/-- `0.to_pgame` has the same moves as `0`. -/
noncomputable def zeroToPgameRelabelling : toPGame 0 ≡r 0 :=
  Relabelling.isEmpty _
#align ordinal.zero_to_pgame_relabelling Ordinal.zeroToPgameRelabelling

noncomputable instance uniqueOneToPgameLeftMoves : Unique (toPGame 1).LeftMoves :=
  (Equiv.cast <| toPGame_leftMoves 1).unique
#align ordinal.unique_one_to_pgame_left_moves Ordinal.uniqueOneToPgameLeftMoves

@[simp]
theorem one_toPGame_leftMoves_default_eq :
    (default : (toPGame 1).LeftMoves) = @toLeftMovesToPgame 1 ⟨0, zero_lt_one⟩ :=
  rfl
#align ordinal.one_to_pgame_left_moves_default_eq Ordinal.one_toPGame_leftMoves_default_eq

@[simp]
theorem to_leftMoves_one_toPGame_symm (i) : (@toLeftMovesToPgame 1).symm i = ⟨0, zero_lt_one⟩ := by
  simp
#align ordinal.to_left_moves_one_to_pgame_symm Ordinal.to_leftMoves_one_toPGame_symm

theorem one_toPGame_moveLeft (x) : (toPGame 1).moveLeft x = toPGame 0 := by simp
#align ordinal.one_to_pgame_move_left Ordinal.one_toPGame_moveLeft

/-- `1.to_pgame` has the same moves as `1`. -/
noncomputable def oneToPgameRelabelling : toPGame 1 ≡r 1 :=
  ⟨Equiv.equivOfUnique _ _, Equiv.equivOfIsEmpty _ _, fun i => by
    simpa using zero_to_pgame_relabelling, isEmptyElim⟩
#align ordinal.one_to_pgame_relabelling Ordinal.oneToPgameRelabelling

theorem toPGame_lf {a b : Ordinal} (h : a < b) : a.toPGame ⧏ b.toPGame := by
  convert move_left_lf (to_left_moves_to_pgame ⟨a, h⟩); rw [to_pgame_move_left]
#align ordinal.to_pgame_lf Ordinal.toPGame_lf

theorem toPGame_le {a b : Ordinal} (h : a ≤ b) : a.toPGame ≤ b.toPGame := by
  refine' le_iff_forall_lf.2 ⟨fun i => _, isEmptyElim⟩
  rw [to_pgame_move_left']
  exact to_pgame_lf ((to_left_moves_to_pgame_symm_lt i).trans_le h)
#align ordinal.to_pgame_le Ordinal.toPGame_le

theorem toPGame_lt {a b : Ordinal} (h : a < b) : a.toPGame < b.toPGame :=
  ⟨toPGame_le h.le, toPGame_lf h⟩
#align ordinal.to_pgame_lt Ordinal.toPGame_lt

theorem toPGame_nonneg (a : Ordinal) : 0 ≤ a.toPGame :=
  zeroToPgameRelabelling.ge.trans <| toPGame_le <| Ordinal.zero_le a
#align ordinal.to_pgame_nonneg Ordinal.toPGame_nonneg

@[simp]
theorem toPGame_lf_iff {a b : Ordinal} : a.toPGame ⧏ b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt, not_lf]; exact to_pgame_le, toPGame_lf⟩
#align ordinal.to_pgame_lf_iff Ordinal.toPGame_lf_iff

@[simp]
theorem toPGame_le_iff {a b : Ordinal} : a.toPGame ≤ b.toPGame ↔ a ≤ b :=
  ⟨by contrapose; rw [not_le, PGame.not_le]; exact to_pgame_lf, toPGame_le⟩
#align ordinal.to_pgame_le_iff Ordinal.toPGame_le_iff

@[simp]
theorem toPGame_lt_iff {a b : Ordinal} : a.toPGame < b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt]; exact fun h => not_lt_of_le (to_pgame_le h), toPGame_lt⟩
#align ordinal.to_pgame_lt_iff Ordinal.toPGame_lt_iff

@[simp]
theorem toPGame_equiv_iff {a b : Ordinal} : (a.toPGame ≈ b.toPGame) ↔ a = b := by
  rw [PGame.Equiv, le_antisymm_iff, to_pgame_le_iff, to_pgame_le_iff]
#align ordinal.to_pgame_equiv_iff Ordinal.toPGame_equiv_iff

theorem toPGame_injective : Function.Injective Ordinal.toPGame := fun a b h =>
  toPGame_equiv_iff.1 <| equiv_of_eq h
#align ordinal.to_pgame_injective Ordinal.toPGame_injective

@[simp]
theorem toPGame_eq_iff {a b : Ordinal} : a.toPGame = b.toPGame ↔ a = b :=
  toPGame_injective.eq_iff
#align ordinal.to_pgame_eq_iff Ordinal.toPGame_eq_iff

/-- The order embedding version of `to_pgame`. -/
@[simps]
noncomputable def toPGameEmbedding : Ordinal.{u} ↪o PGame.{u} where
  toFun := Ordinal.toPGame
  inj' := toPGame_injective
  map_rel_iff' := @toPGame_le_iff
#align ordinal.to_pgame_embedding Ordinal.toPGameEmbedding

/-- The sum of ordinals as games corresponds to natural addition of ordinals. -/
theorem toPGame_add : ∀ a b : Ordinal.{u}, a.toPGame + b.toPGame ≈ (a ♯ b).toPGame
  | a, b => by
    refine' ⟨le_of_forall_lf (fun i => _) isEmptyElim, le_of_forall_lf (fun i => _) isEmptyElim⟩
    · apply left_moves_add_cases i <;> intro i <;> let wf := to_left_moves_to_pgame_symm_lt i <;>
            try rw [add_move_left_inl] <;> try rw [add_move_left_inr] <;>
        rw [to_pgame_move_left', lf_congr_left (to_pgame_add _ _), to_pgame_lf_iff]
      · exact nadd_lt_nadd_right wf _
      · exact nadd_lt_nadd_left wf _
    · rw [to_pgame_move_left']
      rcases lt_nadd_iff.1 (to_left_moves_to_pgame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
          rw [← to_pgame_le_iff, ← le_congr_right (to_pgame_add _ _)] at hc'  <;>
        apply lf_of_le_of_lf hc'
      · apply add_lf_add_right
        rwa [to_pgame_lf_iff]
      · apply add_lf_add_left
        rwa [to_pgame_lf_iff]
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.to_pgame_add Ordinal.toPGame_add

@[simp]
theorem toPGame_add_mk' (a b : Ordinal) : ⟦a.toPGame⟧ + ⟦b.toPGame⟧ = ⟦(a ♯ b).toPGame⟧ :=
  Quot.sound (toPGame_add a b)
#align ordinal.to_pgame_add_mk Ordinal.toPGame_add_mk'

end Ordinal
