/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.SetTheory.Game.Basic
import Mathlib.Tactic.NthRewrite

#align_import set_theory.game.impartial from "leanprover-community/mathlib"@"2e0975f6a25dd3fbfb9e41556a77f075f6269748"

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classified as
impartial.
-/


universe u

namespace SetTheory

open scoped PGame

namespace PGame

/-- The definition for an impartial game, defined using Conway induction. -/
def ImpartialAux : PGame → Prop
  | G => (G ≈ -G) ∧ (∀ i, ImpartialAux (G.moveLeft i)) ∧ ∀ j, ImpartialAux (G.moveRight j)
termination_by G => G -- Porting note: Added `termination_by`
#align pgame.impartial_aux SetTheory.PGame.ImpartialAux

theorem impartialAux_def {G : PGame} :
    G.ImpartialAux ↔
      (G ≈ -G) ∧ (∀ i, ImpartialAux (G.moveLeft i)) ∧ ∀ j, ImpartialAux (G.moveRight j) := by
  rw [ImpartialAux]
#align pgame.impartial_aux_def SetTheory.PGame.impartialAux_def

/-- A typeclass on impartial games. -/
class Impartial (G : PGame) : Prop where
  out : ImpartialAux G
#align pgame.impartial SetTheory.PGame.Impartial

theorem impartial_iff_aux {G : PGame} : G.Impartial ↔ G.ImpartialAux :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align pgame.impartial_iff_aux SetTheory.PGame.impartial_iff_aux

theorem impartial_def {G : PGame} :
    G.Impartial ↔ (G ≈ -G) ∧ (∀ i, Impartial (G.moveLeft i)) ∧ ∀ j, Impartial (G.moveRight j) := by
  simpa only [impartial_iff_aux] using impartialAux_def
#align pgame.impartial_def SetTheory.PGame.impartial_def

namespace Impartial

instance impartial_zero : Impartial 0 := by rw [impartial_def]; dsimp; simp
#align pgame.impartial.impartial_zero SetTheory.PGame.Impartial.impartial_zero

instance impartial_star : Impartial star := by
  rw [impartial_def]; simpa using Impartial.impartial_zero
#align pgame.impartial.impartial_star SetTheory.PGame.Impartial.impartial_star

theorem neg_equiv_self (G : PGame) [h : G.Impartial] : G ≈ -G :=
  (impartial_def.1 h).1
#align pgame.impartial.neg_equiv_self SetTheory.PGame.Impartial.neg_equiv_self

-- Porting note: Changed `-⟦G⟧` to `-(⟦G⟧ : Quotient setoid)`
@[simp]
theorem mk'_neg_equiv_self (G : PGame) [G.Impartial] : -(⟦G⟧ : Quotient setoid) = ⟦G⟧ :=
  Quot.sound (Equiv.symm (neg_equiv_self G))
#align pgame.impartial.mk_neg_equiv_self SetTheory.PGame.Impartial.mk'_neg_equiv_self

instance moveLeft_impartial {G : PGame} [h : G.Impartial] (i : G.LeftMoves) :
    (G.moveLeft i).Impartial :=
  (impartial_def.1 h).2.1 i
#align pgame.impartial.move_left_impartial SetTheory.PGame.Impartial.moveLeft_impartial

instance moveRight_impartial {G : PGame} [h : G.Impartial] (j : G.RightMoves) :
    (G.moveRight j).Impartial :=
  (impartial_def.1 h).2.2 j
#align pgame.impartial.move_right_impartial SetTheory.PGame.Impartial.moveRight_impartial

theorem impartial_congr : ∀ {G H : PGame} (_ : G ≡r H) [G.Impartial], H.Impartial
  | G, H => fun e => by
    intro h
    exact impartial_def.2
      ⟨Equiv.trans e.symm.equiv (Equiv.trans (neg_equiv_self G) (neg_equiv_neg_iff.2 e.equiv)),
        fun i => impartial_congr (e.moveLeftSymm i), fun j => impartial_congr (e.moveRightSymm j)⟩
termination_by G H => (G, H)
#align pgame.impartial.impartial_congr SetTheory.PGame.Impartial.impartial_congr

instance impartial_add : ∀ (G H : PGame) [G.Impartial] [H.Impartial], (G + H).Impartial
  | G, H, _, _ => by
    rw [impartial_def]
    refine ⟨Equiv.trans (add_congr (neg_equiv_self G) (neg_equiv_self _))
        (Equiv.symm (negAddRelabelling _ _).equiv), fun k => ?_, fun k => ?_⟩
    · apply leftMoves_add_cases k
      all_goals
        intro i; simp only [add_moveLeft_inl, add_moveLeft_inr]
        apply impartial_add
    · apply rightMoves_add_cases k
      all_goals
        intro i; simp only [add_moveRight_inl, add_moveRight_inr]
        apply impartial_add
termination_by G H => (G, H)
#align pgame.impartial.impartial_add SetTheory.PGame.Impartial.impartial_add

instance impartial_neg : ∀ (G : PGame) [G.Impartial], (-G).Impartial
  | G, _ => by
    rw [impartial_def]
    refine ⟨?_, fun i => ?_, fun i => ?_⟩
    · rw [neg_neg]
      exact Equiv.symm (neg_equiv_self G)
    · rw [moveLeft_neg']
      apply impartial_neg
    · rw [moveRight_neg']
      apply impartial_neg
termination_by G => G
#align pgame.impartial.impartial_neg SetTheory.PGame.Impartial.impartial_neg

variable (G : PGame) [Impartial G]

theorem nonpos : ¬0 < G := fun h => by
  have h' := neg_lt_neg_iff.2 h
  rw [neg_zero, lt_congr_left (Equiv.symm (neg_equiv_self G))] at h'
  exact (h.trans h').false
#align pgame.impartial.nonpos SetTheory.PGame.Impartial.nonpos

theorem nonneg : ¬G < 0 := fun h => by
  have h' := neg_lt_neg_iff.2 h
  rw [neg_zero, lt_congr_right (Equiv.symm (neg_equiv_self G))] at h'
  exact (h.trans h').false
#align pgame.impartial.nonneg SetTheory.PGame.Impartial.nonneg

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem equiv_or_fuzzy_zero : (G ≈ 0) ∨ G ‖ 0 := by
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with (h | h | h | h)
  · exact ((nonneg G) h).elim
  · exact Or.inl h
  · exact ((nonpos G) h).elim
  · exact Or.inr h
#align pgame.impartial.equiv_or_fuzzy_zero SetTheory.PGame.Impartial.equiv_or_fuzzy_zero

@[simp]
theorem not_equiv_zero_iff : ¬(G ≈ 0) ↔ G ‖ 0 :=
  ⟨(equiv_or_fuzzy_zero G).resolve_left, Fuzzy.not_equiv⟩
#align pgame.impartial.not_equiv_zero_iff SetTheory.PGame.Impartial.not_equiv_zero_iff

@[simp]
theorem not_fuzzy_zero_iff : ¬G ‖ 0 ↔ (G ≈ 0) :=
  ⟨(equiv_or_fuzzy_zero G).resolve_right, Equiv.not_fuzzy⟩
#align pgame.impartial.not_fuzzy_zero_iff SetTheory.PGame.Impartial.not_fuzzy_zero_iff

theorem add_self : G + G ≈ 0 :=
  Equiv.trans (add_congr_left (neg_equiv_self G)) (add_left_neg_equiv G)
#align pgame.impartial.add_self SetTheory.PGame.Impartial.add_self

-- Porting note: Changed `⟦G⟧` to `(⟦G⟧ : Quotient setoid)`
@[simp]
theorem mk'_add_self : (⟦G⟧ : Quotient setoid) + ⟦G⟧ = 0 :=
  Quot.sound (add_self G)
#align pgame.impartial.mk_add_self SetTheory.PGame.Impartial.mk'_add_self

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero (H : PGame) : (H ≈ G) ↔ (H + G ≈ 0) := by
  rw [Game.PGame.equiv_iff_game_eq, ← @add_right_cancel_iff _ _ _ ⟦G⟧, mk'_add_self, ← quot_add,
    Game.PGame.equiv_iff_game_eq]
  rfl
#align pgame.impartial.equiv_iff_add_equiv_zero SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero' (H : PGame) : (G ≈ H) ↔ (G + H ≈ 0) := by
  rw [Game.PGame.equiv_iff_game_eq, ← @add_left_cancel_iff _ _ _ ⟦G⟧, mk'_add_self, ← quot_add,
    Game.PGame.equiv_iff_game_eq]
  exact ⟨Eq.symm, Eq.symm⟩
#align pgame.impartial.equiv_iff_add_equiv_zero' SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero'

theorem le_zero_iff {G : PGame} [G.Impartial] : G ≤ 0 ↔ 0 ≤ G := by
  rw [← zero_le_neg_iff, le_congr_right (neg_equiv_self G)]
#align pgame.impartial.le_zero_iff SetTheory.PGame.Impartial.le_zero_iff

theorem lf_zero_iff {G : PGame} [G.Impartial] : G ⧏ 0 ↔ 0 ⧏ G := by
  rw [← zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]
#align pgame.impartial.lf_zero_iff SetTheory.PGame.Impartial.lf_zero_iff

theorem equiv_zero_iff_le : (G ≈ 0) ↔ G ≤ 0 :=
  ⟨And.left, fun h => ⟨h, le_zero_iff.1 h⟩⟩
#align pgame.impartial.equiv_zero_iff_le SetTheory.PGame.Impartial.equiv_zero_iff_le

theorem fuzzy_zero_iff_lf : G ‖ 0 ↔ G ⧏ 0 :=
  ⟨And.left, fun h => ⟨h, lf_zero_iff.1 h⟩⟩
#align pgame.impartial.fuzzy_zero_iff_lf SetTheory.PGame.Impartial.fuzzy_zero_iff_lf

theorem equiv_zero_iff_ge : (G ≈ 0) ↔ 0 ≤ G :=
  ⟨And.right, fun h => ⟨le_zero_iff.2 h, h⟩⟩
#align pgame.impartial.equiv_zero_iff_ge SetTheory.PGame.Impartial.equiv_zero_iff_ge

theorem fuzzy_zero_iff_gf : G ‖ 0 ↔ 0 ⧏ G :=
  ⟨And.right, fun h => ⟨lf_zero_iff.2 h, h⟩⟩
#align pgame.impartial.fuzzy_zero_iff_gf SetTheory.PGame.Impartial.fuzzy_zero_iff_gf

theorem forall_leftMoves_fuzzy_iff_equiv_zero : (∀ i, G.moveLeft i ‖ 0) ↔ (G ≈ 0) := by
  refine ⟨fun hb => ?_, fun hp i => ?_⟩
  · rw [equiv_zero_iff_le G, le_zero_lf]
    exact fun i => (hb i).1
  · rw [fuzzy_zero_iff_lf]
    exact hp.1.moveLeft_lf i
#align pgame.impartial.forall_left_moves_fuzzy_iff_equiv_zero SetTheory.PGame.Impartial.forall_leftMoves_fuzzy_iff_equiv_zero

theorem forall_rightMoves_fuzzy_iff_equiv_zero : (∀ j, G.moveRight j ‖ 0) ↔ (G ≈ 0) := by
  refine ⟨fun hb => ?_, fun hp i => ?_⟩
  · rw [equiv_zero_iff_ge G, zero_le_lf]
    exact fun i => (hb i).2
  · rw [fuzzy_zero_iff_gf]
    exact hp.2.lf_moveRight i
#align pgame.impartial.forall_right_moves_fuzzy_iff_equiv_zero SetTheory.PGame.Impartial.forall_rightMoves_fuzzy_iff_equiv_zero

theorem exists_left_move_equiv_iff_fuzzy_zero : (∃ i, G.moveLeft i ≈ 0) ↔ G ‖ 0 := by
  refine ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_gf G).2 (lf_of_le_moveLeft hi.2), fun hn => ?_⟩
  rw [fuzzy_zero_iff_gf G, zero_lf_le] at hn
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_ge _).2 hi⟩
#align pgame.impartial.exists_left_move_equiv_iff_fuzzy_zero SetTheory.PGame.Impartial.exists_left_move_equiv_iff_fuzzy_zero

theorem exists_right_move_equiv_iff_fuzzy_zero : (∃ j, G.moveRight j ≈ 0) ↔ G ‖ 0 := by
  refine ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_lf G).2 (lf_of_moveRight_le hi.1), fun hn => ?_⟩
  rw [fuzzy_zero_iff_lf G, lf_zero_le] at hn
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_le _).2 hi⟩
#align pgame.impartial.exists_right_move_equiv_iff_fuzzy_zero SetTheory.PGame.Impartial.exists_right_move_equiv_iff_fuzzy_zero

end Impartial

end PGame
