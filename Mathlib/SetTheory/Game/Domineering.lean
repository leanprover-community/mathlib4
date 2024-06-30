/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.SetTheory.Game.State

#align_import set_theory.game.domineering from "leanprover-community/mathlib"@"b134b2f5cf6dd25d4bbfd3c498b6e36c11a17225"

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/

namespace SetTheory

namespace PGame

namespace Domineering

open Function

/-- The equivalence `(x, y) ↦ (x, y+1)`. -/
@[simps!]
def shiftUp : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.refl ℤ).prodCongr (Equiv.addRight (1 : ℤ))
#align pgame.domineering.shift_up SetTheory.PGame.Domineering.shiftUp

/-- The equivalence `(x, y) ↦ (x+1, y)`. -/
@[simps!]
def shiftRight : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.addRight (1 : ℤ)).prodCongr (Equiv.refl ℤ)
#align pgame.domineering.shift_right SetTheory.PGame.Domineering.shiftRight

/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
-- Porting note: reducibility cannot be `local`. For now there are no dependents of this file so
-- being globally reducible is fine.
abbrev Board :=
  Finset (ℤ × ℤ)
#align pgame.domineering.board SetTheory.PGame.Domineering.Board

/-- Left can play anywhere that a square and the square below it are open. -/
def left (b : Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shiftUp
#align pgame.domineering.left SetTheory.PGame.Domineering.left

/-- Right can play anywhere that a square and the square to the left are open. -/
def right (b : Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shiftRight
#align pgame.domineering.right SetTheory.PGame.Domineering.right

theorem mem_left {b : Board} (x : ℤ × ℤ) : x ∈ left b ↔ x ∈ b ∧ (x.1, x.2 - 1) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)
#align pgame.domineering.mem_left SetTheory.PGame.Domineering.mem_left

theorem mem_right {b : Board} (x : ℤ × ℤ) : x ∈ right b ↔ x ∈ b ∧ (x.1 - 1, x.2) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)
#align pgame.domineering.mem_right SetTheory.PGame.Domineering.mem_right

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def moveLeft (b : Board) (m : ℤ × ℤ) : Board :=
  (b.erase m).erase (m.1, m.2 - 1)
#align pgame.domineering.move_left SetTheory.PGame.Domineering.moveLeft

/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def moveRight (b : Board) (m : ℤ × ℤ) : Board :=
  (b.erase m).erase (m.1 - 1, m.2)
#align pgame.domineering.move_right SetTheory.PGame.Domineering.moveRight

theorem fst_pred_mem_erase_of_mem_right {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    (m.1 - 1, m.2) ∈ b.erase m := by
  rw [mem_right] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.fst (pred_ne_self m.1)
#align pgame.domineering.fst_pred_mem_erase_of_mem_right SetTheory.PGame.Domineering.fst_pred_mem_erase_of_mem_right

theorem snd_pred_mem_erase_of_mem_left {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    (m.1, m.2 - 1) ∈ b.erase m := by
  rw [mem_left] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.snd (pred_ne_self m.2)
#align pgame.domineering.snd_pred_mem_erase_of_mem_left SetTheory.PGame.Domineering.snd_pred_mem_erase_of_mem_left

theorem card_of_mem_left {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) : 2 ≤ Finset.card b := by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ : (m.1, m.2 - 1) ∈ b.erase m := snd_pred_mem_erase_of_mem_left h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_lt i₂ i₁
#align pgame.domineering.card_of_mem_left SetTheory.PGame.Domineering.card_of_mem_left

theorem card_of_mem_right {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) : 2 ≤ Finset.card b := by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ := fst_pred_mem_erase_of_mem_right h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_lt i₂ i₁
#align pgame.domineering.card_of_mem_right SetTheory.PGame.Domineering.card_of_mem_right

theorem moveLeft_card {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    Finset.card (moveLeft b m) + 2 = Finset.card b := by
  dsimp [moveLeft]
  rw [Finset.card_erase_of_mem (snd_pred_mem_erase_of_mem_left h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_left h)
#align pgame.domineering.move_left_card SetTheory.PGame.Domineering.moveLeft_card

theorem moveRight_card {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    Finset.card (moveRight b m) + 2 = Finset.card b := by
  dsimp [moveRight]
  rw [Finset.card_erase_of_mem (fst_pred_mem_erase_of_mem_right h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_right h)
#align pgame.domineering.move_right_card SetTheory.PGame.Domineering.moveRight_card

theorem moveLeft_smaller {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    Finset.card (moveLeft b m) / 2 < Finset.card b / 2 := by simp [← moveLeft_card h, lt_add_one]
#align pgame.domineering.move_left_smaller SetTheory.PGame.Domineering.moveLeft_smaller

theorem moveRight_smaller {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    Finset.card (moveRight b m) / 2 < Finset.card b / 2 := by simp [← moveRight_card h, lt_add_one]
#align pgame.domineering.move_right_smaller SetTheory.PGame.Domineering.moveRight_smaller

/-- The instance describing allowed moves on a Domineering board. -/
instance state : State Board where
  turnBound s := s.card / 2
  l s := (left s).image (moveLeft s)
  r s := (right s).image (moveRight s)
  left_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact moveLeft_smaller h
  right_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact moveRight_smaller h
#align pgame.domineering.state SetTheory.PGame.Domineering.state

end Domineering

/-- Construct a pre-game from a Domineering board. -/
def domineering (b : Domineering.Board) : PGame :=
  PGame.ofState b
#align pgame.domineering SetTheory.PGame.domineering

/-- All games of Domineering are short, because each move removes two squares. -/
instance shortDomineering (b : Domineering.Board) : Short (domineering b) := by
  dsimp [domineering]
  infer_instance
#align pgame.short_domineering SetTheory.PGame.shortDomineering

/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def domineering.one :=
  domineering [(0, 0), (0, 1)].toFinset
#align pgame.domineering.one SetTheory.PGame.domineering.one

/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def domineering.L :=
  domineering [(0, 2), (0, 1), (0, 0), (1, 0)].toFinset
set_option linter.uppercaseLean3 false in
#align pgame.domineering.L SetTheory.PGame.domineering.L

instance shortOne : Short domineering.one := by dsimp [domineering.one]; infer_instance
#align pgame.short_one SetTheory.PGame.shortOne

instance shortL : Short domineering.L := by dsimp [domineering.L]; infer_instance
set_option linter.uppercaseLean3 false in
#align pgame.short_L SetTheory.PGame.shortL

-- The VM can play small games successfully:
-- #eval decide (domineering.one ≈ 1)
-- #eval decide (domineering.L + domineering.L ≈ 1)
-- The following no longer works since Lean 3.29, since definitions by well-founded
-- recursion no longer reduce definitionally.
-- We can check that `Decidable` instances reduce as expected,
-- and so our implementation of domineering is computable.
-- run_cmd tactic.whnf `(by apply_instance : Decidable (domineering.one ≤ 1)) >>= tactic.trace
-- dec_trivial can handle most of the dictionary of small games described in [conway2001]
-- example : domineering.one ≈ 1 := by decide
-- example : domineering.L + domineering.L ≈ 1 := by decide
-- example : domineering.L ≈ PGame.ofLists [0] [1] := by decide
-- example : (domineering ([(0,0), (0,1), (0,2), (0,3)].toFinset) ≈ 2) := by decide
-- example : (domineering ([(0,0), (0,1), (1,0), (1,1)].toFinset) ≈ PGame.ofLists [1] [-1]) :=
--   by decide
-- The 3x3 grid is doable, but takes a minute...
-- example :
--   (domineering ([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)].toFinset) ≈
--     PGame.ofLists [1] [-1]) := by decide
-- The 5x5 grid is actually 0, but brute-forcing this is too challenging even for the VM.
-- #eval decide (domineering ([
--   (0,0), (0,1), (0,2), (0,3), (0,4),
--   (1,0), (1,1), (1,2), (1,3), (1,4),
--   (2,0), (2,1), (2,2), (2,3), (2,4),
--   (3,0), (3,1), (3,2), (3,3), (3,4),
--   (4,0), (4,1), (4,2), (4,3), (4,4)
--   ].toFinset) ≈ 0)
end PGame
