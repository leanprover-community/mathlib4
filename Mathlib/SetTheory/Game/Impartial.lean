/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.SetTheory.Game.Basic
import Mathlib.Tactic.NthRewrite

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

/-- An impartial game is one that's equivalent to its negative, such that each left and right move
is also impartial.

In such a game, both players have the same payoffs at any given moment. -/
def Impartial (G : PGame) : Prop :=
  G ≈ -G ∧ (∀ i, Impartial (G.moveLeft i)) ∧ ∀ j, Impartial (G.moveRight j)
termination_by G

theorem impartial_def {G : PGame} :
    G.Impartial ↔ (G ≈ -G) ∧ (∀ i, Impartial (G.moveLeft i)) ∧ ∀ j, Impartial (G.moveRight j) := by
  rw [Impartial]

theorem impartial_mk {G : PGame} (he : G ≈ -G)
    (hl : ∀ i, Impartial (G.moveLeft i)) (hr : ∀ j, Impartial (G.moveRight j)) : G.Impartial :=
  impartial_def.2 ⟨he, hl, hr⟩

theorem impartial_zero : Impartial 0 := by
  rw [impartial_def]
  simp

theorem impartial_star : Impartial star := by
  rw [impartial_def]
  simpa using impartial_zero

namespace Impartial

theorem neg_equiv_self {G : PGame} (h : G.Impartial) : G ≈ -G :=
  (impartial_def.1 h).1

theorem mk'_neg_equiv_self {G : PGame} (h : G.Impartial) : -(⟦G⟧ : Game) = ⟦G⟧ :=
  game_eq (Equiv.symm h.neg_equiv_self)

theorem moveLeft {G : PGame} (h : G.Impartial) (i : G.LeftMoves) :
    (G.moveLeft i).Impartial :=
  (impartial_def.1 h).2.1 i

theorem moveRight {G : PGame} (h : G.Impartial) (j : G.RightMoves) :
    (G.moveRight j).Impartial :=
  (impartial_def.1 h).2.2 j

theorem congr {G H : PGame} (e : G ≡r H) (h : G.Impartial) : H.Impartial :=
  impartial_mk
    (Equiv.trans e.symm.equiv <| Equiv.trans h.neg_equiv_self <| neg_equiv_neg_iff.2 e.equiv)
      (fun i => congr (e.moveLeftSymm i) (h.moveLeft _))
      (fun j => congr (e.moveRightSymm j) (h.moveRight _))
termination_by G

theorem add {G H : PGame} (hG : G.Impartial) (hH : H.Impartial) : (G + H).Impartial := by
  rw [impartial_def]
  refine ⟨Equiv.trans (add_congr hG.neg_equiv_self hH.neg_equiv_self)
    (Equiv.symm (negAddRelabelling _ _).equiv), ?_, ?_⟩ <;>
  intro k
  apply leftMoves_add_cases k
  on_goal 3 => apply rightMoves_add_cases k
  all_goals
    intro i
    simp only [add_moveLeft_inl, add_moveLeft_inr, add_moveRight_inl, add_moveRight_inr]
    apply add
    assumption'
  exacts [hG.moveLeft _, hH.moveLeft _, hG.moveRight _, hH.moveRight _]
termination_by (G, H)

theorem neg {G : PGame} (h : G.Impartial) : (-G).Impartial := by
  apply impartial_mk
  · rw [neg_neg]
    exact Equiv.symm h.neg_equiv_self
  · rw [moveLeft_neg]
    exact neg (h.moveRight _)
  · rw [moveRight_neg]
    exact neg (h.moveLeft _)
termination_by G

variable {G H : PGame}

theorem nonpos (hG : G.Impartial) : ¬ 0 < G := by
  intro hl
  have hg := neg_lt_neg_iff.2 hl
  rw [neg_zero, lt_congr_left (Equiv.symm hG.neg_equiv_self)] at hg
  exact hl.asymm hg

theorem nonneg (hG : G.Impartial) : ¬ G < 0 := by
  rw [← neg_lt_neg_iff, neg_zero]
  exact nonpos hG.neg

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem equiv_or_fuzzy_zero (hG : G.Impartial) : G ≈ 0 ∨ G ‖ 0 := by
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with (h | h | h | h)
  · exact (hG.nonneg h).elim
  · exact Or.inl h
  · exact (hG.nonpos h).elim
  · exact Or.inr h

theorem not_equiv_zero_iff (h : G.Impartial) : ¬ G ≈ 0 ↔ G ‖ 0 :=
  ⟨(equiv_or_fuzzy_zero h).resolve_left, Fuzzy.not_equiv⟩

theorem not_fuzzy_zero_iff (h : G.Impartial) : ¬ G ‖ 0 ↔ G ≈ 0 :=
  ⟨(equiv_or_fuzzy_zero h).resolve_right, Equiv.not_fuzzy⟩

theorem add_self (h : G.Impartial) : G + G ≈ 0 :=
  Equiv.trans (add_congr_left h.neg_equiv_self) (neg_add_cancel_equiv G)

theorem mk'_add_self (h : G.Impartial) : (⟦G⟧ : Game) + ⟦G⟧ = 0 :=
  game_eq h.add_self

/-- This lemma doesn't require `G` to be impartial. -/
theorem equiv_iff_add_equiv_zero (G : PGame) (h : H.Impartial) : (G ≈ H) ↔ (G + H ≈ 0) := by
  rw [equiv_iff_game_eq, ← add_right_cancel_iff (a := ⟦H⟧), h.mk'_add_self, ← quot_add,
    equiv_iff_game_eq, quot_zero]

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero' (h : G.Impartial) (H : PGame) : (G ≈ H) ↔ (G + H ≈ 0) := by
  rw [equiv_iff_game_eq, ← add_left_cancel_iff, h.mk'_add_self, ← quot_add, equiv_iff_game_eq,
    Eq.comm, quot_zero]

theorem le_zero_iff (hG : G.Impartial) : G ≤ 0 ↔ 0 ≤ G := by
  rw [← zero_le_neg_iff, le_congr_right hG.neg_equiv_self]

theorem lf_zero_iff (hG : G.Impartial) : G ⧏ 0 ↔ 0 ⧏ G := by
  rw [← zero_lf_neg_iff, lf_congr_right hG.neg_equiv_self]

theorem equiv_zero_iff_le (hG : G.Impartial) : G ≈ 0 ↔ G ≤ 0 :=
  ⟨And.left, fun h => ⟨h, (le_zero_iff hG).1 h⟩⟩

theorem fuzzy_zero_iff_lf (hG : G.Impartial) : G ‖ 0 ↔ G ⧏ 0 :=
  ⟨And.left, fun h => ⟨h, (lf_zero_iff hG).1 h⟩⟩

theorem equiv_zero_iff_ge (hG : G.Impartial) : G ≈ 0 ↔ 0 ≤ G :=
  ⟨And.right, fun h => ⟨(le_zero_iff hG).2 h, h⟩⟩

theorem fuzzy_zero_iff_gf (hG : G.Impartial) : G ‖ 0 ↔ 0 ⧏ G :=
  ⟨And.right, fun h => ⟨(lf_zero_iff hG).2 h, h⟩⟩

theorem forall_leftMoves_fuzzy_iff_equiv_zero (h : G.Impartial) :
    (∀ i, G.moveLeft i ‖ 0) ↔ G ≈ 0 := by
  refine ⟨fun hb => ?_, fun hp i => ?_⟩
  · rw [equiv_zero_iff_le h, le_zero_lf]
    exact fun i => (hb i).1
  · rw [fuzzy_zero_iff_lf (h.moveLeft i)]
    exact hp.1.moveLeft_lf i

theorem forall_rightMoves_fuzzy_iff_equiv_zero (h : G.Impartial) :
    (∀ j, G.moveRight j ‖ 0) ↔ G ≈ 0 := by
  refine ⟨fun hb => ?_, fun hp i => ?_⟩
  · rw [equiv_zero_iff_ge h, zero_le_lf]
    exact fun i => (hb i).2
  · rw [fuzzy_zero_iff_gf (h.moveRight i)]
    exact hp.2.lf_moveRight i

theorem exists_left_move_equiv_iff_fuzzy_zero (h : G.Impartial) :
    (∃ i, G.moveLeft i ≈ 0) ↔ G ‖ 0 := by
  refine ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_gf h).2 (lf_of_le_moveLeft hi.2), fun hn => ?_⟩
  rw [fuzzy_zero_iff_gf h, zero_lf_le] at hn
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_ge (h.moveLeft i)).2 hi⟩

theorem exists_right_move_equiv_iff_fuzzy_zero (h : G.Impartial) :
    (∃ j, G.moveRight j ≈ 0) ↔ G ‖ 0 := by
  refine ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_lf h).2 (lf_of_moveRight_le hi.1), fun hn => ?_⟩
  rw [fuzzy_zero_iff_lf h, lf_zero_le] at hn
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_le (h.moveRight _)).2 hi⟩

end Impartial

end PGame

end SetTheory
