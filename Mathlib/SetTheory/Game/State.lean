/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.SetTheory.Game.Short

#align_import set_theory.game.state from "leanprover-community/mathlib"@"b134b2f5cf6dd25d4bbfd3c498b6e36c11a17225"

/-!
# Games described via "the state of the board".

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `decide`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `SetTheory/Game/Domineering` for an example using this construction.
-/

universe u

namespace SetTheory
namespace PGame

/-- `SetTheory.PGame.State S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `SetTheory.PGame.ofState s` or `SetTheory.Game.ofState s` to construct the game.

`SetTheory.PGame.State.l : S → Finset S` and `SetTheory.PGame.State.r : S → Finset S` describe
the states reachable by a move by Left or Right. `SetTheory.PGame.State.turnBound : S → ℕ`
gives an upper bound on the number of possible turns remaining from this state.
-/
class State (S : Type u) where
  turnBound : S → ℕ
  l : S → Finset S
  r : S → Finset S
  left_bound : ∀ {s t : S}, t ∈ l s → turnBound t < turnBound s
  right_bound : ∀ {s t : S}, t ∈ r s → turnBound t < turnBound s
#align pgame.state SetTheory.PGame.State

open State

variable {S : Type u} [State S]

theorem turnBound_ne_zero_of_left_move {s t : S} (m : t ∈ l s) : turnBound s ≠ 0 := by
  intro h
  have t := left_bound m
  rw [h] at t
  exact Nat.not_succ_le_zero _ t
#align pgame.turn_bound_ne_zero_of_left_move SetTheory.PGame.turnBound_ne_zero_of_left_move

theorem turnBound_ne_zero_of_right_move {s t : S} (m : t ∈ r s) : turnBound s ≠ 0 := by
  intro h
  have t := right_bound m
  rw [h] at t
  exact Nat.not_succ_le_zero _ t
#align pgame.turn_bound_ne_zero_of_right_move SetTheory.PGame.turnBound_ne_zero_of_right_move

theorem turnBound_of_left {s t : S} (m : t ∈ l s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (left_bound m) h)
#align pgame.turn_bound_of_left SetTheory.PGame.turnBound_of_left

theorem turnBound_of_right {s t : S} (m : t ∈ r s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (right_bound m) h)
#align pgame.turn_bound_of_right SetTheory.PGame.turnBound_of_right

/-- Construct a `PGame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def ofStateAux : ∀ (n : ℕ) (s : S), turnBound s ≤ n → PGame
  | 0, s, h =>
    PGame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => by exfalso; exact turnBound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h))
      fun t => by exfalso; exact turnBound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    PGame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => ofStateAux n t (turnBound_of_left t.2 n h)) fun t =>
      ofStateAux n t (turnBound_of_right t.2 n h)
#align pgame.of_state_aux SetTheory.PGame.ofStateAux

/-- Two different (valid) turn bounds give equivalent games. -/
def ofStateAuxRelabelling :
    ∀ (s : S) (n m : ℕ) (hn : turnBound s ≤ n) (hm : turnBound s ≤ m),
      Relabelling (ofStateAux n s hn) (ofStateAux m s hm)
  | s, 0, 0, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor
    · rfl
    · rfl
    · intro i; dsimp at i; exfalso
      exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    · intro j; dsimp at j; exfalso
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
  | s, 0, m + 1, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor
    · rfl
    · rfl
    · intro i; dsimp at i; exfalso
      exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    · intro j; dsimp at j; exfalso
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn)
  | s, n + 1, 0, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor
    · rfl
    · rfl
    · intro i; dsimp at i; exfalso
      exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm)
    · intro j; dsimp at j; exfalso
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
  | s, n + 1, m + 1, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor
    · rfl
    · rfl
    · intro i
      apply ofStateAuxRelabelling
    · intro j
      apply ofStateAuxRelabelling
#align pgame.of_state_aux_relabelling SetTheory.PGame.ofStateAuxRelabelling

/-- Construct a combinatorial `PGame` from a state. -/
def ofState (s : S) : PGame :=
  ofStateAux (turnBound s) s (refl _)
#align pgame.of_state SetTheory.PGame.ofState

/-- The equivalence between `leftMoves` for a `PGame` constructed using `ofStateAux _ s _`, and
`L s`. -/
def leftMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    LeftMoves (ofStateAux n s h) ≃ { t // t ∈ l s } := by induction n <;> rfl
#align pgame.left_moves_of_state_aux SetTheory.PGame.leftMovesOfStateAux

/-- The equivalence between `leftMoves` for a `PGame` constructed using `ofState s`, and `l s`. -/
def leftMovesOfState (s : S) : LeftMoves (ofState s) ≃ { t // t ∈ l s } :=
  leftMovesOfStateAux _ _
#align pgame.left_moves_of_state SetTheory.PGame.leftMovesOfState

/-- The equivalence between `rightMoves` for a `PGame` constructed using `ofStateAux _ s _`, and
`R s`. -/
def rightMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    RightMoves (ofStateAux n s h) ≃ { t // t ∈ r s } := by induction n <;> rfl
#align pgame.right_moves_of_state_aux SetTheory.PGame.rightMovesOfStateAux

/-- The equivalence between `rightMoves` for a `PGame` constructed using `ofState s`, and
`R s`. -/
def rightMovesOfState (s : S) : RightMoves (ofState s) ≃ { t // t ∈ r s } :=
  rightMovesOfStateAux _ _
#align pgame.right_moves_of_state SetTheory.PGame.rightMovesOfState

/-- The relabelling showing `moveLeft` applied to a game constructed using `ofStateAux`
has itself been constructed using `ofStateAux`.
-/
def relabellingMoveLeftAux (n : ℕ) {s : S} (h : turnBound s ≤ n)
    (t : LeftMoves (ofStateAux n s h)) :
    Relabelling (moveLeft (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((leftMovesOfStateAux n h) t : S)
        (turnBound_of_left ((leftMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) := by
  induction n
  · have t' := (leftMovesOfStateAux 0 h) t
    exfalso; exact turnBound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl
#align pgame.relabelling_move_left_aux SetTheory.PGame.relabellingMoveLeftAux

/-- The relabelling showing `moveLeft` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveLeft (s : S) (t : LeftMoves (ofState s)) :
    Relabelling (moveLeft (ofState s) t) (ofState ((leftMovesOfState s).toFun t : S)) := by
  trans
  · apply relabellingMoveLeftAux
  · apply ofStateAuxRelabelling
#align pgame.relabelling_move_left SetTheory.PGame.relabellingMoveLeft

/-- The relabelling showing `moveRight` applied to a game constructed using `ofStateAux`
has itself been constructed using `ofStateAux`.
-/
def relabellingMoveRightAux (n : ℕ) {s : S} (h : turnBound s ≤ n)
    (t : RightMoves (ofStateAux n s h)) :
    Relabelling (moveRight (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((rightMovesOfStateAux n h) t : S)
        (turnBound_of_right ((rightMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) := by
  induction n
  · have t' := (rightMovesOfStateAux 0 h) t
    exfalso; exact turnBound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl
#align pgame.relabelling_move_right_aux SetTheory.PGame.relabellingMoveRightAux

/-- The relabelling showing `moveRight` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveRight (s : S) (t : RightMoves (ofState s)) :
    Relabelling (moveRight (ofState s) t) (ofState ((rightMovesOfState s).toFun t : S)) := by
  trans
  · apply relabellingMoveRightAux
  · apply ofStateAuxRelabelling
#align pgame.relabelling_move_right SetTheory.PGame.relabellingMoveRight

instance fintypeLeftMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (LeftMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (leftMovesOfStateAux _ _).symm
#align pgame.fintype_left_moves_of_state_aux SetTheory.PGame.fintypeLeftMovesOfStateAux

instance fintypeRightMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (RightMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (rightMovesOfStateAux _ _).symm
#align pgame.fintype_right_moves_of_state_aux SetTheory.PGame.fintypeRightMovesOfStateAux

instance shortOfStateAux : ∀ (n : ℕ) {s : S} (h : turnBound s ≤ n), Short (ofStateAux n s h)
  | 0, s, h =>
    Short.mk'
      (fun i => by
        have i := (leftMovesOfStateAux _ _).toFun i
        exfalso
        exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
      fun j => by
      have j := (rightMovesOfStateAux _ _).toFun j
      exfalso
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    Short.mk'
      (fun i =>
        shortOfRelabelling (relabellingMoveLeftAux (n + 1) h i).symm (shortOfStateAux n _))
      fun j =>
      shortOfRelabelling (relabellingMoveRightAux (n + 1) h j).symm (shortOfStateAux n _)
#align pgame.short_of_state_aux SetTheory.PGame.shortOfStateAux

instance shortOfState (s : S) : Short (ofState s) := by
  dsimp [PGame.ofState]
  infer_instance
#align pgame.short_of_state SetTheory.PGame.shortOfState

end PGame

namespace Game

/-- Construct a combinatorial `Game` from a state. -/
def ofState {S : Type u} [PGame.State S] (s : S) : Game :=
  ⟦PGame.ofState s⟧
#align game.of_state SetTheory.Game.ofState

end Game
