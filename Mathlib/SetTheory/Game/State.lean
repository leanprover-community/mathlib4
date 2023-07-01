/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module set_theory.game.state
! leanprover-community/mathlib commit b134b2f5cf6dd25d4bbfd3c498b6e36c11a17225
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.SetTheory.Game.Short

/-!
# Games described via "the state of the board".

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `dec_trivial`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `set_theory/game/domineering` for an example using this construction.
-/


universe u

namespace PGame

/-- `pgame_state S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `pgame.of_state s` or `game.of_state s` to construct the game.

`pgame_state.L : S → finset S` and `pgame_state.R : S → finset S` describe the states reachable
by a move by Left or Right. `pgame_state.turn_bound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class State (S : Type u) where
  turnBound : S → ℕ
  l : S → Finset S
  r : S → Finset S
  left_bound : ∀ {s t : S} (m : t ∈ L s), turn_bound t < turn_bound s
  right_bound : ∀ {s t : S} (m : t ∈ R s), turn_bound t < turn_bound s
#align pgame.state PGame.State

open StateM

variable {S : Type u} [State S]

theorem turnBound_ne_zero_of_left_move {s t : S} (m : t ∈ l s) : turnBound s ≠ 0 := by
  intro h
  have t := state.left_bound m
  rw [h] at t 
  exact Nat.not_succ_le_zero _ t
#align pgame.turn_bound_ne_zero_of_left_move PGame.turnBound_ne_zero_of_left_move

theorem turnBound_ne_zero_of_right_move {s t : S} (m : t ∈ r s) : turnBound s ≠ 0 := by
  intro h
  have t := state.right_bound m
  rw [h] at t 
  exact Nat.not_succ_le_zero _ t
#align pgame.turn_bound_ne_zero_of_right_move PGame.turnBound_ne_zero_of_right_move

theorem turnBound_of_left {s t : S} (m : t ∈ l s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (left_bound m) h)
#align pgame.turn_bound_of_left PGame.turnBound_of_left

theorem turnBound_of_right {s t : S} (m : t ∈ r s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (right_bound m) h)
#align pgame.turn_bound_of_right PGame.turnBound_of_right

/-- Construct a `pgame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def ofStateAux : ∀ (n : ℕ) (s : S) (h : turnBound s ≤ n), PGame
  | 0, s, h =>
    PGame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => by exfalso; exact turn_bound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h))
      fun t => by exfalso; exact turn_bound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    PGame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => of_state_aux n t (turnBound_of_left t.2 n h)) fun t =>
      of_state_aux n t (turnBound_of_right t.2 n h)
#align pgame.of_state_aux PGame.ofStateAux

/-- Two different (valid) turn bounds give equivalent games. -/
def ofStateAuxRelabelling :
    ∀ (s : S) (n m : ℕ) (hn : turnBound s ≤ n) (hm : turnBound s ≤ m),
      Relabelling (ofStateAux n s hn) (ofStateAux m s hm)
  | s, 0, 0, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i; dsimp at i ; exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    · intro j; dsimp at j ; exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
  | s, 0, m + 1, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i; dsimp at i ; exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    · intro j; dsimp at j ; exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn)
  | s, n + 1, 0, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i; dsimp at i ; exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm)
    · intro j; dsimp at j ; exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
  | s, n + 1, m + 1, hn, hm => by
    dsimp [PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i
      apply of_state_aux_relabelling
    · intro j
      apply of_state_aux_relabelling
#align pgame.of_state_aux_relabelling PGame.ofStateAuxRelabelling

/-- Construct a combinatorial `pgame` from a state. -/
def ofState (s : S) : PGame :=
  ofStateAux (turnBound s) s (refl _)
#align pgame.of_state PGame.ofState

/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`L s`. -/
def leftMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    LeftMoves (ofStateAux n s h) ≃ { t // t ∈ l s } := by induction n <;> rfl
#align pgame.left_moves_of_state_aux PGame.leftMovesOfStateAux

/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state s`, and `L s`. -/
def leftMovesOfState (s : S) : LeftMoves (ofState s) ≃ { t // t ∈ l s } :=
  leftMovesOfStateAux _ _
#align pgame.left_moves_of_state PGame.leftMovesOfState

/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`R s`. -/
def rightMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    RightMoves (ofStateAux n s h) ≃ { t // t ∈ r s } := by induction n <;> rfl
#align pgame.right_moves_of_state_aux PGame.rightMovesOfStateAux

/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state s`, and
`R s`. -/
def rightMovesOfState (s : S) : RightMoves (ofState s) ≃ { t // t ∈ r s } :=
  rightMovesOfStateAux _ _
#align pgame.right_moves_of_state PGame.rightMovesOfState

/-- The relabelling showing `move_left` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def relabellingMoveLeftAux (n : ℕ) {s : S} (h : turnBound s ≤ n)
    (t : LeftMoves (ofStateAux n s h)) :
    Relabelling (moveLeft (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((leftMovesOfStateAux n h) t : S)
        (turnBound_of_left ((leftMovesOfStateAux n h) t).2 (n - 1) (Nat.le_trans h le_tsub_add))) :=
  by
  induction n
  · have t' := (left_moves_of_state_aux 0 h) t
    exfalso; exact turn_bound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl
#align pgame.relabelling_move_left_aux PGame.relabellingMoveLeftAux

/-- The relabelling showing `move_left` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveLeft (s : S) (t : LeftMoves (ofState s)) :
    Relabelling (moveLeft (ofState s) t) (ofState ((leftMovesOfState s).toFun t : S)) := by
  trans
  apply relabelling_move_left_aux
  apply of_state_aux_relabelling
#align pgame.relabelling_move_left PGame.relabellingMoveLeft

/-- The relabelling showing `move_right` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def relabellingMoveRightAux (n : ℕ) {s : S} (h : turnBound s ≤ n)
    (t : RightMoves (ofStateAux n s h)) :
    Relabelling (moveRight (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((rightMovesOfStateAux n h) t : S)
        (turnBound_of_right ((rightMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) := by
  induction n
  · have t' := (right_moves_of_state_aux 0 h) t
    exfalso; exact turn_bound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl
#align pgame.relabelling_move_right_aux PGame.relabellingMoveRightAux

/-- The relabelling showing `move_right` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveRight (s : S) (t : RightMoves (ofState s)) :
    Relabelling (moveRight (ofState s) t) (ofState ((rightMovesOfState s).toFun t : S)) := by
  trans
  apply relabelling_move_right_aux
  apply of_state_aux_relabelling
#align pgame.relabelling_move_right PGame.relabellingMoveRight

instance fintypeLeftMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (LeftMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (left_moves_of_state_aux _ _).symm
  infer_instance
#align pgame.fintype_left_moves_of_state_aux PGame.fintypeLeftMovesOfStateAux

instance fintypeRightMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (RightMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (right_moves_of_state_aux _ _).symm
  infer_instance
#align pgame.fintype_right_moves_of_state_aux PGame.fintypeRightMovesOfStateAux

instance shortOfStateAux : ∀ (n : ℕ) {s : S} (h : turnBound s ≤ n), Short (ofStateAux n s h)
  | 0, s, h =>
    Short.mk'
      (fun i => by
        have i := (left_moves_of_state_aux _ _).toFun i
        exfalso
        exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
      fun j => by
      have j := (right_moves_of_state_aux _ _).toFun j
      exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    Short.mk'
      (fun i =>
        shortOfRelabelling (relabellingMoveLeftAux (n + 1) h i).symm (short_of_state_aux n _))
      fun j =>
      shortOfRelabelling (relabellingMoveRightAux (n + 1) h j).symm (short_of_state_aux n _)
#align pgame.short_of_state_aux PGame.shortOfStateAux

instance shortOfState (s : S) : Short (ofState s) := by
  dsimp [PGame.ofState]
  infer_instance
#align pgame.short_of_state PGame.shortOfState

end PGame

namespace Game

/-- Construct a combinatorial `game` from a state. -/
def ofState {S : Type u} [PGame.State S] (s : S) : Game :=
  ⟦PGame.ofState s⟧
#align game.of_state Game.ofState

end Game

