/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.SetTheory.Game.Short

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
  /-- Upper bound on the number of possible turns remaining from this state -/
  turnBound : S → ℕ
  /-- States reachable by a Left move -/
  l : S → Finset S
  /-- States reachable by a Right move -/
  r : S → Finset S
  left_bound : ∀ {s t : S}, t ∈ l s → turnBound t < turnBound s
  right_bound : ∀ {s t : S}, t ∈ r s → turnBound t < turnBound s

open State

variable {S : Type u} [State S]

theorem turnBound_ne_zero_of_left_move {s t : S} (m : t ∈ l s) : turnBound s ≠ 0 := by
  intro h
  have t := left_bound m
  rw [h] at t
  exact Nat.not_succ_le_zero _ t

theorem turnBound_ne_zero_of_right_move {s t : S} (m : t ∈ r s) : turnBound s ≠ 0 := by
  intro h
  have t := right_bound m
  omega

theorem turnBound_of_left {s t : S} (m : t ∈ l s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (left_bound m) h)

theorem turnBound_of_right {s t : S} (m : t ∈ r s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (right_bound m) h)

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

/-- Construct a combinatorial `PGame` from a state. -/
def ofState (s : S) : PGame :=
  ofStateAux (turnBound s) s (refl _)

/-- The equivalence between `leftMoves` for a `PGame` constructed using `ofStateAux _ s _`, and
`L s`. -/
def leftMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    LeftMoves (ofStateAux n s h) ≃ { t // t ∈ l s } := by induction n <;> rfl

/-- The equivalence between `leftMoves` for a `PGame` constructed using `ofState s`, and `l s`. -/
def leftMovesOfState (s : S) : LeftMoves (ofState s) ≃ { t // t ∈ l s } :=
  leftMovesOfStateAux _ _

/-- The equivalence between `rightMoves` for a `PGame` constructed using `ofStateAux _ s _`, and
`R s`. -/
def rightMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    RightMoves (ofStateAux n s h) ≃ { t // t ∈ r s } := by induction n <;> rfl

/-- The equivalence between `rightMoves` for a `PGame` constructed using `ofState s`, and
`R s`. -/
def rightMovesOfState (s : S) : RightMoves (ofState s) ≃ { t // t ∈ r s } :=
  rightMovesOfStateAux _ _

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

/-- The relabelling showing `moveLeft` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveLeft (s : S) (t : LeftMoves (ofState s)) :
    Relabelling (moveLeft (ofState s) t) (ofState ((leftMovesOfState s).toFun t : S)) := by
  trans
  · apply relabellingMoveLeftAux
  · apply ofStateAuxRelabelling

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

/-- The relabelling showing `moveRight` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveRight (s : S) (t : RightMoves (ofState s)) :
    Relabelling (moveRight (ofState s) t) (ofState ((rightMovesOfState s).toFun t : S)) := by
  trans
  · apply relabellingMoveRightAux
  · apply ofStateAuxRelabelling

instance fintypeLeftMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (LeftMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (leftMovesOfStateAux _ _).symm

instance fintypeRightMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (RightMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (rightMovesOfStateAux _ _).symm

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
  | n + 1, _, h =>
    Short.mk'
      (fun i =>
        shortOfRelabelling (relabellingMoveLeftAux (n + 1) h i).symm (shortOfStateAux n _))
      fun j =>
      shortOfRelabelling (relabellingMoveRightAux (n + 1) h j).symm (shortOfStateAux n _)

instance shortOfState (s : S) : Short (ofState s) := by
  dsimp [PGame.ofState]
  infer_instance

end PGame

namespace Game

/-- Construct a combinatorial `Game` from a state. -/
def ofState {S : Type u} [PGame.State S] (s : S) : Game :=
  ⟦PGame.ofState s⟧

end Game

end SetTheory
