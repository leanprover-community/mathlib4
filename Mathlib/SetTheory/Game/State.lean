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

namespace PGame

/-- `PGame.State S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `PGame.ofState s` or `Game.ofState s` to construct the game.

`PGame.State.l : S → Finset S` and `PGame.State.r : S → Finset S` describe the states reachable
by a move by Left or Right. `PGame.State.turnBound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class State (S : Type u) where
  turnBound : S → ℕ
  l : S → Finset S
  r : S → Finset S
  left_bound : ∀ {s t : S}, t ∈ l s → turnBound t < turnBound s
  right_bound : ∀ {s t : S}, t ∈ r s → turnBound t < turnBound s
#align pgame.state PGame.State

open State

variable {S : Type u} [State S]

theorem turnBound_ne_zero_of_left_move {s t : S} (m : t ∈ l s) : turnBound s ≠ 0 := by
  intro h
  -- ⊢ False
  have t := left_bound m
  -- ⊢ False
  rw [h] at t
  -- ⊢ False
  exact Nat.not_succ_le_zero _ t
  -- 🎉 no goals
#align pgame.turn_bound_ne_zero_of_left_move PGame.turnBound_ne_zero_of_left_move

theorem turnBound_ne_zero_of_right_move {s t : S} (m : t ∈ r s) : turnBound s ≠ 0 := by
  intro h
  -- ⊢ False
  have t := right_bound m
  -- ⊢ False
  rw [h] at t
  -- ⊢ False
  exact Nat.not_succ_le_zero _ t
  -- 🎉 no goals
#align pgame.turn_bound_ne_zero_of_right_move PGame.turnBound_ne_zero_of_right_move

theorem turnBound_of_left {s t : S} (m : t ∈ l s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (left_bound m) h)
#align pgame.turn_bound_of_left PGame.turnBound_of_left

theorem turnBound_of_right {s t : S} (m : t ∈ r s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (right_bound m) h)
#align pgame.turn_bound_of_right PGame.turnBound_of_right

/-- Construct a `PGame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def ofStateAux : ∀ (n : ℕ) (s : S), turnBound s ≤ n → PGame
  | 0, s, h =>
    PGame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => by exfalso; exact turnBound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h))
                   -- ⊢ False
                            -- 🎉 no goals
      fun t => by exfalso; exact turnBound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h)
                  -- ⊢ False
                           -- 🎉 no goals
  | n + 1, s, h =>
    PGame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => ofStateAux n t (turnBound_of_left t.2 n h)) fun t =>
      ofStateAux n t (turnBound_of_right t.2 n h)
#align pgame.of_state_aux PGame.ofStateAux

/-- Two different (valid) turn bounds give equivalent games. -/
def ofStateAuxRelabelling :
    ∀ (s : S) (n m : ℕ) (hn : turnBound s ≤ n) (hm : turnBound s ≤ m),
      Relabelling (ofStateAux n s hn) (ofStateAux m s hm)
  | s, 0, 0, hn, hm => by
    dsimp [PGame.ofStateAux]
    -- ⊢ (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : False)) fun  …
    fconstructor; rfl; rfl
                       -- ⊢ (i : LeftMoves (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ …
    · intro i; dsimp at i; exfalso
      -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fal …
               -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fal …
                           -- ⊢ False
      exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
      -- 🎉 no goals
    · intro j; dsimp at j; exfalso
      -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fa …
               -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fa …
                           -- ⊢ False
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
      -- 🎉 no goals
  | s, 0, m + 1, hn, hm => by
    dsimp [PGame.ofStateAux]
    -- ⊢ (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : False)) fun  …
    fconstructor; rfl; rfl
                       -- ⊢ (i : LeftMoves (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ …
    · intro i; dsimp at i; exfalso
      -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fal …
               -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fal …
                           -- ⊢ False
      exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
      -- 🎉 no goals
    · intro j; dsimp at j; exfalso
      -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fa …
               -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => False.elim (_ : Fa …
                           -- ⊢ False
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn)
      -- 🎉 no goals
  | s, n + 1, 0, hn, hm => by
    dsimp [PGame.ofStateAux]
    -- ⊢ (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_ : turnBou …
    fconstructor; rfl; rfl
                       -- ⊢ (i : LeftMoves (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n  …
    · intro i; dsimp at i; exfalso
      -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_  …
               -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_  …
                           -- ⊢ False
      exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm)
      -- 🎉 no goals
    · intro j; dsimp at j; exfalso
      -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_ …
               -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_ …
                           -- ⊢ False
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
      -- 🎉 no goals
  | s, n + 1, m + 1, hn, hm => by
    dsimp [PGame.ofStateAux]
    -- ⊢ (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_ : turnBou …
    fconstructor; rfl; rfl
                       -- ⊢ (i : LeftMoves (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n  …
    · intro i
      -- ⊢ moveLeft (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_  …
      apply ofStateAuxRelabelling
      -- 🎉 no goals
    · intro j
      -- ⊢ moveRight (mk { t // t ∈ l s } { t // t ∈ r s } (fun t => ofStateAux n ↑t (_ …
      apply ofStateAuxRelabelling
      -- 🎉 no goals
#align pgame.of_state_aux_relabelling PGame.ofStateAuxRelabelling

/-- Construct a combinatorial `PGame` from a state. -/
def ofState (s : S) : PGame :=
  ofStateAux (turnBound s) s (refl _)
#align pgame.of_state PGame.ofState

/-- The equivalence between `leftMoves` for a `PGame` constructed using `ofStateAux _ s _`, and
`L s`. -/
def leftMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    LeftMoves (ofStateAux n s h) ≃ { t // t ∈ l s } := by induction n <;> rfl
                                                          -- ⊢ LeftMoves (ofStateAux Nat.zero s h) ≃ { t // t ∈ l s }
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align pgame.left_moves_of_state_aux PGame.leftMovesOfStateAux

/-- The equivalence between `leftMoves` for a `PGame` constructed using `ofState s`, and `l s`. -/
def leftMovesOfState (s : S) : LeftMoves (ofState s) ≃ { t // t ∈ l s } :=
  leftMovesOfStateAux _ _
#align pgame.left_moves_of_state PGame.leftMovesOfState

/-- The equivalence between `rightMoves` for a `PGame` constructed using `ofStateAux _ s _`, and
`R s`. -/
def rightMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    RightMoves (ofStateAux n s h) ≃ { t // t ∈ r s } := by induction n <;> rfl
                                                           -- ⊢ RightMoves (ofStateAux Nat.zero s h) ≃ { t // t ∈ r s }
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align pgame.right_moves_of_state_aux PGame.rightMovesOfStateAux

/-- The equivalence between `rightMoves` for a `PGame` constructed using `ofState s`, and
`R s`. -/
def rightMovesOfState (s : S) : RightMoves (ofState s) ≃ { t // t ∈ r s } :=
  rightMovesOfStateAux _ _
#align pgame.right_moves_of_state PGame.rightMovesOfState

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
  -- ⊢ moveLeft (ofStateAux Nat.zero s h) t ≡r ofStateAux (Nat.zero - 1) ↑(↑(leftMo …
  · have t' := (leftMovesOfStateAux 0 h) t
    -- ⊢ moveLeft (ofStateAux Nat.zero s h) t ≡r ofStateAux (Nat.zero - 1) ↑(↑(leftMo …
    exfalso; exact turnBound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
    -- ⊢ False
             -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align pgame.relabelling_move_left_aux PGame.relabellingMoveLeftAux

/-- The relabelling showing `moveLeft` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveLeft (s : S) (t : LeftMoves (ofState s)) :
    Relabelling (moveLeft (ofState s) t) (ofState ((leftMovesOfState s).toFun t : S)) := by
  trans
  apply relabellingMoveLeftAux
  -- ⊢ ofStateAux (turnBound s - 1) ↑(↑(leftMovesOfStateAux (turnBound s) (_ : turn …
  apply ofStateAuxRelabelling
  -- 🎉 no goals
#align pgame.relabelling_move_left PGame.relabellingMoveLeft

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
  -- ⊢ moveRight (ofStateAux Nat.zero s h) t ≡r ofStateAux (Nat.zero - 1) ↑(↑(right …
  · have t' := (rightMovesOfStateAux 0 h) t
    -- ⊢ moveRight (ofStateAux Nat.zero s h) t ≡r ofStateAux (Nat.zero - 1) ↑(↑(right …
    exfalso; exact turnBound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
    -- ⊢ False
             -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align pgame.relabelling_move_right_aux PGame.relabellingMoveRightAux

/-- The relabelling showing `moveRight` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveRight (s : S) (t : RightMoves (ofState s)) :
    Relabelling (moveRight (ofState s) t) (ofState ((rightMovesOfState s).toFun t : S)) := by
  trans
  apply relabellingMoveRightAux
  -- ⊢ ofStateAux (turnBound s - 1) ↑(↑(rightMovesOfStateAux (turnBound s) (_ : tur …
  apply ofStateAuxRelabelling
  -- 🎉 no goals
#align pgame.relabelling_move_right PGame.relabellingMoveRight

instance fintypeLeftMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (LeftMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (leftMovesOfStateAux _ _).symm
  -- 🎉 no goals
#align pgame.fintype_left_moves_of_state_aux PGame.fintypeLeftMovesOfStateAux

instance fintypeRightMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (RightMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (rightMovesOfStateAux _ _).symm
  -- 🎉 no goals
#align pgame.fintype_right_moves_of_state_aux PGame.fintypeRightMovesOfStateAux

instance shortOfStateAux : ∀ (n : ℕ) {s : S} (h : turnBound s ≤ n), Short (ofStateAux n s h)
  | 0, s, h =>
    Short.mk'
      (fun i => by
        have i := (leftMovesOfStateAux _ _).toFun i
        -- ⊢ Short (moveLeft (ofStateAux 0 s h) i✝)
        exfalso
        -- ⊢ False
        exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
        -- 🎉 no goals
      fun j => by
      have j := (rightMovesOfStateAux _ _).toFun j
      -- ⊢ Short (moveRight (ofStateAux 0 s h) j✝)
      exfalso
      -- ⊢ False
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
      -- 🎉 no goals
  | n + 1, s, h =>
    Short.mk'
      (fun i =>
        shortOfRelabelling (relabellingMoveLeftAux (n + 1) h i).symm (shortOfStateAux n _))
      fun j =>
      shortOfRelabelling (relabellingMoveRightAux (n + 1) h j).symm (shortOfStateAux n _)
#align pgame.short_of_state_aux PGame.shortOfStateAux

instance shortOfState (s : S) : Short (ofState s) := by
  dsimp [PGame.ofState]
  -- ⊢ Short (ofStateAux (turnBound s) s (_ : turnBound s ≤ turnBound s))
  infer_instance
  -- 🎉 no goals
#align pgame.short_of_state PGame.shortOfState

end PGame

namespace Game

/-- Construct a combinatorial `Game` from a state. -/
def ofState {S : Type u} [PGame.State S] (s : S) : Game :=
  ⟦PGame.ofState s⟧
#align game.of_state Game.ofState

end Game
