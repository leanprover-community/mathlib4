/-
Copyright (c) 2024 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.SetTheory.Game.State
import Mathlib.SetTheory.Game.Impartial

/-!
# Chomp as a combiantorial game

We define the game of Chomp as the normal-play variant of
the game described in Games of No Chance:

Players alternately name divisors of N other than 1,
which may not be multiples of previously named numbers.
The last player to name a divisor wins.

Then, we analyze it using the general strategy stealing argument,
proving it by contradiction,
as described in Siegel's Combinatorial Game Theory in pg. 38:

Assume G is a 2nd player win:
  There exists a G' that is a first-player win, such that G'' is a second-player win
  However, there exists a direct move from G -> G''. End contradiction
-/
namespace SetTheory

namespace PGame

namespace Chomp

open Function

abbrev PNon1Nat := { n : ℕ // 1 < n }

-- No element in D should have its proper divisors in D
def noMultiples (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ d ∈ x.properDivisors, d ∉ D

instance : DecidablePred noMultiples := by unfold noMultiples; infer_instance

/--
Should be true iff D is a subset of the proper divisors of n
where none of the numbers are multiples of each other.

Relative to Chomp, `n` is the controlling number, and `D`
is the board state without `n`.
-/
def validMentionableDivisors (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ n.properDivisors ∧ noMultiples D

instance : ∀ n : ℕ, DecidablePred (validMentionableDivisors n) :=
  by unfold validMentionableDivisors; infer_instance

def validDivisorSet (D : Finset ℕ) : Prop :=
  match D.max with
  | none => False
  | some α => validMentionableDivisors α (D.erase α)

instance : DecidablePred validDivisorSet := by unfold validDivisorSet; sorry

/--
A Chomp game is a natural number
attached with a set of "mentioned" divisors of n
such that no divisor is a multiple of each other.

In this representation, a game starts out with some 'controlling' natural number,
which is the max number in the Finset.
-/
abbrev Board := Subtype validDivisorSet

def controlling (b : Board) : ℕ := match b.val.max with
  -- b.val ≠ ∅ → b.val.max ≠ none
  | none => by solve_by_elim
  | some α => α

/--
Players can move by 'saying' a divisor.
This constructs the list of possible games to be made
in one move.
-/
def moves (b : Board) : Finset Board :=
  have controller := controlling b
  -- No divisors exist past b.n
  have upperPossibleMoves := Finset.range controller
  -- However, our only possible moves exist if the divisors + that move is still valid
  have moveset := upperPossibleMoves.val.filterMap fun x =>
    have newValid := b.val ∪ {x}
    have p := instDecidablePredFinsetNatValidDivisorSet newValid
    match p with
    | isTrue isStillValid => Option.some (Subtype.mk newValid isStillValid)
    | isFalse _ => Option.none

  moveset.toFinset

instance state : State Board where
  turnBound s := (controlling s).properDivisors.card - s.val.card
  l s := moves s
  r s := moves s
  left_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    sorry
  right_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    sorry

end Chomp

/-- Construct a pre-game from a Chomp board -/
def chomp (b : Chomp.Board) : PGame :=
  PGame.ofState b

/-- All games of Chomp are short.r -/
instance shortChomp (b : Chomp.Board) : Short (chomp b) := by
  dsimp [chomp]
  infer_instance

/-- All games of Chomp are impartial. -/
instance impartialChomp (b : Chomp.Board) : Impartial (chomp b) := by
  sorry

end PGame

end SetTheory
