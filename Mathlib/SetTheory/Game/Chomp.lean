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

instance : DecidablePred validDivisorSet := by
  unfold validDivisorSet
  sorry

/--
A Chomp game is a natural number
attached with a set of "mentioned" divisors of n
such that no divisor is a multiple of each other.

In this representation, a game starts out with some 'controlling' natural number,
which is the max number in the Finset.
-/
abbrev Board := Subtype validDivisorSet

theorem never_empty (b : Board) : b.val ≠ ∅ := by
  have x := b.property
  sorry

def controlling (b : Board) : ℕ := match b.val.max with
  -- b.val ≠ ∅ → b.val.max ≠ none
  | none => by solve_by_elim
  | some α => α


/--
Players can move by 'saying' a divisor.
This constructs the list of possible games to be made
in one move.
-/
def moves (b : Board) : Finset ℕ :=
  -- No divisors exist past b.n
  have upperPossibleMoves := Finset.range (controlling b)
  -- However, our only possible moves exist if the divisors + that move is still valid
  have moveset := upperPossibleMoves.val.filterMap fun x =>
    have newValid := b.val ∪ {x}
    have p := instDecidablePredFinsetNatValidDivisorSet newValid
    match p with
    | isTrue _ => x
    | isFalse _ => none

  moveset.toFinset

def move (b : Board) (move : ℕ) : Board :=
  have newValid := b.val ∪ {move}
  have p := instDecidablePredFinsetNatValidDivisorSet newValid
  match p with
  | isTrue isStillValid => Subtype.mk newValid isStillValid
  | isFalse _ => by solve_by_elim

def upperBoundMoveCount (b : Board) : ℕ := (controlling b).properDivisors.card - (b.val.card - 1)

theorem unchanging_controller (b : Board) (m : ℕ) :
    controlling b = controlling (move b m) := by
  unfold controlling
  sorry

theorem move_card {b : Board} {m : ℕ} (h : m ∈ moves b) :
  Finset.card (move b m).val = Finset.card b.val + 1 := by sorry

theorem moves_smaller {b : Board} {m : ℕ} (h : m ∈ moves b) :
    upperBoundMoveCount (move b m) < upperBoundMoveCount b := by
  simp [upperBoundMoveCount, move_card h, ← unchanging_controller b]
  -- an unfinished game b will always have a move left
  have x : b.val.card - 1 < (controlling b).properDivisors.card := by
    sorry
  refine Nat.sub_lt_sub_left ?a ?b
  · exact x
  have y : 0 < b.val.card := by
    by_contra k
    simp at k
    have x : b.val ≠ ∅ := never_empty b
    contradiction
  exact Nat.sub_one_lt_of_lt y

instance state : State Board where
  turnBound s := upperBoundMoveCount s
  l s := (moves s).image (move s)
  r s := (moves s).image (move s)
  left_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, ⟨h, rfl⟩⟩
    exact moves_smaller h
  right_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, ⟨h, rfl⟩⟩
    exact moves_smaller h

end Chomp

/-- Construct a pre-game from a Chomp board -/
def chomp (b : Chomp.Board) : PGame :=
  PGame.ofState b

/-- All games of Chomp are short.r -/
instance shortChomp (b : Chomp.Board) : Short (chomp b) := by
  dsimp [chomp]
  infer_instance

end PGame

end SetTheory
