/-
Copyright (c) 2024 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import Mathlib.Data.Finset.Max
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

-- TODO: this could be computable if we drop the reliance on Classical.decPred
noncomputable section

namespace SetTheory

namespace PGame

namespace Chomp

open Function

abbrev PNon1Nat := { n : ℕ // 1 < n }

-- No element in D should have its proper divisors in D
def noMultiples (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ d ∈ x.properDivisors, d ∉ D

/--
Should be true iff D is a subset of the proper divisors of n
where none of the numbers are multiples of each other.

Relative to Chomp, `n` is the controlling number, and `D`
is the board state without `n`.
-/
def validMentionableDivisors (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ n.properDivisors ∧ noMultiples D

def validDivisorSet (D : Finset ℕ) : Prop :=
  match D.max with
  | none => False
  | some α => validMentionableDivisors α (D.erase α)

instance : DecidablePred validDivisorSet := Classical.decPred _

/--
A Chomp game is a natural number
attached with a set of "mentioned" divisors of n
such that no divisor is a multiple of each other.

In this representation, a game starts out with some 'controlling' natural number,
which is the max number in the Finset.
-/
abbrev Board := Subtype validDivisorSet
theorem max_not_bot (b : Board) : b.val.max.isSome := by
  have p := b.property
  unfold validDivisorSet at p
  by_contra k
  simp only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at k
  simp only [k] at p

theorem never_empty (b : Board) : b.val ≠ ∅ := by
  have p := b.property
  unfold validDivisorSet at p
  by_contra k
  have y : b.val.max = ⊥ := by
    rw [k]
    exact Finset.max_empty
  simp only [y] at p

def controlling (b : Board) : ℕ := b.val.max.get (max_not_bot b)

/--
Players can move by 'saying' a divisor.
This constructs the list of possible games to be made
in one move.
-/
def moves (b : Board) : Finset ℕ :=
  let upperPossibleMoves := Finset.range (controlling b)
  let validMoves := upperPossibleMoves.val.filterMap fun x =>
    if validDivisorSet (b.val ∪ {x}) then some x else none
  validMoves.toFinset

def move (b : Board) (move : ℕ) : Board :=
  have newValid := b.val ∪ {move}
  have p := instDecidablePredFinsetNatValidDivisorSet newValid
  match p with
  | isTrue isStillValid => Subtype.mk newValid isStillValid
  | isFalse _ => by solve_by_elim

def upperBoundMoveCount (b : Board) : ℕ := (controlling b).properDivisors.card - (b.val.card - 1)

theorem unchanging_controller (b : Board) (m : ℕ) :
    controlling b = controlling (move b m) := by
  unfold controlling move
  let D := b.val
  simp
  sorry

theorem move_card {b : Board} {m : ℕ} (h : m ∈ moves b) :
    Finset.card (move b m).val = Finset.card b.val + 1 := by
  unfold move
  sorry

theorem moves_smaller {b : Board} {m : ℕ} (h : m ∈ moves b) :
    upperBoundMoveCount (move b m) < upperBoundMoveCount b := by
  simp only [upperBoundMoveCount, ← unchanging_controller b, move_card h, add_tsub_cancel_right]
  -- an unfinished game b will always have a move left
  have x : b.val.card - 1 < (controlling b).properDivisors.card := by
    have p := b.property
    have k : b.val.max.isSome := max_not_bot b
    unfold controlling
    simp [k]
    sorry

  refine Nat.sub_lt_sub_left ?a ?b
  · exact x
  have y : 0 < b.val.card := by
    by_contra k
    simp only [Finset.card_pos, Finset.not_nonempty_iff_eq_empty] at k
    have := never_empty b
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
  dsimp only [chomp]
  infer_instance

end PGame

end SetTheory
