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
# Chomp as a combinatorial game

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

-- TODO: computable without classical predicate logic?
instance : DecidablePred noMultiples := by unfold noMultiples; infer_instance

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

theorem max_is_some (b : Board) : b.val.max.isSome = true := by
  have p := b.property
  unfold validDivisorSet at p
  by_contra k
  simp only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at k
  simp only [k] at p

theorem never_empty (b : Board) : b.val.Nonempty := by
  have p := b.property
  unfold validDivisorSet at p
  by_contra k
  simp only [Finset.not_nonempty_iff_eq_empty] at k
  have y : b.val.max = ⊥ := by
    rw [k]
    exact Finset.max_empty
  simp only [y] at p

def controlling (b : Board) : ℕ := b.val.max.get (max_is_some b)

theorem controlling_is_max (b : Board) : Option.some (controlling b) = b.val.max := by
  unfold controlling
  rw [Option.some_get (max_is_some b)]

theorem controlling_is_max' (b : Board) : controlling b = b.val.max' (never_empty b) := by
  unfold controlling
  sorry

theorem controlling_in_board (b : Board) : controlling b ∈ b.val := by
  rw [controlling_is_max']
  simp [Finset.max'_mem]

/-- Players can move by 'saying' a divisor. -/
def moves (b : Board) : Finset ℕ := Finset.filter
  (fun x => validDivisorSet (b.val ∪ {x}))
  ((controlling b).properDivisors \ b.val)

def move (b : Board) (m : ℕ) (h : m ∈ moves b) : Board :=
  have isValidDivisorSet := by
    unfold moves at h
    simp_all only [Finset.mem_filter]
  Subtype.mk (b.val ∪ {m}) isValidDivisorSet

theorem move_not_in_board (b : Board) (m : ℕ) (h : m ∈ moves b) : m ∉ b.val := by
  unfold moves at h
  simp only [Finset.mem_filter, Nat.mem_properDivisors] at h
  have x := h.left
  simp [Finset.mem_sdiff] at x
  exact x.right

theorem move_smaller_than_controller (b : Board) (m : ℕ) (h : m ∈ moves b) : m < controlling b := by
  unfold moves at h
  sorry

theorem move_is_set (b : Board) (m : ℕ) (h : m ∈ moves b) : (move b m h).val = b.val ∪ {m} := by
  unfold move
  sorry

def upperBoundMoveCount (b : Board) : ℕ := (controlling b).properDivisors.card - (b.val.card - 1)

theorem unchanging_controller (b : Board) (m : ℕ) (h : m ∈ moves b) :
    controlling b = controlling (move b m h) := by
  repeat rw [controlling_is_max']
  unfold move
  let D := b.val
  simp
  have s := move_smaller_than_controller b m h
  
  sorry

theorem move_card {b : Board} {m : ℕ} (h : m ∈ moves b) :
    Finset.card (move b m h).val = Finset.card b.val + 1 := by
  rw [move_is_set]
  have x := move_not_in_board b m h
  rw [← Finset.disjoint_singleton_right] at x
  simp only [Finset.sup_eq_union, Finset.card_union_of_disjoint x, Finset.card_singleton]

theorem unfinished_game_has_moves (b : Board) (h : moves b ≠ ∅) :
    b.val.card - 1 < (controlling b).properDivisors.card := by
  have p := b.property
  unfold validDivisorSet validMentionableDivisors at p
  have s : controlling b = b.val.max := controlling_is_max b
  simp only [← s, Nat.cast_id] at p
  have u := Finset.card_le_card p.left
  have y := Finset.card_erase_add_one (controlling_in_board b)
  have j := Nat.eq_sub_of_add_eq y
  rw [← j]
  unfold moves at h
  -- TODO: by h, ≤ transforms
  sorry

theorem moves_smaller {b : Board} {m : ℕ} (h : m ∈ moves b) :
    upperBoundMoveCount (move b m h) < upperBoundMoveCount b := by
  simp only [upperBoundMoveCount, ← unchanging_controller b, move_card h, add_tsub_cancel_right]
  -- an unfinished game b will always have a move left
  have k : moves b ≠ ∅ := Finset.ne_empty_of_mem h
  have x := unfinished_game_has_moves b k

  refine Nat.sub_lt_sub_left ?a ?b
  · exact x
  have y : 0 < b.val.card := by
    by_contra k
    simp only [Finset.card_pos, Finset.not_nonempty_iff_eq_empty] at k
    have u := never_empty b
    simp only [Finset.nonempty_iff_ne_empty] at u
    contradiction
  exact Nat.sub_one_lt_of_lt y

instance state : State Board where
  turnBound s := upperBoundMoveCount s
  l s := ((moves s).val.map (fun m => (move s m (sorry)))).toFinset
  r s := ((moves s).val.map (fun m => (move s m (sorry)))).toFinset
  left_bound m := by
    simp only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val] at m
    rcases m with ⟨_, ⟨h, rfl⟩⟩
    exact moves_smaller h
  right_bound m := by
    simp only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val] at m
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
