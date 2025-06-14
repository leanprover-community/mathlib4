/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathlib.SetTheory.Game.Birthday
import Mathlib.SetTheory.Game.Impartial
import Mathlib.SetTheory.Nimber.Basic

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `o`. In the game of `nim o₁` both players
may move to `nim o₂` for any `o₂ < o₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundyValue G)`.
Finally, we prove that the grundy value of a sum `G + H` corresponds to the nimber sum of the
individual grundy values.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim o` to be `Set.Iio o`.
However, this definition does not work for us because it would make the type of nim
`Ordinal.{u} → SetTheory.PGame.{u + 1}`, which would make it impossible for us to state the
Sprague-Grundy theorem, since that requires the type of `nim` to be
`Ordinal.{u} → SetTheory.PGame.{u}`. For this reason, we instead use `o.toType` for the possible
moves. We expose `toLeftMovesNim` and `toRightMovesNim` to conveniently convert an ordinal less than
`o` into a left or right move of `nim o`, and vice versa.
-/


noncomputable section

universe u

namespace SetTheory

open scoped PGame
open Ordinal Nimber

namespace PGame

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
noncomputable def nim (o : Ordinal.{u}) : PGame.{u} :=
  ⟨o.toType, o.toType,
    fun x => nim ((enumIsoToType o).symm x).val,
    fun x => nim ((enumIsoToType o).symm x).val⟩
termination_by o
decreasing_by all_goals exact ((enumIsoToType o).symm x).prop

@[deprecated "you can use `rw [nim]` directly" (since := "2025-01-23")]
theorem nim_def (o : Ordinal) : nim o =
    ⟨o.toType, o.toType,
      fun x => nim ((enumIsoToType o).symm x).val,
      fun x => nim ((enumIsoToType o).symm x).val⟩ := by
  rw [nim]

theorem leftMoves_nim (o : Ordinal) : (nim o).LeftMoves = o.toType := by rw [nim]; rfl
theorem rightMoves_nim (o : Ordinal) : (nim o).RightMoves = o.toType := by rw [nim]; rfl

theorem moveLeft_nim_hEq (o : Ordinal) :
    HEq (nim o).moveLeft fun i : o.toType => nim ((enumIsoToType o).symm i) := by rw [nim]; rfl

theorem moveRight_nim_hEq (o : Ordinal) :
    HEq (nim o).moveRight fun i : o.toType => nim ((enumIsoToType o).symm i) := by rw [nim]; rfl

/-- Turns an ordinal less than `o` into a left move for `nim o` and vice versa. -/
noncomputable def toLeftMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).LeftMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (leftMoves_nim o).symm)

/-- Turns an ordinal less than `o` into a right move for `nim o` and vice versa. -/
noncomputable def toRightMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).RightMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (rightMoves_nim o).symm)

@[simp]
theorem toLeftMovesNim_symm_lt {o : Ordinal} (i : (nim o).LeftMoves) :
    toLeftMovesNim.symm i < o :=
  (toLeftMovesNim.symm i).prop

@[simp]
theorem toRightMovesNim_symm_lt {o : Ordinal} (i : (nim o).RightMoves) :
    toRightMovesNim.symm i < o :=
  (toRightMovesNim.symm i).prop

@[simp]
theorem moveLeft_nim {o : Ordinal} (i) : (nim o).moveLeft i = nim (toLeftMovesNim.symm i).val :=
  (congr_heq (moveLeft_nim_hEq o).symm (cast_heq _ i)).symm

@[deprecated moveLeft_nim (since := "2024-10-30")]
alias moveLeft_nim' := moveLeft_nim

theorem moveLeft_toLeftMovesNim {o : Ordinal} (i) :
    (nim o).moveLeft (toLeftMovesNim i) = nim i := by
  simp

@[simp]
theorem moveRight_nim {o : Ordinal} (i) : (nim o).moveRight i = nim (toRightMovesNim.symm i).val :=
  (congr_heq (moveRight_nim_hEq o).symm (cast_heq _ i)).symm

@[deprecated moveRight_nim (since := "2024-10-30")]
alias moveRight_nim' := moveRight_nim

theorem moveRight_toRightMovesNim {o : Ordinal} (i) :
    (nim o).moveRight (toRightMovesNim i) = nim i := by
  simp

/-- A recursion principle for left moves of a nim game. -/
@[elab_as_elim]
def leftMovesNimRecOn {o : Ordinal} {P : (nim o).LeftMoves → Sort*} (i : (nim o).LeftMoves)
    (H : ∀ a (H : a < o), P <| toLeftMovesNim ⟨a, H⟩) : P i := by
  rw [← toLeftMovesNim.apply_symm_apply i]; apply H

/-- A recursion principle for right moves of a nim game. -/
@[elab_as_elim]
def rightMovesNimRecOn {o : Ordinal} {P : (nim o).RightMoves → Sort*} (i : (nim o).RightMoves)
    (H : ∀ a (H : a < o), P <| toRightMovesNim ⟨a, H⟩) : P i := by
  rw [← toRightMovesNim.apply_symm_apply i]; apply H

instance isEmpty_nim_zero_leftMoves : IsEmpty (nim 0).LeftMoves := by
  rw [nim]
  exact isEmpty_toType_zero

instance isEmpty_nim_zero_rightMoves : IsEmpty (nim 0).RightMoves := by
  rw [nim]
  exact isEmpty_toType_zero

/-- `nim 0` has exactly the same moves as `0`. -/
def nimZeroRelabelling : nim 0 ≡r 0 :=
  Relabelling.isEmpty _

theorem nim_zero_equiv : nim 0 ≈ 0 :=
  Equiv.isEmpty _

noncomputable instance uniqueNimOneLeftMoves : Unique (nim 1).LeftMoves :=
  (Equiv.cast <| leftMoves_nim 1).unique

noncomputable instance uniqueNimOneRightMoves : Unique (nim 1).RightMoves :=
  (Equiv.cast <| rightMoves_nim 1).unique

@[simp]
theorem default_nim_one_leftMoves_eq :
    (default : (nim 1).LeftMoves) = @toLeftMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl

@[simp]
theorem default_nim_one_rightMoves_eq :
    (default : (nim 1).RightMoves) = @toRightMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl

@[simp]
theorem toLeftMovesNim_one_symm (i) :
    (@toLeftMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]

@[simp]
theorem toRightMovesNim_one_symm (i) :
    (@toRightMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]

theorem nim_one_moveLeft (x) : (nim 1).moveLeft x = nim 0 := by simp

theorem nim_one_moveRight (x) : (nim 1).moveRight x = nim 0 := by simp

/-- `nim 1` has exactly the same moves as `star`. -/
def nimOneRelabelling : nim 1 ≡r star := by
  rw [nim]
  refine ⟨?_, ?_, fun i => ?_, fun j => ?_⟩
  any_goals dsimp; apply Equiv.ofUnique
  all_goals simpa [enumIsoToType] using nimZeroRelabelling

theorem nim_one_equiv : nim 1 ≈ star :=
  nimOneRelabelling.equiv

@[simp]
theorem nim_birthday (o : Ordinal) : (nim o).birthday = o := by
  induction o using Ordinal.induction with | _ o IH
  rw [nim, birthday_def]
  dsimp
  rw [max_eq_right le_rfl]
  convert lsub_typein o with i
  exact IH _ (typein_lt_self i)

@[simp]
theorem neg_nim (o : Ordinal) : -nim o = nim o := by
  induction o using Ordinal.induction with | _ o IH
  rw [nim]; dsimp; congr <;> funext i <;> exact IH _ (Ordinal.typein_lt_self i)

instance impartial_nim (o : Ordinal) : Impartial (nim o) := by
  induction o using Ordinal.induction with | _ o IH
  rw [impartial_def, neg_nim]
  refine ⟨equiv_rfl, fun i => ?_, fun i => ?_⟩ <;> simpa using IH _ (typein_lt_self _)

theorem nim_fuzzy_zero_of_ne_zero {o : Ordinal} (ho : o ≠ 0) : nim o ‖ 0 := by
  rw [Impartial.fuzzy_zero_iff_lf, lf_zero_le]
  use toRightMovesNim ⟨0, Ordinal.pos_iff_ne_zero.2 ho⟩
  simp

@[simp]
theorem nim_add_equiv_zero_iff (o₁ o₂ : Ordinal) : (nim o₁ + nim o₂ ≈ 0) ↔ o₁ = o₂ := by
  constructor
  · refine not_imp_not.1 fun hne : _ ≠ _ => (Impartial.not_equiv_zero_iff (nim o₁ + nim o₂)).2 ?_
    wlog h : o₁ < o₂
    · exact (fuzzy_congr_left add_comm_equiv).1 (this _ _ hne.symm (hne.lt_or_gt.resolve_left h))
    rw [Impartial.fuzzy_zero_iff_gf, zero_lf_le]
    use toLeftMovesAdd (Sum.inr <| toLeftMovesNim ⟨_, h⟩)
    · simpa using (Impartial.add_self (nim o₁)).2
  · rintro rfl
    exact Impartial.add_self (nim o₁)

@[simp]
theorem nim_add_fuzzy_zero_iff {o₁ o₂ : Ordinal} : nim o₁ + nim o₂ ‖ 0 ↔ o₁ ≠ o₂ := by
  rw [iff_not_comm, Impartial.not_fuzzy_zero_iff, nim_add_equiv_zero_iff]

@[simp]
theorem nim_equiv_iff_eq {o₁ o₂ : Ordinal} : (nim o₁ ≈ nim o₂) ↔ o₁ = o₂ := by
  rw [Impartial.equiv_iff_add_equiv_zero, nim_add_equiv_zero_iff]

/-- The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of either its left or right options.

This is the ordinal which corresponds to the game of nim that the game is equivalent to.

This function takes a value in `Nimber`. This is a type synonym for the ordinals which has the same
ordering, but addition in `Nimber` is such that it corresponds to the grundy value of the addition
of games. See that file for more information on nimbers and their arithmetic. -/
noncomputable def grundyValue (G : PGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun i => grundyValue (G.moveLeft i))ᶜ
termination_by G

theorem grundyValue_eq_sInf_moveLeft (G : PGame) :
    grundyValue G = sInf (Set.range (grundyValue ∘ G.moveLeft))ᶜ := by
  rw [grundyValue]; rfl

theorem grundyValue_ne_moveLeft {G : PGame} (i : G.LeftMoves) :
    grundyValue (G.moveLeft i) ≠ grundyValue G := by
  conv_rhs => rw [grundyValue_eq_sInf_moveLeft]
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (Set.range fun i => grundyValue (G.moveLeft i)))
  rw [Set.mem_compl_iff, Set.mem_range, not_exists] at this
  exact this _

theorem le_grundyValue_of_Iio_subset_moveLeft {G : PGame} {o : Nimber}
    (h : Set.Iio o ⊆ Set.range (grundyValue ∘ G.moveLeft)) : o ≤ grundyValue G := by
  by_contra! ho
  obtain ⟨i, hi⟩ := h ho
  exact grundyValue_ne_moveLeft i hi

theorem exists_grundyValue_moveLeft_of_lt {G : PGame} {o : Nimber} (h : o < grundyValue G) :
    ∃ i, grundyValue (G.moveLeft i) = o := by
  rw [grundyValue_eq_sInf_moveLeft] at h
  by_contra ha
  exact h.not_ge (csInf_le' ha)

theorem grundyValue_le_of_forall_moveLeft {G : PGame} {o : Nimber}
    (h : ∀ i, grundyValue (G.moveLeft i) ≠ o) : G.grundyValue ≤ o := by
  contrapose! h
  exact exists_grundyValue_moveLeft_of_lt h

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim corresponding to the game's Grundy value. -/
theorem equiv_nim_grundyValue (G : PGame.{u}) [G.Impartial] :
    G ≈ nim (toOrdinal (grundyValue G)) := by
  rw [Impartial.equiv_iff_add_equiv_zero, ← Impartial.forall_leftMoves_fuzzy_iff_equiv_zero]
  intro x
  apply leftMoves_add_cases x <;>
  intro i
  · rw [add_moveLeft_inl,
      ← fuzzy_congr_left (add_congr_left (Equiv.symm (equiv_nim_grundyValue _))),
      nim_add_fuzzy_zero_iff]
    exact grundyValue_ne_moveLeft i
  · rw [add_moveLeft_inr, ← Impartial.exists_left_move_equiv_iff_fuzzy_zero]
    obtain ⟨j, hj⟩ := exists_grundyValue_moveLeft_of_lt <| toLeftMovesNim_symm_lt i
    use toLeftMovesAdd (Sum.inl j)
    rw [add_moveLeft_inl, moveLeft_nim]
    exact Equiv.trans (add_congr_left (equiv_nim_grundyValue _)) (hj ▸ Impartial.add_self _)
termination_by G

theorem grundyValue_eq_iff_equiv_nim {G : PGame} [G.Impartial] {o : Nimber} :
    grundyValue G = o ↔ G ≈ nim (toOrdinal o) :=
  ⟨by rintro rfl; exact equiv_nim_grundyValue G,
   by intro h; rw [← nim_equiv_iff_eq]; exact Equiv.trans (Equiv.symm (equiv_nim_grundyValue G)) h⟩

@[simp]
theorem nim_grundyValue (o : Ordinal.{u}) : grundyValue (nim o) = ∗o :=
  grundyValue_eq_iff_equiv_nim.2 PGame.equiv_rfl

theorem grundyValue_eq_iff_equiv (G H : PGame) [G.Impartial] [H.Impartial] :
    grundyValue G = grundyValue H ↔ (G ≈ H) :=
  grundyValue_eq_iff_equiv_nim.trans (equiv_congr_left.1 (equiv_nim_grundyValue H) _).symm

@[simp]
theorem grundyValue_zero : grundyValue 0 = 0 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_zero_equiv)

theorem grundyValue_iff_equiv_zero (G : PGame) [G.Impartial] : grundyValue G = 0 ↔ G ≈ 0 := by
  rw [← grundyValue_eq_iff_equiv, grundyValue_zero]

@[simp]
theorem grundyValue_star : grundyValue star = 1 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_one_equiv)

@[simp]
theorem grundyValue_neg (G : PGame) [G.Impartial] : grundyValue (-G) = grundyValue G := by
  rw [grundyValue_eq_iff_equiv_nim, neg_equiv_iff, neg_nim, ← grundyValue_eq_iff_equiv_nim]

theorem grundyValue_eq_sInf_moveRight (G : PGame) [G.Impartial] :
    grundyValue G = sInf (Set.range (grundyValue ∘ G.moveRight))ᶜ := by
  obtain ⟨l, r, L, R⟩ := G
  rw [← grundyValue_neg, grundyValue_eq_sInf_moveLeft]
  iterate 3 apply congr_arg
  ext i
  exact @grundyValue_neg _ (@Impartial.moveRight_impartial ⟨l, r, L, R⟩ _ _)

theorem grundyValue_ne_moveRight {G : PGame} [G.Impartial] (i : G.RightMoves) :
    grundyValue (G.moveRight i) ≠ grundyValue G := by
  convert grundyValue_ne_moveLeft (toLeftMovesNeg i) using 1 <;> simp

theorem le_grundyValue_of_Iio_subset_moveRight {G : PGame} [G.Impartial] {o : Nimber}
    (h : Set.Iio o ⊆ Set.range (grundyValue ∘ G.moveRight)) : o ≤ grundyValue G := by
  by_contra! ho
  obtain ⟨i, hi⟩ := h ho
  exact grundyValue_ne_moveRight i hi

theorem exists_grundyValue_moveRight_of_lt {G : PGame} [G.Impartial] {o : Nimber}
    (h : o < grundyValue G) : ∃ i, grundyValue (G.moveRight i) = o := by
  rw [← grundyValue_neg] at h
  obtain ⟨i, hi⟩ := exists_grundyValue_moveLeft_of_lt h
  use toLeftMovesNeg.symm i
  rwa [← grundyValue_neg, ← moveLeft_neg]

theorem grundyValue_le_of_forall_moveRight {G : PGame} [G.Impartial] {o : Nimber}
    (h : ∀ i, grundyValue (G.moveRight i) ≠ o) : G.grundyValue ≤ o := by
  contrapose! h
  exact exists_grundyValue_moveRight_of_lt h

/-- The Grundy value of the sum of two nim games equals their nimber addition. -/
theorem grundyValue_nim_add_nim (x y : Ordinal) : grundyValue (nim x + nim y) = ∗x + ∗y := by
  apply (grundyValue_le_of_forall_moveLeft _).antisymm (le_grundyValue_of_Iio_subset_moveLeft _)
  · intro i
    apply leftMoves_add_cases i <;> intro j <;> have := (toLeftMovesNim_symm_lt j).ne
    · simpa [grundyValue_nim_add_nim (toLeftMovesNim.symm j) y]
    · simpa [grundyValue_nim_add_nim x (toLeftMovesNim.symm j)]
  · intro k hk
    obtain h | h := Nimber.lt_add_cases hk
    · let a := toOrdinal (k + ∗y)
      use toLeftMovesAdd (Sum.inl (toLeftMovesNim ⟨a, h⟩))
      simp [a, grundyValue_nim_add_nim a y]
    · let a := toOrdinal (k + ∗x)
      use toLeftMovesAdd (Sum.inr (toLeftMovesNim ⟨a, h⟩))
      simp [a, grundyValue_nim_add_nim x a, add_comm (∗x)]
termination_by (x, y)

theorem nim_add_nim_equiv (x y : Ordinal) :
    nim x + nim y ≈ nim (toOrdinal (∗x + ∗y)) := by
  rw [← grundyValue_eq_iff_equiv_nim, grundyValue_nim_add_nim]

@[simp]
theorem grundyValue_add (G H : PGame) [G.Impartial] [H.Impartial] :
    grundyValue (G + H) = grundyValue G + grundyValue H := by
  rw [← (grundyValue G).toOrdinal_toNimber, ← (grundyValue H).toOrdinal_toNimber,
    ← grundyValue_nim_add_nim, grundyValue_eq_iff_equiv]
  exact add_congr (equiv_nim_grundyValue G) (equiv_nim_grundyValue H)

end PGame

end SetTheory
