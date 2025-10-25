/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "This module is now at `CombinatorialGames.Game.Birthday` in the CGT repo <https://github.com/vihdzp/combinatorial-games>"
  (since := "2025-08-06")

/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial game theory. One is
the birthday of a pre-game, which represents the "step" at which it is constructed. We define it
recursively as the least ordinal larger than the birthdays of its left and right options. On the
other hand, the birthday of a game is the smallest birthday among all pre-games that quotient to it.

The birthday of a pre-game can be understood as representing the depth of its game tree. On the
other hand, the birthday of a game more closely matches Conway's original description. The lemma
`SetTheory.Game.birthday_eq_pGameBirthday` links both definitions together.

# Main declarations

- `SetTheory.PGame.birthday`: The birthday of a pre-game.
- `SetTheory.Game.birthday`: The birthday of a game.

# Todo

- Characterize the birthdays of other basic arithmetical operations.
-/

universe u

open Ordinal

namespace SetTheory

open scoped NaturalOps PGame

namespace PGame

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : PGame.{u} → Ordinal.{u}
  | ⟨_, _, xL, xR⟩ =>
    max (lsub.{u, u} fun i => birthday (xL i)) (lsub.{u, u} fun i => birthday (xR i))

theorem birthday_def (x : PGame) :
    birthday x =
      max (lsub.{u, u} fun i => birthday (x.moveLeft i))
        (lsub.{u, u} fun i => birthday (x.moveRight i)) := by
  cases x; rw [birthday]; rfl

theorem birthday_moveLeft_lt {x : PGame} (i : x.LeftMoves) :
    (x.moveLeft i).birthday < x.birthday := by
  cases x; rw [birthday]; exact lt_max_of_lt_left (lt_lsub _ i)

theorem birthday_moveRight_lt {x : PGame} (i : x.RightMoves) :
    (x.moveRight i).birthday < x.birthday := by
  cases x; rw [birthday]; exact lt_max_of_lt_right (lt_lsub _ i)

theorem lt_birthday_iff {x : PGame} {o : Ordinal} :
    o < x.birthday ↔
      (∃ i : x.LeftMoves, o ≤ (x.moveLeft i).birthday) ∨
        ∃ i : x.RightMoves, o ≤ (x.moveRight i).birthday := by
  constructor
  · rw [birthday_def]
    intro h
    rcases lt_max_iff.1 h with h' | h'
    · left
      rwa [lt_lsub_iff] at h'
    · right
      rwa [lt_lsub_iff] at h'
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hi.trans_lt (birthday_moveLeft_lt i)
    · exact hi.trans_lt (birthday_moveRight_lt i)

theorem Relabelling.birthday_congr : ∀ {x y : PGame.{u}}, x ≡r y → birthday x = birthday y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, r => by
    unfold birthday
    congr 1
    all_goals
      apply lsub_eq_of_range_eq.{u, u, u}
      ext i; constructor
    all_goals rintro ⟨j, rfl⟩
    · exact ⟨_, (r.moveLeft j).birthday_congr.symm⟩
    · exact ⟨_, (r.moveLeftSymm j).birthday_congr⟩
    · exact ⟨_, (r.moveRight j).birthday_congr.symm⟩
    · exact ⟨_, (r.moveRightSymm j).birthday_congr⟩

@[simp]
theorem birthday_eq_zero {x : PGame} :
    birthday x = 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves := by
  rw [birthday_def, max_eq_zero, lsub_eq_zero_iff, lsub_eq_zero_iff]

@[simp]
theorem birthday_zero : birthday 0 = 0 := by simp [inferInstanceAs (IsEmpty PEmpty)]

@[simp]
theorem birthday_one : birthday 1 = 1 := by rw [birthday_def]; simp

@[simp]
theorem birthday_star : birthday star = 1 := by rw [birthday_def]; simp

@[simp]
theorem birthday_neg : ∀ x : PGame, (-x).birthday = x.birthday
  | ⟨xl, xr, xL, xR⟩ => by
    rw [birthday_def, birthday_def, max_comm]
    congr <;> funext <;> apply birthday_neg

@[simp]
theorem birthday_ordinalToPGame (o : Ordinal) : o.toPGame.birthday = o := by
  induction o using Ordinal.induction with | _ o IH
  rw [toPGame, PGame.birthday]
  simp only [lsub_empty, max_zero_right]
  conv_rhs => rw [← lsub_typein o]
  congr with x
  exact IH _ (typein_lt_self x)

theorem le_birthday : ∀ x : PGame, x ≤ x.birthday.toPGame
  | ⟨xl, _, xL, _⟩ =>
    le_def.2
      ⟨fun i =>
        Or.inl ⟨toLeftMovesToPGame ⟨_, birthday_moveLeft_lt i⟩, by simp [le_birthday (xL i)]⟩,
        isEmptyElim⟩

variable (x : PGame.{u})

theorem neg_birthday_le : -x.birthday.toPGame ≤ x := by
  simpa only [birthday_neg, ← neg_le_iff] using le_birthday (-x)

@[simp]
theorem birthday_add : ∀ x y : PGame.{u}, (x + y).birthday = x.birthday ♯ y.birthday
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    rw [birthday_def, nadd, lsub_sum, lsub_sum]
    simp only [mk_add_moveLeft_inl, mk_add_moveLeft_inr, mk_add_moveRight_inl, mk_add_moveRight_inr,
      moveLeft_mk, moveRight_mk]
    conv_lhs => left; left; right; intro a; rw [birthday_add (xL a) ⟨yl, yr, yL, yR⟩]
    conv_lhs => left; right; right; intro b; rw [birthday_add ⟨xl, xr, xL, xR⟩ (yL b)]
    conv_lhs => right; left; right; intro a; rw [birthday_add (xR a) ⟨yl, yr, yL, yR⟩]
    conv_lhs => right; right; right; intro b; rw [birthday_add ⟨xl, xr, xL, xR⟩ (yR b)]
    rw [max_max_max_comm]
    congr <;> apply le_antisymm
    any_goals
      refine max_le_iff.2 ⟨?_, ?_⟩
      all_goals
        refine lsub_le_iff.2 fun i ↦ ?_
        rw [← Order.succ_le_iff]
        refine Ordinal.le_iSup (fun _ : Set.Iio _ ↦ _) ⟨_, ?_⟩
        apply_rules [birthday_moveLeft_lt, birthday_moveRight_lt]
    all_goals
      rw [Ordinal.iSup_le_iff]
      rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ | ⟨j, hj⟩ := lt_birthday_iff.1 hi <;> rw [Order.succ_le_iff]
    · exact lt_max_of_lt_left ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _))
    · exact lt_max_of_lt_right ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _))
    · exact lt_max_of_lt_left ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))
    · exact lt_max_of_lt_right ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))
termination_by a b => (a, b)

@[simp]
theorem birthday_sub (x y : PGame) : (x - y).birthday = x.birthday ♯ y.birthday := by
  apply (birthday_add x _).trans
  rw [birthday_neg]

@[simp]
theorem birthday_natCast : ∀ n : ℕ, birthday n = n
  | 0 => birthday_zero
  | n + 1 => by simp [birthday_natCast]

end PGame

namespace Game

/-- The birthday of a game is defined as the least birthday among all pre-games that define it. -/
noncomputable def birthday (x : Game.{u}) : Ordinal.{u} :=
  sInf (PGame.birthday '' (Quotient.mk' ⁻¹' {x}))

theorem birthday_eq_pGameBirthday (x : Game) :
    ∃ y : PGame.{u}, ⟦y⟧ = x ∧ y.birthday = birthday x := by
  refine csInf_mem (Set.image_nonempty.2 ?_)
  exact ⟨_, x.out_eq⟩

theorem birthday_quot_le_pGameBirthday (x : PGame) : birthday ⟦x⟧ ≤ x.birthday :=
  csInf_le' ⟨x, rfl, rfl⟩

@[simp]
theorem birthday_zero : birthday 0 = 0 := by
  rw [← Ordinal.le_zero, ← PGame.birthday_zero]
  exact birthday_quot_le_pGameBirthday _

@[simp]
theorem birthday_eq_zero {x : Game} : birthday x = 0 ↔ x = 0 := by
  constructor
  · intro h
    let ⟨y, hy₁, hy₂⟩ := birthday_eq_pGameBirthday x
    rw [← hy₁]
    rw [h, PGame.birthday_eq_zero] at hy₂
    exact PGame.game_eq (@PGame.Equiv.isEmpty _ hy₂.1 hy₂.2)
  · rintro rfl
    exact birthday_zero

@[simp]
theorem birthday_ordinalToGame (o : Ordinal) : birthday o.toGame = o := by
  apply le_antisymm
  · conv_rhs => rw [← PGame.birthday_ordinalToPGame o]
    apply birthday_quot_le_pGameBirthday
  · let ⟨x, hx₁, hx₂⟩ := birthday_eq_pGameBirthday o.toGame
    rw [← hx₂, ← toPGame_le_iff]
    rw [← mk_toPGame, ← PGame.equiv_iff_game_eq] at hx₁
    exact hx₁.2.trans (PGame.le_birthday x)

@[simp, norm_cast]
theorem birthday_natCast (n : ℕ) : birthday n = n := by
  rw [← toGame_natCast]
  exact birthday_ordinalToGame _

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] :
    birthday ofNat(n) = OfNat.ofNat n :=
  birthday_natCast n

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  rw [← Nat.cast_one, birthday_natCast, Nat.cast_one]

@[simp]
theorem birthday_star : birthday ⟦PGame.star⟧ = 1 := by
  apply le_antisymm
  · rw [← PGame.birthday_star]
    exact birthday_quot_le_pGameBirthday _
  · rw [Ordinal.one_le_iff_ne_zero, ne_eq, birthday_eq_zero, Game.zero_def,
      ← PGame.equiv_iff_game_eq]
    exact PGame.star_fuzzy_zero.not_equiv

private theorem birthday_neg' (x : Game) : (-x).birthday ≤ x.birthday := by
  let ⟨y, hy₁, hy₂⟩ := birthday_eq_pGameBirthday x
  rw [← hy₂, ← PGame.birthday_neg y]
  conv_lhs => rw [← hy₁]
  apply birthday_quot_le_pGameBirthday

@[simp]
theorem birthday_neg (x : Game) : (-x).birthday = x.birthday := by
  apply le_antisymm (birthday_neg' x)
  conv_lhs => rw [← neg_neg x]
  exact birthday_neg' _

theorem le_birthday (x : Game) : x ≤ x.birthday.toGame := by
  let ⟨y, hy₁, hy₂⟩ := birthday_eq_pGameBirthday x
  rw [← hy₁]
  apply (y.le_birthday).trans
  rw [toPGame_le_iff, hy₁, hy₂]

theorem neg_birthday_le (x : Game) : -x.birthday.toGame ≤ x := by
  rw [neg_le, ← birthday_neg]
  exact le_birthday _

theorem birthday_add_le (x y : Game) : (x + y).birthday ≤ x.birthday ♯ y.birthday := by
  let ⟨a, ha₁, ha₂⟩ := birthday_eq_pGameBirthday x
  let ⟨b, hb₁, hb₂⟩ := birthday_eq_pGameBirthday y
  rw [← ha₂, ← hb₂, ← ha₁, ← hb₁, ← PGame.birthday_add]
  exact birthday_quot_le_pGameBirthday _

theorem birthday_sub_le (x y : Game) : (x - y).birthday ≤ x.birthday ♯ y.birthday := by
  apply (birthday_add_le x _).trans_eq
  rw [birthday_neg]

/- The bound `(x * y).birthday ≤ x.birthday ⨳ y.birthday` is currently an open problem. See
  https://mathoverflow.net/a/476829/147705. -/

/-- Games with bounded birthday are a small set. -/
theorem small_setOf_birthday_lt (o : Ordinal) : Small.{u} {x : Game.{u} // birthday x < o} := by
  induction o using Ordinal.induction with | h o IH =>
  let S := ⋃ a ∈ Set.Iio o, {x : Game.{u} | birthday x < a}
  let H : Small.{u} S := @small_biUnion _ _ _ _ _ IH
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_isSuccLimit o
  · simp_rw [Ordinal.not_lt_zero]
    exact small_empty
  · simp_rw [Order.lt_succ_iff, le_iff_lt_or_eq]
    convert small_union.{u} {x | birthday x < a} {x | birthday x = a}
    · exact IH _ (Order.lt_succ a)
    · let f (g : Set S × Set S) : Game := ⟦PGame.mk _ _
        (fun x ↦ ((equivShrink g.1).symm x).1.1.out) (fun x ↦ ((equivShrink g.2).symm x).1.1.out)⟧
      suffices {x | x.birthday = a} ⊆ Set.range f from small_subset this
      rintro x rfl
      obtain ⟨y, rfl, hy'⟩ := birthday_eq_pGameBirthday x
      refine ⟨⟨{z | ∃ i, ⟦y.moveLeft i⟧ = z.1}, {z | ∃ i, ⟦y.moveRight i⟧ = z.1}⟩, ?_⟩
      apply PGame.game_eq <| PGame.Equiv.of_exists _ _ _ _ <;> intro i
      · obtain ⟨j, hj⟩ := ((equivShrink _).symm i).2
        exact ⟨j, by simp [PGame.equiv_iff_game_eq, hj]⟩
      · obtain ⟨j, hj⟩ := ((equivShrink _).symm i).2
        exact ⟨j, by simp [PGame.equiv_iff_game_eq, hj]⟩
      · refine ⟨equivShrink _ ⟨⟨⟦y.moveLeft i⟧, ?_⟩, i, rfl⟩, by simpa using Quotient.mk_out _⟩
        suffices ∃ b ≤ y.birthday, birthday ⟦y.moveLeft i⟧ < b by simpa [S, hy'] using this
        refine ⟨_, le_rfl, ?_⟩
        exact (birthday_quot_le_pGameBirthday _).trans_lt (PGame.birthday_moveLeft_lt i)
      · refine ⟨equivShrink _ ⟨⟨⟦y.moveRight i⟧, ?_⟩, i, rfl⟩, by simpa using Quotient.mk_out _⟩
        suffices ∃ b ≤ y.birthday, birthday ⟦y.moveRight i⟧ < b by simpa [S, hy'] using this
        refine ⟨_, le_rfl, ?_⟩
        exact (birthday_quot_le_pGameBirthday _).trans_lt (PGame.birthday_moveRight_lt i)
  · convert H
    change birthday _ < o ↔ ∃ a, _
    simpa using ho.lt_iff_exists_lt

end Game

end SetTheory
