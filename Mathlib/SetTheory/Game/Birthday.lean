/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.SetTheory.Ordinal.NaturalOps

#align_import set_theory.game.birthday from "leanprover-community/mathlib"@"a347076985674932c0e91da09b9961ed0a79508c"

/-!
# Birthdays of games

The birthday of a game is an ordinal that represents at which "step" the game was constructed. We
define it recursively as the least ordinal larger than the birthdays of its left and right games. We
prove the basic properties about these.

# Main declarations

- `PGame.birthday`: The birthday of a pre-game.

# Todo

- Define the birthdays of `Game`s and `Surreal`s.
- Characterize the birthdays of basic arithmetical operations.
-/


universe u

open Ordinal

open scoped NaturalOps PGame

namespace PGame

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : PGame.{u} → Ordinal.{u}
  | ⟨_, _, xL, xR⟩ =>
    max (lsub.{u, u} fun i => birthday (xL i)) (lsub.{u, u} fun i => birthday (xR i))
#align pgame.birthday PGame.birthday

theorem birthday_def (x : PGame) :
    birthday x =
      max (lsub.{u, u} fun i => birthday (x.moveLeft i))
        (lsub.{u, u} fun i => birthday (x.moveRight i)) := by
  cases x; rw [birthday]; rfl
  -- ⊢ birthday (mk α✝ β✝ a✝¹ a✝) = max (lsub fun i => birthday (moveLeft (mk α✝ β✝ …
           -- ⊢ max (lsub fun i => birthday (a✝¹ i)) (lsub fun i => birthday (a✝ i)) = max ( …
                          -- 🎉 no goals
#align pgame.birthday_def PGame.birthday_def

theorem birthday_moveLeft_lt {x : PGame} (i : x.LeftMoves) : (x.moveLeft i).birthday < x.birthday :=
  by cases x; rw [birthday]; exact lt_max_of_lt_left (lt_lsub _ i)
     -- ⊢ birthday (moveLeft (mk α✝ β✝ a✝¹ a✝) i) < birthday (mk α✝ β✝ a✝¹ a✝)
              -- ⊢ birthday (moveLeft (mk α✝ β✝ a✝¹ a✝) i) < max (lsub fun i => birthday (a✝¹ i …
                             -- 🎉 no goals
#align pgame.birthday_move_left_lt PGame.birthday_moveLeft_lt

theorem birthday_moveRight_lt {x : PGame} (i : x.RightMoves) :
    (x.moveRight i).birthday < x.birthday := by
  cases x; rw [birthday]; exact lt_max_of_lt_right (lt_lsub _ i)
  -- ⊢ birthday (moveRight (mk α✝ β✝ a✝¹ a✝) i) < birthday (mk α✝ β✝ a✝¹ a✝)
           -- ⊢ birthday (moveRight (mk α✝ β✝ a✝¹ a✝) i) < max (lsub fun i => birthday (a✝¹  …
                          -- 🎉 no goals
#align pgame.birthday_move_right_lt PGame.birthday_moveRight_lt

theorem lt_birthday_iff {x : PGame} {o : Ordinal} :
    o < x.birthday ↔
      (∃ i : x.LeftMoves, o ≤ (x.moveLeft i).birthday) ∨
        ∃ i : x.RightMoves, o ≤ (x.moveRight i).birthday := by
  constructor
  -- ⊢ o < birthday x → (∃ i, o ≤ birthday (moveLeft x i)) ∨ ∃ i, o ≤ birthday (mov …
  · rw [birthday_def]
    -- ⊢ o < max (lsub fun i => birthday (moveLeft x i)) (lsub fun i => birthday (mov …
    intro h
    -- ⊢ (∃ i, o ≤ birthday (moveLeft x i)) ∨ ∃ i, o ≤ birthday (moveRight x i)
    cases' lt_max_iff.1 h with h' h'
    -- ⊢ (∃ i, o ≤ birthday (moveLeft x i)) ∨ ∃ i, o ≤ birthday (moveRight x i)
    · left
      -- ⊢ ∃ i, o ≤ birthday (moveLeft x i)
      rwa [lt_lsub_iff] at h'
      -- 🎉 no goals
    · right
      -- ⊢ ∃ i, o ≤ birthday (moveRight x i)
      rwa [lt_lsub_iff] at h'
      -- 🎉 no goals
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    -- ⊢ o < birthday x
    · exact hi.trans_lt (birthday_moveLeft_lt i)
      -- 🎉 no goals
    · exact hi.trans_lt (birthday_moveRight_lt i)
      -- 🎉 no goals
#align pgame.lt_birthday_iff PGame.lt_birthday_iff

theorem Relabelling.birthday_congr : ∀ {x y : PGame.{u}}, x ≡r y → birthday x = birthday y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, r => by
    unfold birthday
    -- ⊢ max (lsub fun i => birthday (xL i)) (lsub fun i => birthday (xR i)) = max (l …
    congr 1
    -- ⊢ (lsub fun i => birthday (xL i)) = lsub fun i => birthday (yL i)
    all_goals
      apply lsub_eq_of_range_eq.{u, u, u}
      ext i; constructor
    all_goals rintro ⟨j, rfl⟩
    · exact ⟨_, (r.moveLeft j).birthday_congr.symm⟩
      -- 🎉 no goals
    · exact ⟨_, (r.moveLeftSymm j).birthday_congr⟩
      -- 🎉 no goals
    · exact ⟨_, (r.moveRight j).birthday_congr.symm⟩
      -- 🎉 no goals
    · exact ⟨_, (r.moveRightSymm j).birthday_congr⟩
      -- 🎉 no goals
termination_by birthday_congr x y _ => (x, y)
#align pgame.relabelling.birthday_congr PGame.Relabelling.birthday_congr

@[simp]
theorem birthday_eq_zero {x : PGame} :
    birthday x = 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves := by
  rw [birthday_def, max_eq_zero, lsub_eq_zero_iff, lsub_eq_zero_iff]
  -- 🎉 no goals
#align pgame.birthday_eq_zero PGame.birthday_eq_zero

@[simp]
theorem birthday_zero : birthday 0 = 0 := by simp [inferInstanceAs (IsEmpty PEmpty)]
                                             -- 🎉 no goals
#align pgame.birthday_zero PGame.birthday_zero

@[simp]
theorem birthday_one : birthday 1 = 1 := by rw [birthday_def]; simp
                                            -- ⊢ max (lsub fun i => birthday (moveLeft 1 i)) (lsub fun i => birthday (moveRig …
                                                               -- 🎉 no goals
#align pgame.birthday_one PGame.birthday_one

@[simp]
theorem birthday_star : birthday star = 1 := by rw [birthday_def]; simp
                                                -- ⊢ max (lsub fun i => birthday (moveLeft star i)) (lsub fun i => birthday (move …
                                                                   -- 🎉 no goals
#align pgame.birthday_star PGame.birthday_star

@[simp]
theorem neg_birthday : ∀ x : PGame, (-x).birthday = x.birthday
  | ⟨xl, xr, xL, xR⟩ => by
    rw [birthday_def, birthday_def, max_comm]
    -- ⊢ max (lsub fun i => birthday (moveRight (-mk xl xr xL xR) i)) (lsub fun i =>  …
    congr <;> funext <;> apply neg_birthday
    -- ⊢ (fun i => birthday (moveRight (-mk xl xr xL xR) i)) = fun i => birthday (mov …
              -- ⊢ birthday (moveRight (-mk xl xr xL xR) x✝) = birthday (moveLeft (mk xl xr xL  …
              -- ⊢ birthday (moveLeft (-mk xl xr xL xR) x✝) = birthday (moveRight (mk xl xr xL  …
                         -- 🎉 no goals
                         -- 🎉 no goals
#align pgame.neg_birthday PGame.neg_birthday

@[simp]
theorem toPGame_birthday (o : Ordinal) : o.toPGame.birthday = o := by
  induction' o using Ordinal.induction with o IH
  -- ⊢ birthday (toPGame o) = o
  rw [toPGame_def, PGame.birthday]
  -- ⊢ max (lsub fun i => birthday (toPGame (typein (fun x x_1 => x < x_1) i))) (ls …
  simp only [lsub_empty, max_zero_right]
  -- ⊢ (lsub fun i => birthday (toPGame (typein (fun x x_1 => x < x_1) i))) = o
  -- Porting note: was `nth_rw 1 [← lsub_typein o]`
  conv_rhs => rw [← lsub_typein o]
  -- ⊢ (lsub fun i => birthday (toPGame (typein (fun x x_1 => x < x_1) i))) = lsub  …
  congr with x
  -- ⊢ birthday (toPGame (typein (fun x x_1 => x < x_1) x)) = typein (fun x x_1 =>  …
  exact IH _ (typein_lt_self x)
  -- 🎉 no goals
#align pgame.to_pgame_birthday PGame.toPGame_birthday

theorem le_birthday : ∀ x : PGame, x ≤ x.birthday.toPGame
  | ⟨xl, _, xL, _⟩ =>
    le_def.2
      ⟨fun i =>
        Or.inl ⟨toLeftMovesToPGame ⟨_, birthday_moveLeft_lt i⟩, by simp [le_birthday (xL i)]⟩,
                                                                   -- 🎉 no goals
        isEmptyElim⟩
#align pgame.le_birthday PGame.le_birthday

variable (a b x : PGame.{u})

theorem neg_birthday_le : -x.birthday.toPGame ≤ x := by
  simpa only [neg_birthday, ← neg_le_iff] using le_birthday (-x)
  -- 🎉 no goals
#align pgame.neg_birthday_le PGame.neg_birthday_le

@[simp]
theorem birthday_add : ∀ x y : PGame.{u}, (x + y).birthday = x.birthday ♯ y.birthday
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    rw [birthday_def, nadd_def]
    -- ⊢ max (lsub fun i => birthday (moveLeft (mk xl xr xL xR + mk yl yr yL yR) i))  …
    -- Porting note: `simp` doesn't apply
    erw [lsub_sum, lsub_sum]
    -- ⊢ max (max (lsub fun a => birthday (moveLeft (mk xl xr xL xR + mk yl yr yL yR) …
    simp only [lsub_sum, mk_add_moveLeft_inl, moveLeft_mk, mk_add_moveLeft_inr,
      mk_add_moveRight_inl, moveRight_mk, mk_add_moveRight_inr]
    -- Porting note: Originally `simp only [birthday_add]`, but this causes an error in
    -- `termination_by`. Use a workaround.
    conv_lhs => left; left; right; intro a; rw [birthday_add (xL a) ⟨yl, yr, yL, yR⟩]
    -- ⊢ max (max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub f …
    conv_lhs => left; right; right; intro b; rw [birthday_add ⟨xl, xr, xL, xR⟩ (yL b)]
    -- ⊢ max (max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub f …
    conv_lhs => right; left; right; intro a; rw [birthday_add (xR a) ⟨yl, yr, yL, yR⟩]
    -- ⊢ max (max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub f …
    conv_lhs => right; right; right; intro b; rw [birthday_add ⟨xl, xr, xL, xR⟩ (yR b)]
    -- ⊢ max (max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub f …
    rw [max_max_max_comm]
    -- ⊢ max (max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub f …
    congr <;> apply le_antisymm
    -- ⊢ max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub fun a  …
              -- ⊢ max (lsub fun a => birthday (xL a) ♯ birthday (mk yl yr yL yR)) (lsub fun a  …
              -- ⊢ max (lsub fun b => birthday (mk xl xr xL xR) ♯ birthday (yL b)) (lsub fun b  …
    any_goals
      exact
        max_le_iff.2
          ⟨lsub_le_iff.2 fun i => lt_blsub _ _ (birthday_moveLeft_lt _),
            lsub_le_iff.2 fun i => lt_blsub _ _ (birthday_moveRight_lt _)⟩
    all_goals
      refine blsub_le_iff.2 fun i hi => ?_
      rcases lt_birthday_iff.1 hi with (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact lt_max_of_lt_left ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _))
      -- 🎉 no goals
    · exact lt_max_of_lt_right ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _))
      -- 🎉 no goals
    · exact lt_max_of_lt_left ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))
      -- 🎉 no goals
    · exact lt_max_of_lt_right ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))
      -- 🎉 no goals
termination_by birthday_add a b => (a, b)
#align pgame.birthday_add PGame.birthday_add

theorem birthday_add_zero : (a + 0).birthday = a.birthday := by simp
                                                                -- 🎉 no goals
#align pgame.birthday_add_zero PGame.birthday_add_zero

theorem birthday_zero_add : (0 + a).birthday = a.birthday := by simp
                                                                -- 🎉 no goals
#align pgame.birthday_zero_add PGame.birthday_zero_add

theorem birthday_add_one : (a + 1).birthday = Order.succ a.birthday := by simp
                                                                          -- 🎉 no goals
#align pgame.birthday_add_one PGame.birthday_add_one

theorem birthday_one_add : (1 + a).birthday = Order.succ a.birthday := by simp
                                                                          -- 🎉 no goals
#align pgame.birthday_one_add PGame.birthday_one_add

@[simp]
theorem birthday_nat_cast : ∀ n : ℕ, birthday n = n
  | 0 => birthday_zero
  | n + 1 => by simp [birthday_nat_cast]
                -- 🎉 no goals
#align pgame.birthday_nat_cast PGame.birthday_nat_cast

theorem birthday_add_nat (n : ℕ) : (a + n).birthday = a.birthday + n := by simp
                                                                           -- 🎉 no goals
#align pgame.birthday_add_nat PGame.birthday_add_nat

theorem birthday_nat_add (n : ℕ) : (↑n + a).birthday = a.birthday + n := by simp
                                                                            -- 🎉 no goals
#align pgame.birthday_nat_add PGame.birthday_nat_add

end PGame
