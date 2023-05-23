/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade

! This file was ported from Lean 3 source module set_theory.game.basic
! leanprover-community/mathlib commit 6623e6af705e97002a9054c1c05a980180276fc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.SetTheory.Game.Pgame
import Mathlib.Tactic.Abel

/-!
# Combinatorial games.

In this file we define the quotient of pre-games by the equivalence relation
`p ≈ q ↔ p ≤ q ∧ q ≤ p` (its `antisymmetrization`), and construct an instance `add_comm_group game`,
as well as an instance `partial_order game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/


open Function PGame

open PGame

universe u

instance PGame.setoid : Setoid PGame :=
  ⟨(· ≈ ·), equiv_refl, @PGame.Equiv.symm, @PGame.Equiv.trans⟩
#align pgame.setoid PGame.setoid

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbrev Game :=
  Quotient PGame.setoid
#align game Game

namespace Game

instance : AddCommGroupWithOne Game where
  zero := ⟦0⟧
  one := ⟦1⟧
  neg := Quot.lift (fun x => ⟦-x⟧) fun x y h => Quot.sound ((@neg_equiv_neg_iff x y).2 h)
  add :=
    Quotient.lift₂ (fun x y : PGame => ⟦x + y⟧) fun x₁ y₁ x₂ y₂ hx hy =>
      Quot.sound (PGame.add_congr hx hy)
  add_zero := by
    rintro ⟨x⟩
    exact Quot.sound (add_zero_equiv x)
  zero_add := by
    rintro ⟨x⟩
    exact Quot.sound (zero_add_equiv x)
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact Quot.sound add_assoc_equiv
  add_left_neg := by
    rintro ⟨x⟩
    exact Quot.sound (add_left_neg_equiv x)
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    exact Quot.sound add_comm_equiv

instance : Inhabited Game :=
  ⟨0⟩

instance : PartialOrder Game where
  le := Quotient.lift₂ (· ≤ ·) fun x₁ y₁ x₂ y₂ hx hy => propext (le_congr hx hy)
  le_refl := by
    rintro ⟨x⟩
    exact le_refl x
  le_trans := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact @le_trans _ _ x y z
  le_antisymm := by
    rintro ⟨x⟩ ⟨y⟩ h₁ h₂
    apply Quot.sound
    exact ⟨h₁, h₂⟩
  lt := Quotient.lift₂ (· < ·) fun x₁ y₁ x₂ y₂ hx hy => propext (lt_congr hx hy)
  lt_iff_le_not_le := by
    rintro ⟨x⟩ ⟨y⟩
    exact @lt_iff_le_not_le _ _ x y

/-- The less or fuzzy relation on games.

If `0 ⧏ x` (less or fuzzy with), then Left can win `x` as the first player. -/
def Lf : Game → Game → Prop :=
  Quotient.lift₂ Lf fun x₁ y₁ x₂ y₂ hx hy => propext (lf_congr hx hy)
#align game.lf Game.Lf

-- mathport name: «expr ⧏ »
local infixl:50 " ⧏ " => Lf

/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem not_le : ∀ {x y : Game}, ¬x ≤ y ↔ y ⧏ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact PGame.not_le
#align game.not_le Game.not_le

/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem not_lf : ∀ {x y : Game}, ¬x ⧏ y ↔ y ≤ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact not_lf
#align game.not_lf Game.not_lf

instance : IsTrichotomous Game (· ⧏ ·) :=
  ⟨by
    rintro ⟨x⟩ ⟨y⟩
    change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _
    rw [Quotient.eq']
    apply lf_or_equiv_or_gf⟩

/-! It can be useful to use these lemmas to turn `pgame` inequalities into `game` inequalities, as
the `add_comm_group` structure on `game` often simplifies many proofs. -/


theorem PGame.le_iff_game_le {x y : PGame} : x ≤ y ↔ ⟦x⟧ ≤ ⟦y⟧ :=
  Iff.rfl
#align pgame.le_iff_game_le PGame.le_iff_game_le

theorem PGame.lf_iff_game_lf {x y : PGame} : PGame.Lf x y ↔ ⟦x⟧ ⧏ ⟦y⟧ :=
  Iff.rfl
#align pgame.lf_iff_game_lf PGame.lf_iff_game_lf

theorem PGame.lt_iff_game_lt {x y : PGame} : x < y ↔ ⟦x⟧ < ⟦y⟧ :=
  Iff.rfl
#align pgame.lt_iff_game_lt PGame.lt_iff_game_lt

theorem PGame.equiv_iff_game_eq {x y : PGame} : (x ≈ y) ↔ ⟦x⟧ = ⟦y⟧ :=
  (@Quotient.eq' _ _ x y).symm
#align pgame.equiv_iff_game_eq PGame.equiv_iff_game_eq

/-- The fuzzy, confused, or incomparable relation on games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy : Game → Game → Prop :=
  Quotient.lift₂ Fuzzy fun x₁ y₁ x₂ y₂ hx hy => propext (fuzzy_congr hx hy)
#align game.fuzzy Game.Fuzzy

-- mathport name: «expr ‖ »
local infixl:50 " ‖ " => Fuzzy

theorem PGame.fuzzy_iff_game_fuzzy {x y : PGame} : PGame.Fuzzy x y ↔ ⟦x⟧ ‖ ⟦y⟧ :=
  Iff.rfl
#align pgame.fuzzy_iff_game_fuzzy PGame.fuzzy_iff_game_fuzzy

instance covariantClass_add_le : CovariantClass Game Game (· + ·) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_le Game.covariantClass_add_le

instance covariantClass_swap_add_le : CovariantClass Game Game (swap (· + ·)) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_le Game.covariantClass_swap_add_le

instance covariantClass_add_lt : CovariantClass Game Game (· + ·) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_lt Game.covariantClass_add_lt

instance covariantClass_swap_add_lt : CovariantClass Game Game (swap (· + ·)) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_lt Game.covariantClass_swap_add_lt

theorem add_lf_add_right : ∀ {b c : Game} (h : b ⧏ c) (a), b + a ⧏ c + a := by
  rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩
  apply add_lf_add_right h
#align game.add_lf_add_right Game.add_lf_add_right

theorem add_lf_add_left : ∀ {b c : Game} (h : b ⧏ c) (a), a + b ⧏ a + c := by
  rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩
  apply add_lf_add_left h
#align game.add_lf_add_left Game.add_lf_add_left

instance orderedAddCommGroup : OrderedAddCommGroup Game :=
  { Game.addCommGroupWithOne, Game.partialOrder with
    add_le_add_left := @add_le_add_left _ _ _ Game.covariantClass_add_le }
#align game.ordered_add_comm_group Game.orderedAddCommGroup

end Game

namespace PGame

@[simp]
theorem quot_neg (a : PGame) : ⟦-a⟧ = -⟦a⟧ :=
  rfl
#align pgame.quot_neg PGame.quot_neg

@[simp]
theorem quot_add (a b : PGame) : ⟦a + b⟧ = ⟦a⟧ + ⟦b⟧ :=
  rfl
#align pgame.quot_add PGame.quot_add

@[simp]
theorem quot_sub (a b : PGame) : ⟦a - b⟧ = ⟦a⟧ - ⟦b⟧ :=
  rfl
#align pgame.quot_sub PGame.quot_sub

theorem quot_eq_of_mk'_quot_eq {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, ⟦x.moveLeft i⟧ = ⟦y.moveLeft (L i)⟧)
    (hr : ∀ j, ⟦x.moveRight j⟧ = ⟦y.moveRight (R j)⟧) : ⟦x⟧ = ⟦y⟧ := by
  simp_rw [Quotient.eq'] at hl hr
  exact Quot.sound (equiv_of_mk_equiv L R hl hr)
#align pgame.quot_eq_of_mk_quot_eq PGame.quot_eq_of_mk'_quot_eq

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/


/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
instance : Mul PGame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr xL xR IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine' ⟨Sum (xl × yl) (xr × yr), Sum (xl × yr) (xr × yl), _, _⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact IHxl i y + IHyl j - IHxl i (yL j)
    · exact IHxr i y + IHyr j - IHxr i (yR j)
    · exact IHxl i y + IHyr j - IHxl i (yR j)
    · exact IHxr i y + IHyl j - IHxr i (yL j)⟩

theorem leftMoves_mul :
    ∀ x y : PGame.{u},
      (x * y).LeftMoves = Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_mul PGame.leftMoves_mul

theorem rightMoves_mul :
    ∀ x y : PGame.{u},
      (x * y).RightMoves = Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_mul PGame.rightMoves_mul

/-- Turns two left or right moves for `x` and `y` into a left move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesMul {x y : PGame} :
    Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves) ≃ (x * y).LeftMoves :=
  Equiv.cast (leftMoves_mul x y).symm
#align pgame.to_left_moves_mul PGame.toLeftMovesMul

/-- Turns a left and a right move for `x` and `y` into a right move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesMul {x y : PGame} :
    Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves) ≃ (x * y).RightMoves :=
  Equiv.cast (rightMoves_mul x y).symm
#align pgame.to_right_moves_mul PGame.toRightMovesMul

@[simp]
theorem mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j :=
  rfl
#align pgame.mk_mul_move_left_inl PGame.mk_mul_moveLeft_inl

@[simp]
theorem mul_moveLeft_inl {x y : PGame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_left_inl PGame.mul_moveLeft_inl

@[simp]
theorem mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j :=
  rfl
#align pgame.mk_mul_move_left_inr PGame.mk_mul_moveLeft_inr

@[simp]
theorem mul_moveLeft_inr {x y : PGame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveRight j - x.moveRight i * y.moveRight j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_left_inr PGame.mul_moveLeft_inr

@[simp]
theorem mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j :=
  rfl
#align pgame.mk_mul_move_right_inl PGame.mk_mul_moveRight_inl

@[simp]
theorem mul_moveRight_inl {x y : PGame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveRight j - x.moveLeft i * y.moveRight j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_right_inl PGame.mul_moveRight_inl

@[simp]
theorem mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j :=
  rfl
#align pgame.mk_mul_move_right_inr PGame.mk_mul_moveRight_inr

@[simp]
theorem mul_moveRight_inr {x y : PGame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveLeft j - x.moveRight i * y.moveLeft j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_right_inr PGame.mul_moveRight_inr

@[simp]
theorem neg_mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inl PGame.neg_mk_mul_moveLeft_inl

@[simp]
theorem neg_mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inr PGame.neg_mk_mul_moveLeft_inr

@[simp]
theorem neg_mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inl PGame.neg_mk_mul_moveRight_inl

@[simp]
theorem neg_mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inr PGame.neg_mk_mul_moveRight_inr

theorem leftMoves_mul_cases {x y : PGame} (k) {P : (x * y).LeftMoves → Prop}
    (hl : ∀ ix iy, P <| toLeftMovesMul (Sum.inl ⟨ix, iy⟩))
    (hr : ∀ jx jy, P <| toLeftMovesMul (Sum.inr ⟨jx, jy⟩)) : P k := by
  rw [← to_left_moves_mul.apply_symm_apply k]
  rcases to_left_moves_mul.symm k with (⟨ix, iy⟩ | ⟨jx, jy⟩)
  · apply hl
  · apply hr
#align pgame.left_moves_mul_cases PGame.leftMoves_mul_cases

theorem rightMoves_mul_cases {x y : PGame} (k) {P : (x * y).RightMoves → Prop}
    (hl : ∀ ix jy, P <| toRightMovesMul (Sum.inl ⟨ix, jy⟩))
    (hr : ∀ jx iy, P <| toRightMovesMul (Sum.inr ⟨jx, iy⟩)) : P k := by
  rw [← to_right_moves_mul.apply_symm_apply k]
  rcases to_right_moves_mul.symm k with (⟨ix, iy⟩ | ⟨jx, jy⟩)
  · apply hl
  · apply hr
#align pgame.right_moves_mul_cases PGame.rightMoves_mul_cases

/-- `x * y` and `y * x` have the same moves. -/
def mulCommRelabelling : ∀ x y : PGame.{u}, x * y ≡r y * x
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine'
            ⟨Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _),
              (Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)),
              _, _⟩ <;>
          rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
        dsimp <;>
      exact
        ((add_comm_relabelling _ _).trans <|
              (mul_comm_relabelling _ _).addCongr (mul_comm_relabelling _ _)).subCongr
          (mul_comm_relabelling _ _)decreasing_by
  pgame_wf_tac
#align pgame.mul_comm_relabelling PGame.mulCommRelabelling

theorem quot_mul_comm (x y : PGame.{u}) : ⟦x * y⟧ = ⟦y * x⟧ :=
  Quot.sound (mulCommRelabelling x y).Equiv
#align pgame.quot_mul_comm PGame.quot_mul_comm

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : PGame) : x * y ≈ y * x :=
  Quotient.exact <| quot_mul_comm _ _
#align pgame.mul_comm_equiv PGame.mul_comm_equiv

instance isEmpty_mul_zero_leftMoves (x : PGame.{u}) : IsEmpty (x * 0).LeftMoves := by
  cases x
  apply Sum.isEmpty
#align pgame.is_empty_mul_zero_left_moves PGame.isEmpty_mul_zero_leftMoves

instance isEmpty_mul_zero_rightMoves (x : PGame.{u}) : IsEmpty (x * 0).RightMoves := by
  cases x
  apply Sum.isEmpty
#align pgame.is_empty_mul_zero_right_moves PGame.isEmpty_mul_zero_rightMoves

instance isEmpty_zero_mul_leftMoves (x : PGame.{u}) : IsEmpty (0 * x).LeftMoves := by
  cases x
  apply Sum.isEmpty
#align pgame.is_empty_zero_mul_left_moves PGame.isEmpty_zero_mul_leftMoves

instance isEmpty_zero_mul_rightMoves (x : PGame.{u}) : IsEmpty (0 * x).RightMoves := by
  cases x
  apply Sum.isEmpty
#align pgame.is_empty_zero_mul_right_moves PGame.isEmpty_zero_mul_rightMoves

/-- `x * 0` has exactly the same moves as `0`. -/
def mulZeroRelabelling (x : PGame) : x * 0 ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.mul_zero_relabelling PGame.mulZeroRelabelling

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : PGame) : x * 0 ≈ 0 :=
  (mulZeroRelabelling x).Equiv
#align pgame.mul_zero_equiv PGame.mul_zero_equiv

@[simp]
theorem quot_mul_zero (x : PGame) : ⟦x * 0⟧ = ⟦0⟧ :=
  @Quotient.sound _ _ (x * 0) _ x.mul_zero_equiv
#align pgame.quot_mul_zero PGame.quot_mul_zero

/-- `0 * x` has exactly the same moves as `0`. -/
def zeroMulRelabelling (x : PGame) : 0 * x ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.zero_mul_relabelling PGame.zeroMulRelabelling

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : PGame) : 0 * x ≈ 0 :=
  (zeroMulRelabelling x).Equiv
#align pgame.zero_mul_equiv PGame.zero_mul_equiv

@[simp]
theorem quot_zero_mul (x : PGame) : ⟦0 * x⟧ = ⟦0⟧ :=
  @Quotient.sound _ _ (0 * x) _ x.zero_mul_equiv
#align pgame.quot_zero_mul PGame.quot_zero_mul

/-- `-x * y` and `-(x * y)` have the same moves. -/
def negMulRelabelling : ∀ x y : PGame.{u}, -x * y ≡r -(x * y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine' ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, _, _⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩) <;> dsimp <;>
          apply ((neg_add_relabelling _ _).trans _).symm <;>
        apply ((neg_add_relabelling _ _).trans (relabelling.add_congr _ _)).subCongr <;>
      exact (neg_mul_relabelling _ _).symm decreasing_by
  pgame_wf_tac
#align pgame.neg_mul_relabelling PGame.negMulRelabelling

@[simp]
theorem quot_neg_mul (x y : PGame) : ⟦-x * y⟧ = -⟦x * y⟧ :=
  Quot.sound (negMulRelabelling x y).Equiv
#align pgame.quot_neg_mul PGame.quot_neg_mul

/-- `x * -y` and `-(x * y)` have the same moves. -/
def mulNegRelabelling (x y : PGame) : x * -y ≡r -(x * y) :=
  (mulCommRelabelling x _).trans <| (negMulRelabelling _ x).trans (mulCommRelabelling y x).negCongr
#align pgame.mul_neg_relabelling PGame.mulNegRelabelling

@[simp]
theorem quot_mul_neg (x y : PGame) : ⟦x * -y⟧ = -⟦x * y⟧ :=
  Quot.sound (mulNegRelabelling x y).Equiv
#align pgame.quot_mul_neg PGame.quot_mul_neg

@[simp]
theorem quot_left_distrib : ∀ x y z : PGame, ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      ·
        rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    · fconstructor
      ·
        rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧ =
            ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧
        simp [quot_left_distrib]
        abel
      · change
          ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧ =
            ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧
        simp [quot_left_distrib]
        abel
      · change
          ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧ =
            ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧
        simp [quot_left_distrib]
        abel
      · change
          ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧ =
            ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧
        simp [quot_left_distrib]
        abel
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧ =
            ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧
        simp [quot_left_distrib]
        abel
      · change
          ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧ =
            ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧
        simp [quot_left_distrib]
        abel
      · change
          ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧ =
            ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧
        simp [quot_left_distrib]
        abel
      · change
          ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧ =
            ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧
        simp [quot_left_distrib]
        abel decreasing_by pgame_wf_tac
#align pgame.quot_left_distrib PGame.quot_left_distrib

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv (x y z : PGame) : x * (y + z) ≈ x * y + x * z :=
  Quotient.exact <| quot_left_distrib _ _ _
#align pgame.left_distrib_equiv PGame.left_distrib_equiv

@[simp]
theorem quot_left_distrib_sub (x y z : PGame) : ⟦x * (y - z)⟧ = ⟦x * y⟧ - ⟦x * z⟧ := by
  change ⟦x * (y + -z)⟧ = ⟦x * y⟧ + -⟦x * z⟧
  rw [quot_left_distrib, quot_mul_neg]
#align pgame.quot_left_distrib_sub PGame.quot_left_distrib_sub

@[simp]
theorem quot_right_distrib (x y z : PGame) : ⟦(x + y) * z⟧ = ⟦x * z⟧ + ⟦y * z⟧ := by
  simp only [quot_mul_comm, quot_left_distrib]
#align pgame.quot_right_distrib PGame.quot_right_distrib

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : PGame) : (x + y) * z ≈ x * z + y * z :=
  Quotient.exact <| quot_right_distrib _ _ _
#align pgame.right_distrib_equiv PGame.right_distrib_equiv

@[simp]
theorem quot_right_distrib_sub (x y z : PGame) : ⟦(y - z) * x⟧ = ⟦y * x⟧ - ⟦z * x⟧ := by
  change ⟦(y + -z) * x⟧ = ⟦y * x⟧ + -⟦z * x⟧
  rw [quot_right_distrib, quot_neg_mul]
#align pgame.quot_right_distrib_sub PGame.quot_right_distrib_sub

/-- `x * 1` has the same moves as `x`. -/
def mulOneRelabelling : ∀ x : PGame.{u}, x * 1 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    unfold One.one
    refine'
                  ⟨(Equiv.sumEmpty _ _).trans (Equiv.prodPUnit _),
                    (Equiv.emptySum _ _).trans (Equiv.prodPUnit _), _, _⟩ <;>
                try rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩) <;>
              try intro i <;>
            dsimp <;>
          apply (relabelling.sub_congr (relabelling.refl _) (mul_zero_relabelling _)).trans <;>
        rw [sub_zero] <;>
      exact
        (add_zero_relabelling _).trans
          (((mul_one_relabelling _).addCongr (mul_zero_relabelling _)).trans <|
            add_zero_relabelling _)
#align pgame.mul_one_relabelling PGame.mulOneRelabelling

@[simp]
theorem quot_mul_one (x : PGame) : ⟦x * 1⟧ = ⟦x⟧ :=
  Quot.sound <| mulOneRelabelling x
#align pgame.quot_mul_one PGame.quot_mul_one

/-- `x * 1` is equivalent to `x`. -/
theorem mul_one_equiv (x : PGame) : x * 1 ≈ x :=
  Quotient.exact <| quot_mul_one x
#align pgame.mul_one_equiv PGame.mul_one_equiv

/-- `1 * x` has the same moves as `x`. -/
def oneMulRelabelling (x : PGame) : 1 * x ≡r x :=
  (mulCommRelabelling 1 x).trans <| mulOneRelabelling x
#align pgame.one_mul_relabelling PGame.oneMulRelabelling

@[simp]
theorem quot_one_mul (x : PGame) : ⟦1 * x⟧ = ⟦x⟧ :=
  Quot.sound <| oneMulRelabelling x
#align pgame.quot_one_mul PGame.quot_one_mul

/-- `1 * x` is equivalent to `x`. -/
theorem one_mul_equiv (x : PGame) : 1 * x ≈ x :=
  Quotient.exact <| quot_one_mul x
#align pgame.one_mul_equiv PGame.one_mul_equiv

theorem quot_mul_assoc : ∀ x y z : PGame, ⟦x * y * z⟧ = ⟦x * (y * z)⟧
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    · fconstructor
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zL k -
                (xL i * y + x * yL j - xL i * yL j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xL i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp [quot_mul_assoc]
        abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zL k -
                (xR i * y + x * yR j - xR i * yR j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xR i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp [quot_mul_assoc]
        abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zR k -
                (xL i * y + x * yR j - xL i * yR j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xL i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp [quot_mul_assoc]
        abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zR k -
                (xR i * y + x * yL j - xR i * yL j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xR i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp [quot_mul_assoc]
        abel
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zR k -
                (xL i * y + x * yL j - xL i * yL j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xL i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp [quot_mul_assoc]
        abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zR k -
                (xR i * y + x * yR j - xR i * yR j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xR i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp [quot_mul_assoc]
        abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zL k -
                (xL i * y + x * yR j - xL i * yR j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xL i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp [quot_mul_assoc]
        abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zL k -
                (xR i * y + x * yL j - xR i * yL j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xR i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp [quot_mul_assoc]
        abel decreasing_by pgame_wf_tac
#align pgame.quot_mul_assoc PGame.quot_mul_assoc

/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem mul_assoc_equiv (x y z : PGame) : x * y * z ≈ x * (y * z) :=
  Quotient.exact <| quot_mul_assoc _ _ _
#align pgame.mul_assoc_equiv PGame.mul_assoc_equiv

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive InvTy (l r : Type u) : Bool → Type u
  | zero : inv_ty false
  | left₁ : r → inv_ty false → inv_ty false
  | left₂ : l → inv_ty true → inv_ty false
  | right₁ : l → inv_ty false → inv_ty true
  | right₂ : r → inv_ty true → inv_ty true
#align pgame.inv_ty PGame.InvTy

instance (l r : Type u) [IsEmpty l] [IsEmpty r] : IsEmpty (InvTy l r true) :=
  ⟨by rintro (_ | _ | _ | a | a) <;> exact isEmptyElim a⟩

instance (l r : Type u) : Inhabited (InvTy l r false) :=
  ⟨InvTy.zero⟩

instance uniqueInvTy (l r : Type u) [IsEmpty l] [IsEmpty r] : Unique (InvTy l r false) :=
  { InvTy.inhabited l r with
    uniq := by
      rintro (a | a | a)
      rfl
      all_goals exact isEmptyElim a }
#align pgame.unique_inv_ty PGame.uniqueInvTy

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `inv_ty`. -/
def invVal {l r} (L : l → PGame) (R : r → PGame) (IHl : l → PGame) (IHr : r → PGame) :
    ∀ {b}, InvTy l r b → PGame
  | _, inv_ty.zero => 0
  | _, inv_ty.left₁ i j => (1 + (R i - mk l r L R) * inv_val j) * IHr i
  | _, inv_ty.left₂ i j => (1 + (L i - mk l r L R) * inv_val j) * IHl i
  | _, inv_ty.right₁ i j => (1 + (L i - mk l r L R) * inv_val j) * IHl i
  | _, inv_ty.right₂ i j => (1 + (R i - mk l r L R) * inv_val j) * IHr i
#align pgame.inv_val PGame.invVal

@[simp]
theorem invVal_isEmpty {l r : Type u} {b} (L R IHl IHr) (i : InvTy l r b) [IsEmpty l] [IsEmpty r] :
    invVal L R IHl IHr i = 0 := by
  cases' i with a _ a _ a _ a
  · rfl
  all_goals exact isEmptyElim a
#align pgame.inv_val_is_empty PGame.invVal_isEmpty

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : PGame → PGame
  | ⟨l, r, L, R⟩ =>
    let l' := { i // 0 < L i }
    let L' : l' → PGame := fun i => L i.1
    let IHl' : l' → PGame := fun i => inv' (L i.1)
    let IHr i := inv' (R i)
    ⟨InvTy l' r false, InvTy l' r true, invVal L' R IHl' IHr, invVal L' R IHl' IHr⟩
#align pgame.inv' PGame.inv'

theorem zero_lf_inv' : ∀ x : PGame, 0 ⧏ inv' x
  | ⟨xl, xr, xL, xR⟩ => by
    convert lf_mk _ _ inv_ty.zero
    rfl
#align pgame.zero_lf_inv' PGame.zero_lf_inv'

/-- `inv' 0` has exactly the same moves as `1`. -/
def inv'Zero : inv' 0 ≡r 1 := by
  change mk _ _ _ _ ≡r 1
  refine' ⟨_, _, fun i => _, IsEmpty.elim _⟩
  · apply Equiv.equivPUnit (inv_ty _ _ _)
    infer_instance
  · apply Equiv.equivPEmpty (inv_ty _ _ _)
    infer_instance
  · simp
  · dsimp
    infer_instance
#align pgame.inv'_zero PGame.inv'Zero

theorem inv'_zero_equiv : inv' 0 ≈ 1 :=
  inv'Zero.Equiv
#align pgame.inv'_zero_equiv PGame.inv'_zero_equiv

/-- `inv' 1` has exactly the same moves as `1`. -/
def inv'One : inv' 1 ≡r (1 : PGame.{u}) := by
  change relabelling (mk _ _ _ _) 1
  have : IsEmpty { i : PUnit.{u + 1} // (0 : PGame.{u}) < 0 } := by
    rw [lt_self_iff_false]
    infer_instance
  refine' ⟨_, _, fun i => _, IsEmpty.elim _⟩ <;> dsimp
  · apply Equiv.equivPUnit
  · apply Equiv.equivOfIsEmpty
  · simp
  · infer_instance
#align pgame.inv'_one PGame.inv'One

theorem inv'_one_equiv : inv' 1 ≈ 1 :=
  inv'One.Equiv
#align pgame.inv'_one_equiv PGame.inv'_one_equiv

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : Inv PGame :=
  ⟨by classical exact fun x => if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x)⟩

noncomputable instance : Div PGame :=
  ⟨fun x y => x * y⁻¹⟩

theorem inv_eq_of_equiv_zero {x : PGame} (h : x ≈ 0) : x⁻¹ = 0 := by classical exact if_pos h
#align pgame.inv_eq_of_equiv_zero PGame.inv_eq_of_equiv_zero

@[simp]
theorem inv_zero : (0 : PGame)⁻¹ = 0 :=
  inv_eq_of_equiv_zero (equiv_refl _)
#align pgame.inv_zero PGame.inv_zero

theorem inv_eq_of_pos {x : PGame} (h : 0 < x) : x⁻¹ = inv' x := by
  classical exact (if_neg h.lf.not_equiv').trans (if_pos h)
#align pgame.inv_eq_of_pos PGame.inv_eq_of_pos

theorem inv_eq_of_lf_zero {x : PGame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) := by
  classical exact (if_neg h.not_equiv).trans (if_neg h.not_gt)
#align pgame.inv_eq_of_lf_zero PGame.inv_eq_of_lf_zero

/-- `1⁻¹` has exactly the same moves as `1`. -/
def invOne : 1⁻¹ ≡r 1 := by
  rw [inv_eq_of_pos PGame.zero_lt_one]
  exact inv'_one
#align pgame.inv_one PGame.invOne

theorem inv_one_equiv : 1⁻¹ ≈ 1 :=
  invOne.Equiv
#align pgame.inv_one_equiv PGame.inv_one_equiv

end PGame

