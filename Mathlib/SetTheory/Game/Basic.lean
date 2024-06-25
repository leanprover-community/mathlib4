/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade
-/
import Mathlib.Algebra.Ring.Int
import Mathlib.SetTheory.Game.PGame
import Mathlib.Tactic.Abel

#align_import set_theory.game.basic from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Combinatorial games.

In this file we construct an instance `OrderedAddCommGroup SetTheory.Game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/

-- Porting note: many definitions here are noncomputable as the compiler does not support PGame.rec
noncomputable section

namespace SetTheory

open Function PGame

open PGame

universe u

-- Porting note: moved the setoid instance to PGame.lean

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `PGame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbrev Game :=
  Quotient PGame.setoid
#align game SetTheory.Game

namespace Game

-- Porting note (#11445): added this definition
/-- Negation of games. -/
instance : Neg Game where
  neg := Quot.map Neg.neg <| fun _ _ => (neg_equiv_neg_iff).2

instance : Zero Game where zero := ⟦0⟧
instance : Add Game where
  add := Quotient.map₂ HAdd.hAdd <| fun _ _ hx _ _ hy => PGame.add_congr hx hy

instance instAddCommGroupWithOneGame : AddCommGroupWithOne Game where
  zero := ⟦0⟧
  one := ⟦1⟧
  add_zero := by
    rintro ⟨x⟩
    exact Quot.sound (add_zero_equiv x)
  zero_add := by
    rintro ⟨x⟩
    exact Quot.sound (zero_add_equiv x)
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact Quot.sound add_assoc_equiv
  add_left_neg := Quotient.ind <| fun x => Quot.sound (add_left_neg_equiv x)
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    exact Quot.sound add_comm_equiv
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Inhabited Game :=
  ⟨0⟩

instance instPartialOrderGame : PartialOrder Game where
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
def LF : Game → Game → Prop :=
  Quotient.lift₂ PGame.LF fun _ _ _ _ hx hy => propext (lf_congr hx hy)
#align game.lf SetTheory.Game.LF

local infixl:50 " ⧏ " => LF

/-- On `Game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem not_le : ∀ {x y : Game}, ¬x ≤ y ↔ y ⧏ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact PGame.not_le
#align game.not_le SetTheory.Game.not_le

/-- On `Game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem not_lf : ∀ {x y : Game}, ¬x ⧏ y ↔ y ≤ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact PGame.not_lf
#align game.not_lf SetTheory.Game.not_lf

-- Porting note: had to replace ⧏ with LF, otherwise cannot differentiate with the operator on PGame
instance : IsTrichotomous Game LF :=
  ⟨by
    rintro ⟨x⟩ ⟨y⟩
    change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _
    rw [Quotient.eq]
    apply lf_or_equiv_or_gf⟩

/-! It can be useful to use these lemmas to turn `PGame` inequalities into `Game` inequalities, as
the `AddCommGroup` structure on `Game` often simplifies many proofs. -/

-- Porting note: In a lot of places, I had to add explicitely that the quotient element was a Game.
-- In Lean4, quotients don't have the setoid as an instance argument,
-- but as an explicit argument, see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
theorem PGame.le_iff_game_le {x y : PGame} : x ≤ y ↔ (⟦x⟧ : Game) ≤ ⟦y⟧ :=
  Iff.rfl
#align game.pgame.le_iff_game_le SetTheory.Game.PGame.le_iff_game_le

theorem PGame.lf_iff_game_lf {x y : PGame} : PGame.LF x y ↔ ⟦x⟧ ⧏ ⟦y⟧ :=
  Iff.rfl
#align game.pgame.lf_iff_game_lf SetTheory.Game.PGame.lf_iff_game_lf

theorem PGame.lt_iff_game_lt {x y : PGame} : x < y ↔ (⟦x⟧ : Game) < ⟦y⟧ :=
  Iff.rfl
#align game.pgame.lt_iff_game_lt SetTheory.Game.PGame.lt_iff_game_lt

theorem PGame.equiv_iff_game_eq {x y : PGame} : x ≈ y ↔ (⟦x⟧ : Game) = ⟦y⟧ :=
  (@Quotient.eq' _ _ x y).symm
#align game.pgame.equiv_iff_game_eq SetTheory.Game.PGame.equiv_iff_game_eq

/-- The fuzzy, confused, or incomparable relation on games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy : Game → Game → Prop :=
  Quotient.lift₂ PGame.Fuzzy fun _ _ _ _ hx hy => propext (fuzzy_congr hx hy)
#align game.fuzzy SetTheory.Game.Fuzzy

local infixl:50 " ‖ " => Fuzzy

theorem PGame.fuzzy_iff_game_fuzzy {x y : PGame} : PGame.Fuzzy x y ↔ ⟦x⟧ ‖ ⟦y⟧ :=
  Iff.rfl
#align game.pgame.fuzzy_iff_game_fuzzy SetTheory.Game.PGame.fuzzy_iff_game_fuzzy

instance covariantClass_add_le : CovariantClass Game Game (· + ·) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_le SetTheory.Game.covariantClass_add_le

instance covariantClass_swap_add_le : CovariantClass Game Game (swap (· + ·)) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_le SetTheory.Game.covariantClass_swap_add_le

instance covariantClass_add_lt : CovariantClass Game Game (· + ·) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_lt SetTheory.Game.covariantClass_add_lt

instance covariantClass_swap_add_lt : CovariantClass Game Game (swap (· + ·)) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_lt SetTheory.Game.covariantClass_swap_add_lt

theorem add_lf_add_right : ∀ {b c : Game} (_ : b ⧏ c) (a), (b + a : Game) ⧏ c + a := by
  rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩
  apply PGame.add_lf_add_right h
#align game.add_lf_add_right SetTheory.Game.add_lf_add_right

theorem add_lf_add_left : ∀ {b c : Game} (_ : b ⧏ c) (a), (a + b : Game) ⧏ a + c := by
  rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩
  apply PGame.add_lf_add_left h
#align game.add_lf_add_left SetTheory.Game.add_lf_add_left

instance orderedAddCommGroup : OrderedAddCommGroup Game :=
  { Game.instAddCommGroupWithOneGame, Game.instPartialOrderGame with
    add_le_add_left := @add_le_add_left _ _ _ Game.covariantClass_add_le }
#align game.ordered_add_comm_group SetTheory.Game.orderedAddCommGroup

/-- A small family of games is bounded above. -/
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Game.{u}) :
    BddAbove (Set.range f) := by
  obtain ⟨x, hx⟩ := PGame.bddAbove_range_of_small (Quotient.out ∘ f)
  refine ⟨⟦x⟧, Set.forall_mem_range.2 fun i ↦ ?_⟩
  simpa [PGame.le_iff_game_le] using hx $ Set.mem_range_self i

/-- A small set of games is bounded above. -/
lemma bddAbove_of_small (s : Set Game.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → Game.{u})
#align game.bdd_above_of_small SetTheory.Game.bddAbove_of_small

/-- A small family of games is bounded below. -/
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Game.{u}) :
    BddBelow (Set.range f) := by
  obtain ⟨x, hx⟩ := PGame.bddBelow_range_of_small (Quotient.out ∘ f)
  refine ⟨⟦x⟧, Set.forall_mem_range.2 fun i ↦ ?_⟩
  simpa [PGame.le_iff_game_le] using hx $ Set.mem_range_self i

/-- A small set of games is bounded below. -/
lemma bddBelow_of_small (s : Set Game.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → Game.{u})
#align game.bdd_below_of_small SetTheory.Game.bddBelow_of_small

end Game

namespace PGame

@[simp]
theorem quot_neg (a : PGame) : (⟦-a⟧ : Game) = -⟦a⟧ :=
  rfl
#align pgame.quot_neg SetTheory.PGame.quot_neg

@[simp]
theorem quot_add (a b : PGame) : ⟦a + b⟧ = (⟦a⟧ : Game) + ⟦b⟧ :=
  rfl
#align pgame.quot_add SetTheory.PGame.quot_add

@[simp]
theorem quot_sub (a b : PGame) : ⟦a - b⟧ = (⟦a⟧ : Game) - ⟦b⟧ :=
  rfl
#align pgame.quot_sub SetTheory.PGame.quot_sub

theorem quot_eq_of_mk'_quot_eq {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, (⟦x.moveLeft i⟧ : Game) = ⟦y.moveLeft (L i)⟧)
    (hr : ∀ j, (⟦x.moveRight j⟧ : Game) = ⟦y.moveRight (R j)⟧) : (⟦x⟧ : Game) = ⟦y⟧ := by
  exact Quot.sound (equiv_of_mk_equiv L R (fun _ => Game.PGame.equiv_iff_game_eq.2 (hl _))
                                          (fun _ => Game.PGame.equiv_iff_game_eq.2 (hr _)))
#align pgame.quot_eq_of_mk_quot_eq SetTheory.PGame.quot_eq_of_mk'_quot_eq

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/


/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
instance : Mul PGame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr _ _ IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine ⟨Sum (xl × yl) (xr × yr), Sum (xl × yr) (xr × yl), ?_, ?_⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact IHxl i y + IHyl j - IHxl i (yL j)
    · exact IHxr i y + IHyr j - IHxr i (yR j)
    · exact IHxl i y + IHyr j - IHxl i (yR j)
    · exact IHxr i y + IHyl j - IHxr i (yL j)⟩

theorem leftMoves_mul :
    ∀ x y : PGame.{u},
      (x * y).LeftMoves = Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_mul SetTheory.PGame.leftMoves_mul

theorem rightMoves_mul :
    ∀ x y : PGame.{u},
      (x * y).RightMoves = Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_mul SetTheory.PGame.rightMoves_mul

/-- Turns two left or right moves for `x` and `y` into a left move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesMul {x y : PGame} :
    Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves) ≃ (x * y).LeftMoves :=
  Equiv.cast (leftMoves_mul x y).symm
#align pgame.to_left_moves_mul SetTheory.PGame.toLeftMovesMul

/-- Turns a left and a right move for `x` and `y` into a right move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesMul {x y : PGame} :
    Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves) ≃ (x * y).RightMoves :=
  Equiv.cast (rightMoves_mul x y).symm
#align pgame.to_right_moves_mul SetTheory.PGame.toRightMovesMul

@[simp]
theorem mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j :=
  rfl
#align pgame.mk_mul_move_left_inl SetTheory.PGame.mk_mul_moveLeft_inl

@[simp]
theorem mul_moveLeft_inl {x y : PGame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_left_inl SetTheory.PGame.mul_moveLeft_inl

@[simp]
theorem mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j :=
  rfl
#align pgame.mk_mul_move_left_inr SetTheory.PGame.mk_mul_moveLeft_inr

@[simp]
theorem mul_moveLeft_inr {x y : PGame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveRight j - x.moveRight i * y.moveRight j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_left_inr SetTheory.PGame.mul_moveLeft_inr

@[simp]
theorem mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j :=
  rfl
#align pgame.mk_mul_move_right_inl SetTheory.PGame.mk_mul_moveRight_inl

@[simp]
theorem mul_moveRight_inl {x y : PGame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveRight j - x.moveLeft i * y.moveRight j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_right_inl SetTheory.PGame.mul_moveRight_inl

@[simp]
theorem mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j :=
  rfl
#align pgame.mk_mul_move_right_inr SetTheory.PGame.mk_mul_moveRight_inr

@[simp]
theorem mul_moveRight_inr {x y : PGame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveLeft j - x.moveRight i * y.moveLeft j := by
  cases x
  cases y
  rfl
#align pgame.mul_move_right_inr SetTheory.PGame.mul_moveRight_inr

-- @[simp] -- Porting note: simpNF linter complains
theorem neg_mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inl SetTheory.PGame.neg_mk_mul_moveLeft_inl

-- @[simp] -- Porting note: simpNF linter complains
theorem neg_mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inr SetTheory.PGame.neg_mk_mul_moveLeft_inr

-- @[simp] -- Porting note: simpNF linter complains
theorem neg_mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inl SetTheory.PGame.neg_mk_mul_moveRight_inl

-- @[simp] -- Porting note: simpNF linter complains
theorem neg_mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inr SetTheory.PGame.neg_mk_mul_moveRight_inr

theorem leftMoves_mul_cases {x y : PGame} (k) {P : (x * y).LeftMoves → Prop}
    (hl : ∀ ix iy, P <| toLeftMovesMul (Sum.inl ⟨ix, iy⟩))
    (hr : ∀ jx jy, P <| toLeftMovesMul (Sum.inr ⟨jx, jy⟩)) : P k := by
  rw [← toLeftMovesMul.apply_symm_apply k]
  rcases toLeftMovesMul.symm k with (⟨ix, iy⟩ | ⟨jx, jy⟩)
  · apply hl
  · apply hr
#align pgame.left_moves_mul_cases SetTheory.PGame.leftMoves_mul_cases

theorem rightMoves_mul_cases {x y : PGame} (k) {P : (x * y).RightMoves → Prop}
    (hl : ∀ ix jy, P <| toRightMovesMul (Sum.inl ⟨ix, jy⟩))
    (hr : ∀ jx iy, P <| toRightMovesMul (Sum.inr ⟨jx, iy⟩)) : P k := by
  rw [← toRightMovesMul.apply_symm_apply k]
  rcases toRightMovesMul.symm k with (⟨ix, iy⟩ | ⟨jx, jy⟩)
  · apply hl
  · apply hr
#align pgame.right_moves_mul_cases SetTheory.PGame.rightMoves_mul_cases

/-- `x * y` and `y * x` have the same moves. -/
def mulCommRelabelling (x y : PGame.{u}) : x * y ≡r y * x :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _),
      (Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)), ?_, ?_⟩
      <;>
    rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
    { dsimp
      exact ((addCommRelabelling _ _).trans <|
        (mulCommRelabelling _ _).addCongr (mulCommRelabelling _ _)).subCongr
        (mulCommRelabelling _ _) }
  termination_by (x, y)
#align pgame.mul_comm_relabelling SetTheory.PGame.mulCommRelabelling

theorem quot_mul_comm (x y : PGame.{u}) : (⟦x * y⟧ : Game) = ⟦y * x⟧ :=
  Quot.sound (mulCommRelabelling x y).equiv
#align pgame.quot_mul_comm SetTheory.PGame.quot_mul_comm

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : PGame) : x * y ≈ y * x :=
  Quotient.exact <| quot_mul_comm _ _
#align pgame.mul_comm_equiv SetTheory.PGame.mul_comm_equiv

instance isEmpty_mul_zero_leftMoves (x : PGame.{u}) : IsEmpty (x * 0).LeftMoves := by
  cases x
  exact instIsEmptySum
#align pgame.is_empty_mul_zero_left_moves SetTheory.PGame.isEmpty_mul_zero_leftMoves

instance isEmpty_mul_zero_rightMoves (x : PGame.{u}) : IsEmpty (x * 0).RightMoves := by
  cases x
  apply instIsEmptySum
#align pgame.is_empty_mul_zero_right_moves SetTheory.PGame.isEmpty_mul_zero_rightMoves

instance isEmpty_zero_mul_leftMoves (x : PGame.{u}) : IsEmpty (0 * x).LeftMoves := by
  cases x
  apply instIsEmptySum
#align pgame.is_empty_zero_mul_left_moves SetTheory.PGame.isEmpty_zero_mul_leftMoves

instance isEmpty_zero_mul_rightMoves (x : PGame.{u}) : IsEmpty (0 * x).RightMoves := by
  cases x
  apply instIsEmptySum
#align pgame.is_empty_zero_mul_right_moves SetTheory.PGame.isEmpty_zero_mul_rightMoves

/-- `x * 0` has exactly the same moves as `0`. -/
def mulZeroRelabelling (x : PGame) : x * 0 ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.mul_zero_relabelling SetTheory.PGame.mulZeroRelabelling

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : PGame) : x * 0 ≈ 0 :=
  (mulZeroRelabelling x).equiv
#align pgame.mul_zero_equiv SetTheory.PGame.mul_zero_equiv

@[simp]
theorem quot_mul_zero (x : PGame) : (⟦x * 0⟧ : Game) = ⟦0⟧ :=
  @Quotient.sound _ _ (x * 0) _ x.mul_zero_equiv
#align pgame.quot_mul_zero SetTheory.PGame.quot_mul_zero

/-- `0 * x` has exactly the same moves as `0`. -/
def zeroMulRelabelling (x : PGame) : 0 * x ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.zero_mul_relabelling SetTheory.PGame.zeroMulRelabelling

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : PGame) : 0 * x ≈ 0 :=
  (zeroMulRelabelling x).equiv
#align pgame.zero_mul_equiv SetTheory.PGame.zero_mul_equiv

@[simp]
theorem quot_zero_mul (x : PGame) : (⟦0 * x⟧ : Game) = ⟦0⟧ :=
  @Quotient.sound _ _ (0 * x) _ x.zero_mul_equiv
#align pgame.quot_zero_mul SetTheory.PGame.quot_zero_mul

/-- `-x * y` and `-(x * y)` have the same moves. -/
def negMulRelabelling (x y : PGame.{u}) : -x * y ≡r -(x * y) :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
      refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;>
      rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
      · dsimp
        apply ((negAddRelabelling _ _).trans _).symm
        apply ((negAddRelabelling _ _).trans (Relabelling.addCongr _ _)).subCongr
        -- Porting note: we used to just do `<;> exact (negMulRelabelling _ _).symm` from here.
        · exact (negMulRelabelling _ _).symm
        · exact (negMulRelabelling _ _).symm
        -- Porting note: not sure what has gone wrong here.
        -- The goal is hideous here, and the `exact` doesn't work,
        -- but if we just `change` it to look like the mathlib3 goal then we're fine!?
        change -(mk xl xr xL xR * _) ≡r _
        exact (negMulRelabelling _ _).symm
  termination_by (x, y)
#align pgame.neg_mul_relabelling SetTheory.PGame.negMulRelabelling

@[simp]
theorem quot_neg_mul (x y : PGame) : (⟦-x * y⟧ : Game) = -⟦x * y⟧ :=
  Quot.sound (negMulRelabelling x y).equiv
#align pgame.quot_neg_mul SetTheory.PGame.quot_neg_mul

/-- `x * -y` and `-(x * y)` have the same moves. -/
def mulNegRelabelling (x y : PGame) : x * -y ≡r -(x * y) :=
  (mulCommRelabelling x _).trans <| (negMulRelabelling _ x).trans (mulCommRelabelling y x).negCongr
#align pgame.mul_neg_relabelling SetTheory.PGame.mulNegRelabelling

@[simp]
theorem quot_mul_neg (x y : PGame) : ⟦x * -y⟧ = (-⟦x * y⟧ : Game) :=
  Quot.sound (mulNegRelabelling x y).equiv
#align pgame.quot_mul_neg SetTheory.PGame.quot_mul_neg

@[simp]
theorem quot_left_distrib (x y z : PGame) : (⟦x * (y + z)⟧ : Game) = ⟦x * y⟧ + ⟦x * z⟧ :=
  match x, y, z with
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine quot_eq_of_mk'_quot_eq ?_ ?_ ?_ ?_
    · fconstructor
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          -- Porting note: we've increased `maxDepth` here from `5` to `6`.
          -- Likely this sort of off-by-one error is just a change in the implementation
          -- of `solve_by_elim`.
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    · fconstructor
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    -- Porting note: explicitly wrote out arguments to each recursive
    -- quot_left_distrib reference below, because otherwise the decreasing_by block
    -- failed. Previously, each branch ended with: `simp [quot_left_distrib]; abel`
    -- See https://github.com/leanprover/lean4/issues/2288
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧ =
            ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xL i) (yL j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧ =
            ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (zL k)]
        abel
      · change
          ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧ =
            ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xR i) (yR j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧ =
            ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (zR k)]
        abel
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧ =
            ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xL i) (yR j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧ =
            ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (zR k)]
        abel
      · change
          ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧ =
            ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xR i) (yL j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧ =
            ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (zL k)]
        abel
  termination_by (x, y, z)
#align pgame.quot_left_distrib SetTheory.PGame.quot_left_distrib

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv (x y z : PGame) : x * (y + z) ≈ x * y + x * z :=
  Quotient.exact <| quot_left_distrib _ _ _
#align pgame.left_distrib_equiv SetTheory.PGame.left_distrib_equiv

@[simp]
theorem quot_left_distrib_sub (x y z : PGame) : (⟦x * (y - z)⟧ : Game) = ⟦x * y⟧ - ⟦x * z⟧ := by
  change (⟦x * (y + -z)⟧ : Game) = ⟦x * y⟧ + -⟦x * z⟧
  rw [quot_left_distrib, quot_mul_neg]
#align pgame.quot_left_distrib_sub SetTheory.PGame.quot_left_distrib_sub

@[simp]
theorem quot_right_distrib (x y z : PGame) : (⟦(x + y) * z⟧ : Game) = ⟦x * z⟧ + ⟦y * z⟧ := by
  simp only [quot_mul_comm, quot_left_distrib]
#align pgame.quot_right_distrib SetTheory.PGame.quot_right_distrib

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : PGame) : (x + y) * z ≈ x * z + y * z :=
  Quotient.exact <| quot_right_distrib _ _ _
#align pgame.right_distrib_equiv SetTheory.PGame.right_distrib_equiv

@[simp]
theorem quot_right_distrib_sub (x y z : PGame) : (⟦(y - z) * x⟧ : Game) = ⟦y * x⟧ - ⟦z * x⟧ := by
  change (⟦(y + -z) * x⟧ : Game) = ⟦y * x⟧ + -⟦z * x⟧
  rw [quot_right_distrib, quot_neg_mul]
#align pgame.quot_right_distrib_sub SetTheory.PGame.quot_right_distrib_sub

/-- `x * 1` has the same moves as `x`. -/
def mulOneRelabelling : ∀ x : PGame.{u}, x * 1 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    -- Porting note: the next four lines were just `unfold has_one.one,`
    show _ * One.one ≡r _
    unfold One.one
    unfold instOnePGame
    change mk _ _ _ _ * mk _ _ _ _ ≡r _
    refine ⟨(Equiv.sumEmpty _ _).trans (Equiv.prodPUnit _),
      (Equiv.emptySum _ _).trans (Equiv.prodPUnit _), ?_, ?_⟩ <;>
    (try rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩)) <;>
    { dsimp
      apply (Relabelling.subCongr (Relabelling.refl _) (mulZeroRelabelling _)).trans
      rw [sub_zero]
      exact (addZeroRelabelling _).trans <|
        (((mulOneRelabelling _).addCongr (mulZeroRelabelling _)).trans <| addZeroRelabelling _) }
#align pgame.mul_one_relabelling SetTheory.PGame.mulOneRelabelling

@[simp]
theorem quot_mul_one (x : PGame) : (⟦x * 1⟧ : Game) = ⟦x⟧ :=
  Quot.sound <| PGame.Relabelling.equiv <| mulOneRelabelling x
#align pgame.quot_mul_one SetTheory.PGame.quot_mul_one

/-- `x * 1` is equivalent to `x`. -/
theorem mul_one_equiv (x : PGame) : x * 1 ≈ x :=
  Quotient.exact <| quot_mul_one x
#align pgame.mul_one_equiv SetTheory.PGame.mul_one_equiv

/-- `1 * x` has the same moves as `x`. -/
def oneMulRelabelling (x : PGame) : 1 * x ≡r x :=
  (mulCommRelabelling 1 x).trans <| mulOneRelabelling x
#align pgame.one_mul_relabelling SetTheory.PGame.oneMulRelabelling

@[simp]
theorem quot_one_mul (x : PGame) : (⟦1 * x⟧ : Game) = ⟦x⟧ :=
  Quot.sound <| PGame.Relabelling.equiv <| oneMulRelabelling x
#align pgame.quot_one_mul SetTheory.PGame.quot_one_mul

/-- `1 * x` is equivalent to `x`. -/
theorem one_mul_equiv (x : PGame) : 1 * x ≈ x :=
  Quotient.exact <| quot_one_mul x
#align pgame.one_mul_equiv SetTheory.PGame.one_mul_equiv

theorem quot_mul_assoc (x y z : PGame) : (⟦x * y * z⟧ : Game) = ⟦x * (y * z)⟧ :=
  match x, y, z with
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine quot_eq_of_mk'_quot_eq ?_ ?_ ?_ ?_
    · fconstructor
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          -- Porting note: as above, increased the `maxDepth` here by 1.
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    · fconstructor
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    -- Porting note: explicitly wrote out arguments to each recursive
    -- quot_mul_assoc reference below, because otherwise the decreasing_by block
    -- failed. Each branch previously ended with: `simp [quot_mul_assoc]; abel`
    -- See https://github.com/leanprover/lean4/issues/2288
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zL k -
                (xL i * y + x * yL j - xL i * yL j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xL i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zL k)]
        rw [quot_mul_assoc (xL i) (yL j) (zL k)]
        abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zL k -
                (xR i * y + x * yR j - xR i * yR j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xR i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zL k)]
        rw [quot_mul_assoc (xR i) (yR j) (zL k)]
        abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zR k -
                (xL i * y + x * yR j - xL i * yR j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xL i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zR k)]
        rw [quot_mul_assoc (xL i) (yR j) (zR k)]
        abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zR k -
                (xR i * y + x * yL j - xR i * yL j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xR i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zR k)]
        rw [quot_mul_assoc (xR i) (yL j) (zR k)]
        abel
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zR k -
                (xL i * y + x * yL j - xL i * yL j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xL i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zR k)]
        rw [quot_mul_assoc (xL i) (yL j) (zR k)]
        abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zR k -
                (xR i * y + x * yR j - xR i * yR j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xR i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zR k)]
        rw [quot_mul_assoc (xR i) (yR j) (zR k)]
        abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zL k -
                (xL i * y + x * yR j - xL i * yR j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xL i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zL k)]
        rw [quot_mul_assoc (xL i) (yR j) (zL k)]
        abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zL k -
                (xR i * y + x * yL j - xR i * yL j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xR i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zL k)]
        rw [quot_mul_assoc (xR i) (yL j) (zL k)]
        abel
  termination_by (x, y, z)
#align pgame.quot_mul_assoc SetTheory.PGame.quot_mul_assoc

/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem mul_assoc_equiv (x y z : PGame) : x * y * z ≈ x * (y * z) :=
  Quotient.exact <| quot_mul_assoc _ _ _
#align pgame.mul_assoc_equiv SetTheory.PGame.mul_assoc_equiv

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `invVal` is the function part. -/
inductive InvTy (l r : Type u) : Bool → Type u
  | zero : InvTy l r false
  | left₁ : r → InvTy l r false → InvTy l r false
  | left₂ : l → InvTy l r true → InvTy l r false
  | right₁ : l → InvTy l r false → InvTy l r true
  | right₂ : r → InvTy l r true → InvTy l r true
#align pgame.inv_ty SetTheory.PGame.InvTy

instance (l r : Type u) [IsEmpty l] [IsEmpty r] : IsEmpty (InvTy l r true) :=
  ⟨by rintro (_ | _ | _ | a | a) <;> exact isEmptyElim a⟩

instance InvTy.instInhabited (l r : Type u) : Inhabited (InvTy l r false) :=
  ⟨InvTy.zero⟩

instance uniqueInvTy (l r : Type u) [IsEmpty l] [IsEmpty r] : Unique (InvTy l r false) :=
  { InvTy.instInhabited l r with
    uniq := by
      rintro (a | a | a)
      · rfl
      all_goals exact isEmptyElim a }
#align pgame.unique_inv_ty SetTheory.PGame.uniqueInvTy

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `InvTy`. -/
def invVal {l r} (L : l → PGame) (R : r → PGame) (IHl : l → PGame) (IHr : r → PGame) :
    ∀ {b}, InvTy l r b → PGame
  | _, InvTy.zero => 0
  | _, InvTy.left₁ i j => (1 + (R i - mk l r L R) * invVal L R IHl IHr j) * IHr i
  | _, InvTy.left₂ i j => (1 + (L i - mk l r L R) * invVal L R IHl IHr j) * IHl i
  | _, InvTy.right₁ i j => (1 + (L i - mk l r L R) * invVal L R IHl IHr j) * IHl i
  | _, InvTy.right₂ i j => (1 + (R i - mk l r L R) * invVal L R IHl IHr j) * IHr i
#align pgame.inv_val SetTheory.PGame.invVal

@[simp]
theorem invVal_isEmpty {l r : Type u} {b} (L R IHl IHr) (i : InvTy l r b) [IsEmpty l] [IsEmpty r] :
    invVal L R IHl IHr i = 0 := by
  cases' i with a _ a _ a _ a
  · rfl
  all_goals exact isEmptyElim a
#align pgame.inv_val_is_empty SetTheory.PGame.invVal_isEmpty

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : PGame → PGame
  | ⟨_, r, L, R⟩ =>
    let l' := { i // 0 < L i }
    let L' : l' → PGame := fun i => L i.1
    let IHl' : l' → PGame := fun i => inv' (L i.1)
    let IHr i := inv' (R i)
    ⟨InvTy l' r false, InvTy l' r true, invVal L' R IHl' IHr, invVal L' R IHl' IHr⟩
#align pgame.inv' SetTheory.PGame.inv'

theorem zero_lf_inv' : ∀ x : PGame, 0 ⧏ inv' x
  | ⟨xl, xr, xL, xR⟩ => by
    convert lf_mk _ _ InvTy.zero
    rfl
#align pgame.zero_lf_inv' SetTheory.PGame.zero_lf_inv'

/-- `inv' 0` has exactly the same moves as `1`. -/
def inv'Zero : inv' 0 ≡r 1 := by
  change mk _ _ _ _ ≡r 1
  refine ⟨?_, ?_, fun i => ?_, IsEmpty.elim ?_⟩
  · apply Equiv.equivPUnit (InvTy _ _ _)
  · apply Equiv.equivPEmpty (InvTy _ _ _)
  · -- Porting note: had to add `rfl`, because `simp` only uses the built-in `rfl`.
    simp; rfl
  · dsimp
    infer_instance
#align pgame.inv'_zero SetTheory.PGame.inv'Zero

theorem inv'_zero_equiv : inv' 0 ≈ 1 :=
  inv'Zero.equiv
#align pgame.inv'_zero_equiv SetTheory.PGame.inv'_zero_equiv

/-- `inv' 1` has exactly the same moves as `1`. -/
def inv'One : inv' 1 ≡r (1 : PGame.{u}) := by
  change Relabelling (mk _ _ _ _) 1
  have : IsEmpty { _i : PUnit.{u + 1} // (0 : PGame.{u}) < 0 } := by
    rw [lt_self_iff_false]
    infer_instance
  refine ⟨?_, ?_, fun i => ?_, IsEmpty.elim ?_⟩ <;> dsimp
  · apply Equiv.equivPUnit
  · apply Equiv.equivOfIsEmpty
  · -- Porting note: had to add `rfl`, because `simp` only uses the built-in `rfl`.
    simp; rfl
  · infer_instance
#align pgame.inv'_one SetTheory.PGame.inv'One

theorem inv'_one_equiv : inv' 1 ≈ 1 :=
  inv'One.equiv
#align pgame.inv'_one_equiv SetTheory.PGame.inv'_one_equiv

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : Inv PGame :=
  ⟨by classical exact fun x => if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x)⟩

noncomputable instance : Div PGame :=
  ⟨fun x y => x * y⁻¹⟩

theorem inv_eq_of_equiv_zero {x : PGame} (h : x ≈ 0) : x⁻¹ = 0 := by classical exact if_pos h
#align pgame.inv_eq_of_equiv_zero SetTheory.PGame.inv_eq_of_equiv_zero

@[simp]
theorem inv_zero : (0 : PGame)⁻¹ = 0 :=
  inv_eq_of_equiv_zero (equiv_refl _)
#align pgame.inv_zero SetTheory.PGame.inv_zero

theorem inv_eq_of_pos {x : PGame} (h : 0 < x) : x⁻¹ = inv' x := by
  classical exact (if_neg h.lf.not_equiv').trans (if_pos h)
#align pgame.inv_eq_of_pos SetTheory.PGame.inv_eq_of_pos

theorem inv_eq_of_lf_zero {x : PGame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) := by
  classical exact (if_neg h.not_equiv).trans (if_neg h.not_gt)
#align pgame.inv_eq_of_lf_zero SetTheory.PGame.inv_eq_of_lf_zero

/-- `1⁻¹` has exactly the same moves as `1`. -/
def invOne : 1⁻¹ ≡r 1 := by
  rw [inv_eq_of_pos PGame.zero_lt_one]
  exact inv'One
#align pgame.inv_one SetTheory.PGame.invOne

theorem inv_one_equiv : (1⁻¹ : PGame) ≈ 1 :=
  invOne.equiv
#align pgame.inv_one_equiv SetTheory.PGame.inv_one_equiv

end PGame
