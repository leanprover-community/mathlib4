/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.List.InsertNth
import Mathlib.Logic.Relation
import Mathlib.Logic.Small.Defs
import Mathlib.Order.GameAdd

#align_import set_theory.game.pgame from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Combinatorial (pre-)games.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`SetTheory.PGame` below) is axiomatised via an inductive type, whose sole constructor
takes two types (thought of as indexing the possible moves for the players Left and Right), and a
pair of functions out of these types to `SetTheory.PGame` (thought of as describing the resulting
game after making a move).

Combinatorial games themselves, as a quotient of pregames, are constructed in `Game.lean`.

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `SetTheory.PGame → Prop` holds for all pregames, it suffices to prove
that for every pregame `g`, if the predicate holds for every game resulting from making a move,
then it also holds for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `SetTheory.PGame.LeftMoves`,
`SetTheory.PGame.RightMoves`, `SetTheory.PGame.moveLeft` and `SetTheory.PGame.moveRight`.
There is a relation `PGame.Subsequent p q`, saying that
`p` can be reached by playing some non-empty sequence of moves starting from `q`, an instance
`WellFounded Subsequent`, and a local tactic `pgame_wf_tac` which is helpful for discharging proof
obligations in inductive proofs relying on this relation.

## Order properties

Pregames have both a `≤` and a `<` relation, satisfying the usual properties of a `Preorder`. The
relation `0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won
by Left as the second player.

It turns out to be quite convenient to define various relations on top of these. We define the "less
or fuzzy" relation `x ⧏ y` as `¬ y ≤ x`, the equivalence relation `x ≈ y` as `x ≤ y ∧ y ≤ x`, and
the fuzzy relation `x ‖ y` as `x ⧏ y ∧ y ⧏ x`. If `0 ⧏ x`, then `x` can be won by Left as the
first player. If `x ≈ 0`, then `x` can be won by the second player. If `x ‖ 0`, then `x` can be won
by the first player.

Statements like `zero_le_lf`, `zero_lf_le`, etc. unfold these definitions. The theorems `le_def` and
`lf_def` give a recursive characterisation of each relation in terms of themselves two moves later.
The theorems `zero_le`, `zero_lf`, etc. also take into account that `0` has no moves.

Later, games will be defined as the quotient by the `≈` relation; that is to say, the
`Antisymmetrization` of `SetTheory.PGame`.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : PGame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, we introduce the notion of a `Relabelling` of a
game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## Future work

* The theory of dominated and reversible positions, and unique normal form for short games.
* Analysis of basic domineering positions.
* Hex.
* Temperature.
* The development of surreal numbers, based on this development of combinatorial games, is still
  quite incomplete.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/

set_option autoImplicit true

namespace SetTheory

open Function Relation

-- We'd like to be able to use multi-character auto-implicits in this file.
set_option relaxedAutoImplicit true

/-! ### Pre-game moves -/


/-- The type of pre-games, before we have quotiented
  by equivalence (`PGame.Setoid`). In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `PGame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → PGame) → (β → PGame) → PGame
#align pgame SetTheory.PGame
compile_inductive% PGame

namespace PGame

/-- The indexing type for allowable moves by Left. -/
def LeftMoves : PGame → Type u
  | mk l _ _ _ => l
#align pgame.left_moves SetTheory.PGame.LeftMoves

/-- The indexing type for allowable moves by Right. -/
def RightMoves : PGame → Type u
  | mk _ r _ _ => r
#align pgame.right_moves SetTheory.PGame.RightMoves

/-- The new game after Left makes an allowed move. -/
def moveLeft : ∀ g : PGame, LeftMoves g → PGame
  | mk _l _ L _ => L
#align pgame.move_left SetTheory.PGame.moveLeft

/-- The new game after Right makes an allowed move. -/
def moveRight : ∀ g : PGame, RightMoves g → PGame
  | mk _ _r _ R => R
#align pgame.move_right SetTheory.PGame.moveRight

@[simp]
theorem leftMoves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).LeftMoves = xl :=
  rfl
#align pgame.left_moves_mk SetTheory.PGame.leftMoves_mk

@[simp]
theorem moveLeft_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).moveLeft = xL :=
  rfl
#align pgame.move_left_mk SetTheory.PGame.moveLeft_mk

@[simp]
theorem rightMoves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).RightMoves = xr :=
  rfl
#align pgame.right_moves_mk SetTheory.PGame.rightMoves_mk

@[simp]
theorem moveRight_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).moveRight = xR :=
  rfl
#align pgame.move_right_mk SetTheory.PGame.moveRight_mk

-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
def ofLists (L R : List PGame.{u}) : PGame.{u} :=
  mk (ULift (Fin L.length)) (ULift (Fin R.length)) (fun i => L.get i.down) fun j ↦ R.get j.down
#align pgame.of_lists SetTheory.PGame.ofLists

theorem leftMoves_ofLists (L R : List PGame) : (ofLists L R).LeftMoves = ULift (Fin L.length) :=
  rfl
#align pgame.left_moves_of_lists SetTheory.PGame.leftMoves_ofLists

theorem rightMoves_ofLists (L R : List PGame) : (ofLists L R).RightMoves = ULift (Fin R.length) :=
  rfl
#align pgame.right_moves_of_lists SetTheory.PGame.rightMoves_ofLists

/-- Converts a number into a left move for `ofLists`. -/
def toOfListsLeftMoves {L R : List PGame} : Fin L.length ≃ (ofLists L R).LeftMoves :=
  ((Equiv.cast (leftMoves_ofLists L R).symm).trans Equiv.ulift).symm
#align pgame.to_of_lists_left_moves SetTheory.PGame.toOfListsLeftMoves

/-- Converts a number into a right move for `ofLists`. -/
def toOfListsRightMoves {L R : List PGame} : Fin R.length ≃ (ofLists L R).RightMoves :=
  ((Equiv.cast (rightMoves_ofLists L R).symm).trans Equiv.ulift).symm
#align pgame.to_of_lists_right_moves SetTheory.PGame.toOfListsRightMoves

theorem ofLists_moveLeft {L R : List PGame} (i : Fin L.length) :
    (ofLists L R).moveLeft (toOfListsLeftMoves i) = L.get i :=
  rfl
#align pgame.of_lists_move_left SetTheory.PGame.ofLists_moveLeft

@[simp]
theorem ofLists_moveLeft' {L R : List PGame} (i : (ofLists L R).LeftMoves) :
    (ofLists L R).moveLeft i = L.get (toOfListsLeftMoves.symm i) :=
  rfl
#align pgame.of_lists_move_left' SetTheory.PGame.ofLists_moveLeft'

theorem ofLists_moveRight {L R : List PGame} (i : Fin R.length) :
    (ofLists L R).moveRight (toOfListsRightMoves i) = R.get i :=
  rfl
#align pgame.of_lists_move_right SetTheory.PGame.ofLists_moveRight

@[simp]
theorem ofLists_moveRight' {L R : List PGame} (i : (ofLists L R).RightMoves) :
    (ofLists L R).moveRight i = R.get (toOfListsRightMoves.symm i) :=
  rfl
#align pgame.of_lists_move_right' SetTheory.PGame.ofLists_moveRight'

/-- A variant of `PGame.recOn` expressed in terms of `PGame.moveLeft` and `PGame.moveRight`.

Both this and `PGame.recOn` describe Conway induction on games. -/
@[elab_as_elim]
def moveRecOn {C : PGame → Sort*} (x : PGame)
    (IH : ∀ y : PGame, (∀ i, C (y.moveLeft i)) → (∀ j, C (y.moveRight j)) → C y) : C x :=
  x.recOn fun yl yr yL yR => IH (mk yl yr yL yR)
#align pgame.move_rec_on SetTheory.PGame.moveRecOn

/-- `IsOption x y` means that `x` is either a left or right option for `y`. -/
@[mk_iff]
inductive IsOption : PGame → PGame → Prop
  | moveLeft {x : PGame} (i : x.LeftMoves) : IsOption (x.moveLeft i) x
  | moveRight {x : PGame} (i : x.RightMoves) : IsOption (x.moveRight i) x
#align pgame.is_option SetTheory.PGame.IsOption

theorem IsOption.mk_left {xl xr : Type u} (xL : xl → PGame) (xR : xr → PGame) (i : xl) :
    (xL i).IsOption (mk xl xr xL xR) :=
  @IsOption.moveLeft (mk _ _ _ _) i
#align pgame.is_option.mk_left SetTheory.PGame.IsOption.mk_left

theorem IsOption.mk_right {xl xr : Type u} (xL : xl → PGame) (xR : xr → PGame) (i : xr) :
    (xR i).IsOption (mk xl xr xL xR) :=
  @IsOption.moveRight (mk _ _ _ _) i
#align pgame.is_option.mk_right SetTheory.PGame.IsOption.mk_right

theorem wf_isOption : WellFounded IsOption :=
  ⟨fun x =>
    moveRecOn x fun x IHl IHr =>
      Acc.intro x fun y h => by
        induction' h with _ i _ j
        · exact IHl i
        · exact IHr j⟩
#align pgame.wf_is_option SetTheory.PGame.wf_isOption

/-- `Subsequent x y` says that `x` can be obtained by playing some nonempty sequence of moves from
`y`. It is the transitive closure of `IsOption`. -/
def Subsequent : PGame → PGame → Prop :=
  TransGen IsOption
#align pgame.subsequent SetTheory.PGame.Subsequent

instance : IsTrans _ Subsequent :=
  inferInstanceAs <| IsTrans _ (TransGen _)

@[trans]
theorem Subsequent.trans {x y z} : Subsequent x y → Subsequent y z → Subsequent x z :=
  TransGen.trans
#align pgame.subsequent.trans SetTheory.PGame.Subsequent.trans

theorem wf_subsequent : WellFounded Subsequent :=
  wf_isOption.transGen
#align pgame.wf_subsequent SetTheory.PGame.wf_subsequent

instance : WellFoundedRelation PGame :=
  ⟨_, wf_subsequent⟩

@[simp]
theorem Subsequent.moveLeft {x : PGame} (i : x.LeftMoves) : Subsequent (x.moveLeft i) x :=
  TransGen.single (IsOption.moveLeft i)
#align pgame.subsequent.move_left SetTheory.PGame.Subsequent.moveLeft

@[simp]
theorem Subsequent.moveRight {x : PGame} (j : x.RightMoves) : Subsequent (x.moveRight j) x :=
  TransGen.single (IsOption.moveRight j)
#align pgame.subsequent.move_right SetTheory.PGame.Subsequent.moveRight

@[simp]
theorem Subsequent.mk_left {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i : xl) :
    Subsequent (xL i) (mk xl xr xL xR) :=
  @Subsequent.moveLeft (mk _ _ _ _) i
#align pgame.subsequent.mk_left SetTheory.PGame.Subsequent.mk_left

@[simp]
theorem Subsequent.mk_right {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j : xr) :
    Subsequent (xR j) (mk xl xr xL xR) :=
  @Subsequent.moveRight (mk _ _ _ _) j
#align pgame.subsequent.mk_right SetTheory.PGame.Subsequent.mk_right

/--
Discharges proof obligations of the form `⊢ Subsequent ..` arising in termination proofs
of definitions using well-founded recursion on `PGame`.
-/
macro "pgame_wf_tac" : tactic =>
  `(tactic| solve_by_elim (config := { maxDepth := 8 })
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subsequent.moveLeft, Subsequent.moveRight, Subsequent.mk_left, Subsequent.mk_right,
    Subsequent.trans] )

-- Register some consequences of pgame_wf_tac as simp-lemmas for convenience
-- (which are applied by default for WF goals)

-- This is different from mk_right from the POV of the simplifier,
-- because the unifier can't solve `xr =?= RightMoves (mk xl xr xL xR)` at reducible transparency.
@[simp]
theorem Subsequent.mk_right' (xL : xl → PGame) (xR : xr → PGame) (j : RightMoves (mk xl xr xL xR)) :
    Subsequent (xR j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveRight_mk_left (xL : xl → PGame) (j) :
    Subsequent ((xL i).moveRight j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveRight_mk_right (xR : xr → PGame) (j) :
    Subsequent ((xR i).moveRight j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveLeft_mk_left (xL : xl → PGame) (j) :
    Subsequent ((xL i).moveLeft j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveLeft_mk_right (xR : xr → PGame) (j) :
    Subsequent ((xR i).moveLeft j) (mk xl xr xL xR) := by
  pgame_wf_tac

-- Porting note: linter claims these lemmas don't simplify?
open Subsequent in attribute [nolint simpNF] mk_left mk_right mk_right'
  moveRight_mk_left moveRight_mk_right moveLeft_mk_left moveLeft_mk_right

/-! ### Basic pre-games -/


/-- The pre-game `Zero` is defined by `0 = { | }`. -/
instance : Zero PGame :=
  ⟨⟨PEmpty, PEmpty, PEmpty.elim, PEmpty.elim⟩⟩

@[simp]
theorem zero_leftMoves : LeftMoves 0 = PEmpty :=
  rfl
#align pgame.zero_left_moves SetTheory.PGame.zero_leftMoves

@[simp]
theorem zero_rightMoves : RightMoves 0 = PEmpty :=
  rfl
#align pgame.zero_right_moves SetTheory.PGame.zero_rightMoves

instance isEmpty_zero_leftMoves : IsEmpty (LeftMoves 0) :=
  instIsEmptyPEmpty
#align pgame.is_empty_zero_left_moves SetTheory.PGame.isEmpty_zero_leftMoves

instance isEmpty_zero_rightMoves : IsEmpty (RightMoves 0) :=
  instIsEmptyPEmpty
#align pgame.is_empty_zero_right_moves SetTheory.PGame.isEmpty_zero_rightMoves

instance : Inhabited PGame :=
  ⟨0⟩

/-- The pre-game `One` is defined by `1 = { 0 | }`. -/
instance instOnePGame : One PGame :=
  ⟨⟨PUnit, PEmpty, fun _ => 0, PEmpty.elim⟩⟩

@[simp]
theorem one_leftMoves : LeftMoves 1 = PUnit :=
  rfl
#align pgame.one_left_moves SetTheory.PGame.one_leftMoves

@[simp]
theorem one_moveLeft (x) : moveLeft 1 x = 0 :=
  rfl
#align pgame.one_move_left SetTheory.PGame.one_moveLeft

@[simp]
theorem one_rightMoves : RightMoves 1 = PEmpty :=
  rfl
#align pgame.one_right_moves SetTheory.PGame.one_rightMoves

instance uniqueOneLeftMoves : Unique (LeftMoves 1) :=
  PUnit.unique
#align pgame.unique_one_left_moves SetTheory.PGame.uniqueOneLeftMoves

instance isEmpty_one_rightMoves : IsEmpty (RightMoves 1) :=
  instIsEmptyPEmpty
#align pgame.is_empty_one_right_moves SetTheory.PGame.isEmpty_one_rightMoves

/-! ### Pre-game order relations -/


/-- The less or equal relation on pre-games.

If `0 ≤ x`, then Left can win `x` as the second player. -/
instance le : LE PGame :=
  ⟨Sym2.GameAdd.fix wf_isOption fun x y le =>
      (∀ i, ¬le y (x.moveLeft i) (Sym2.GameAdd.snd_fst <| IsOption.moveLeft i)) ∧
        ∀ j, ¬le (y.moveRight j) x (Sym2.GameAdd.fst_snd <| IsOption.moveRight j)⟩

/-- The less or fuzzy relation on pre-games.

If `0 ⧏ x`, then Left can win `x` as the first player. -/
def LF (x y : PGame) : Prop :=
  ¬y ≤ x
#align pgame.lf SetTheory.PGame.LF

@[inherit_doc]
scoped infixl:50 " ⧏ " => PGame.LF

@[simp]
protected theorem not_le {x y : PGame} : ¬x ≤ y ↔ y ⧏ x :=
  Iff.rfl
#align pgame.not_le SetTheory.PGame.not_le

@[simp]
theorem not_lf {x y : PGame} : ¬x ⧏ y ↔ y ≤ x :=
  Classical.not_not
#align pgame.not_lf SetTheory.PGame.not_lf

theorem _root_.LE.le.not_gf {x y : PGame} : x ≤ y → ¬y ⧏ x :=
  not_lf.2
#align has_le.le.not_gf LE.le.not_gf

theorem LF.not_ge {x y : PGame} : x ⧏ y → ¬y ≤ x :=
  id
#align pgame.lf.not_ge SetTheory.PGame.LF.not_ge

/-- Definition of `x ≤ y` on pre-games, in terms of `⧏`.

The ordering here is chosen so that `And.left` refer to moves by Left, and `And.right` refer to
moves by Right. -/
theorem le_iff_forall_lf {x y : PGame} :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by
  unfold LE.le le
  simp only
  rw [Sym2.GameAdd.fix_eq]
  rfl
#align pgame.le_iff_forall_lf SetTheory.PGame.le_iff_forall_lf

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ≤ mk yl yr yL yR ↔ (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
  le_iff_forall_lf
#align pgame.mk_le_mk SetTheory.PGame.mk_le_mk

theorem le_of_forall_lf {x y : PGame} (h₁ : ∀ i, x.moveLeft i ⧏ y) (h₂ : ∀ j, x ⧏ y.moveRight j) :
    x ≤ y :=
  le_iff_forall_lf.2 ⟨h₁, h₂⟩
#align pgame.le_of_forall_lf SetTheory.PGame.le_of_forall_lf

/-- Definition of `x ⧏ y` on pre-games, in terms of `≤`.

The ordering here is chosen so that `or.inl` refer to moves by Left, and `or.inr` refer to
moves by Right. -/
theorem lf_iff_exists_le {x y : PGame} :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [LF, le_iff_forall_lf, not_and_or]
  simp
#align pgame.lf_iff_exists_le SetTheory.PGame.lf_iff_exists_le

/-- Definition of `x ⧏ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ⧏ mk yl yr yL yR ↔ (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
  lf_iff_exists_le
#align pgame.mk_lf_mk SetTheory.PGame.mk_lf_mk

theorem le_or_gf (x y : PGame) : x ≤ y ∨ y ⧏ x := by
  rw [← PGame.not_le]
  apply em
#align pgame.le_or_gf SetTheory.PGame.le_or_gf

theorem moveLeft_lf_of_le {x y : PGame} (h : x ≤ y) (i) : x.moveLeft i ⧏ y :=
  (le_iff_forall_lf.1 h).1 i
#align pgame.move_left_lf_of_le SetTheory.PGame.moveLeft_lf_of_le

alias _root_.LE.le.moveLeft_lf := moveLeft_lf_of_le
#align has_le.le.move_left_lf LE.le.moveLeft_lf

theorem lf_moveRight_of_le {x y : PGame} (h : x ≤ y) (j) : x ⧏ y.moveRight j :=
  (le_iff_forall_lf.1 h).2 j
#align pgame.lf_move_right_of_le SetTheory.PGame.lf_moveRight_of_le

alias _root_.LE.le.lf_moveRight := lf_moveRight_of_le
#align has_le.le.lf_move_right LE.le.lf_moveRight

theorem lf_of_moveRight_le {x y : PGame} {j} (h : x.moveRight j ≤ y) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨j, h⟩
#align pgame.lf_of_move_right_le SetTheory.PGame.lf_of_moveRight_le

theorem lf_of_le_moveLeft {x y : PGame} {i} (h : x ≤ y.moveLeft i) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨i, h⟩
#align pgame.lf_of_le_move_left SetTheory.PGame.lf_of_le_moveLeft

theorem lf_of_le_mk {xl xr xL xR y} : mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
  moveLeft_lf_of_le
#align pgame.lf_of_le_mk SetTheory.PGame.lf_of_le_mk

theorem lf_of_mk_le {x yl yr yL yR} : x ≤ mk yl yr yL yR → ∀ j, x ⧏ yR j :=
  lf_moveRight_of_le
#align pgame.lf_of_mk_le SetTheory.PGame.lf_of_mk_le

theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → PGame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
  @lf_of_moveRight_le (mk _ _ _ _) y j
#align pgame.mk_lf_of_le SetTheory.PGame.mk_lf_of_le

theorem lf_mk_of_le {x yl yr} {yL : yl → PGame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
  @lf_of_le_moveLeft x (mk _ _ _ _) i
#align pgame.lf_mk_of_le SetTheory.PGame.lf_mk_of_le

/- We prove that `x ≤ y → y ≤ z → x ≤ z` inductively, by also simultaneously proving its cyclic
reorderings. This auxiliary lemma is used during said induction. -/
private theorem le_trans_aux {x y z : PGame}
    (h₁ : ∀ {i}, y ≤ z → z ≤ x.moveLeft i → y ≤ x.moveLeft i)
    (h₂ : ∀ {j}, z.moveRight j ≤ x → x ≤ y → z.moveRight j ≤ y) (hxy : x ≤ y) (hyz : y ≤ z) :
    x ≤ z :=
  le_of_forall_lf (fun i => PGame.not_le.1 fun h => (h₁ hyz h).not_gf <| hxy.moveLeft_lf i)
    fun j => PGame.not_le.1 fun h => (h₂ h hxy).not_gf <| hyz.lf_moveRight j

instance : Preorder PGame :=
  { PGame.le with
    le_refl := fun x => by
      induction' x with _ _ _ _ IHl IHr
      exact
        le_of_forall_lf (fun i => lf_of_le_moveLeft (IHl i)) fun i => lf_of_moveRight_le (IHr i)
    le_trans := by
      suffices
        ∀ {x y z : PGame},
          (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y) from
        fun x y z => this.1
      intro x y z
      induction' x with xl xr xL xR IHxl IHxr generalizing y z
      induction' y with yl yr yL yR IHyl IHyr generalizing z
      induction' z with zl zr zL zR IHzl IHzr
      exact
        ⟨le_trans_aux (fun {i} => (IHxl i).2.1) fun {j} => (IHzr j).2.2,
          le_trans_aux (fun {i} => (IHyl i).2.2) fun {j} => (IHxr j).1,
          le_trans_aux (fun {i} => (IHzl i).1) fun {j} => (IHyr j).2.1⟩
    lt := fun x y => x ≤ y ∧ x ⧏ y }

theorem lt_iff_le_and_lf {x y : PGame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
  Iff.rfl
#align pgame.lt_iff_le_and_lf SetTheory.PGame.lt_iff_le_and_lf

theorem lt_of_le_of_lf {x y : PGame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
  ⟨h₁, h₂⟩
#align pgame.lt_of_le_of_lf SetTheory.PGame.lt_of_le_of_lf

theorem lf_of_lt {x y : PGame} (h : x < y) : x ⧏ y :=
  h.2
#align pgame.lf_of_lt SetTheory.PGame.lf_of_lt

alias _root_.LT.lt.lf := lf_of_lt
#align has_lt.lt.lf LT.lt.lf

theorem lf_irrefl (x : PGame) : ¬x ⧏ x :=
  le_rfl.not_gf
#align pgame.lf_irrefl SetTheory.PGame.lf_irrefl

instance : IsIrrefl _ (· ⧏ ·) :=
  ⟨lf_irrefl⟩

@[trans]
theorem lf_of_le_of_lf {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₂ ⊢
  exact fun h₃ => h₂ (h₃.trans h₁)
#align pgame.lf_of_le_of_lf SetTheory.PGame.lf_of_le_of_lf

-- Porting note (#10754): added instance
instance : Trans (· ≤ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_le_of_lf⟩

@[trans]
theorem lf_of_lf_of_le {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₁ ⊢
  exact fun h₃ => h₁ (h₂.trans h₃)
#align pgame.lf_of_lf_of_le SetTheory.PGame.lf_of_lf_of_le

-- Porting note (#10754): added instance
instance : Trans (· ⧏ ·) (· ≤ ·) (· ⧏ ·) := ⟨lf_of_lf_of_le⟩

alias _root_.LE.le.trans_lf := lf_of_le_of_lf
#align has_le.le.trans_lf LE.le.trans_lf

alias LF.trans_le := lf_of_lf_of_le
#align pgame.lf.trans_le SetTheory.PGame.LF.trans_le

@[trans]
theorem lf_of_lt_of_lf {x y z : PGame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
  h₁.le.trans_lf h₂
#align pgame.lf_of_lt_of_lf SetTheory.PGame.lf_of_lt_of_lf

@[trans]
theorem lf_of_lf_of_lt {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
  h₁.trans_le h₂.le
#align pgame.lf_of_lf_of_lt SetTheory.PGame.lf_of_lf_of_lt

alias _root_.LT.lt.trans_lf := lf_of_lt_of_lf
#align has_lt.lt.trans_lf LT.lt.trans_lf

alias LF.trans_lt := lf_of_lf_of_lt
#align pgame.lf.trans_lt SetTheory.PGame.LF.trans_lt

theorem moveLeft_lf {x : PGame} : ∀ i, x.moveLeft i ⧏ x :=
  le_rfl.moveLeft_lf
#align pgame.move_left_lf SetTheory.PGame.moveLeft_lf

theorem lf_moveRight {x : PGame} : ∀ j, x ⧏ x.moveRight j :=
  le_rfl.lf_moveRight
#align pgame.lf_move_right SetTheory.PGame.lf_moveRight

theorem lf_mk {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i) : xL i ⧏ mk xl xr xL xR :=
  @moveLeft_lf (mk _ _ _ _) i
#align pgame.lf_mk SetTheory.PGame.lf_mk

theorem mk_lf {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j) : mk xl xr xL xR ⧏ xR j :=
  @lf_moveRight (mk _ _ _ _) j
#align pgame.mk_lf SetTheory.PGame.mk_lf

/-- This special case of `PGame.le_of_forall_lf` is useful when dealing with surreals, where `<` is
preferred over `⧏`. -/
theorem le_of_forall_lt {x y : PGame} (h₁ : ∀ i, x.moveLeft i < y) (h₂ : ∀ j, x < y.moveRight j) :
    x ≤ y :=
  le_of_forall_lf (fun i => (h₁ i).lf) fun i => (h₂ i).lf
#align pgame.le_of_forall_lt SetTheory.PGame.le_of_forall_lt

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : PGame} :
    x ≤ y ↔
      (∀ i, (∃ i', x.moveLeft i ≤ y.moveLeft i') ∨ ∃ j, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j, (∃ i, x ≤ (y.moveRight j).moveLeft i) ∨ ∃ j', x.moveRight j' ≤ y.moveRight j := by
  rw [le_iff_forall_lf]
  conv =>
    lhs
    simp only [lf_iff_exists_le]
#align pgame.le_def SetTheory.PGame.le_def

/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later. -/
theorem lf_def {x y : PGame} :
    x ⧏ y ↔
      (∃ i, (∀ i', x.moveLeft i' ⧏ y.moveLeft i) ∧ ∀ j, x ⧏ (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i ⧏ y) ∧ ∀ j', x.moveRight j ⧏ y.moveRight j' := by
  rw [lf_iff_exists_le]
  conv =>
    lhs
    simp only [le_iff_forall_lf]
#align pgame.lf_def SetTheory.PGame.lf_def

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem zero_le_lf {x : PGame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.moveRight j := by
  rw [le_iff_forall_lf]
  simp
#align pgame.zero_le_lf SetTheory.PGame.zero_le_lf

/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem le_zero_lf {x : PGame} : x ≤ 0 ↔ ∀ i, x.moveLeft i ⧏ 0 := by
  rw [le_iff_forall_lf]
  simp
#align pgame.le_zero_lf SetTheory.PGame.le_zero_lf

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem zero_lf_le {x : PGame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.moveLeft i := by
  rw [lf_iff_exists_le]
  simp
#align pgame.zero_lf_le SetTheory.PGame.zero_lf_le

/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem lf_zero_le {x : PGame} : x ⧏ 0 ↔ ∃ j, x.moveRight j ≤ 0 := by
  rw [lf_iff_exists_le]
  simp
#align pgame.lf_zero_le SetTheory.PGame.lf_zero_le

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : PGame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_def]
  simp
#align pgame.zero_le SetTheory.PGame.zero_le

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : PGame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_def]
  simp
#align pgame.le_zero SetTheory.PGame.le_zero

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ⧏` two moves later. -/
theorem zero_lf {x : PGame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.moveLeft i).moveRight j := by
  rw [lf_def]
  simp
#align pgame.zero_lf SetTheory.PGame.zero_lf

/-- The definition of `x ⧏ 0` on pre-games, in terms of `⧏ 0` two moves later. -/
theorem lf_zero {x : PGame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.moveRight j).moveLeft i ⧏ 0 := by
  rw [lf_def]
  simp
#align pgame.lf_zero SetTheory.PGame.lf_zero

@[simp]
theorem zero_le_of_isEmpty_rightMoves (x : PGame) [IsEmpty x.RightMoves] : 0 ≤ x :=
  zero_le.2 isEmptyElim
#align pgame.zero_le_of_is_empty_right_moves SetTheory.PGame.zero_le_of_isEmpty_rightMoves

@[simp]
theorem le_zero_of_isEmpty_leftMoves (x : PGame) [IsEmpty x.LeftMoves] : x ≤ 0 :=
  le_zero.2 isEmptyElim
#align pgame.le_zero_of_is_empty_left_moves SetTheory.PGame.le_zero_of_isEmpty_leftMoves

/-- Given a game won by the right player when they play second, provide a response to any move by
left. -/
noncomputable def rightResponse {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).RightMoves :=
  Classical.choose <| (le_zero.1 h) i
#align pgame.right_response SetTheory.PGame.rightResponse

/-- Show that the response for right provided by `rightResponse` preserves the right-player-wins
condition. -/
theorem rightResponse_spec {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (rightResponse h i) ≤ 0 :=
  Classical.choose_spec <| (le_zero.1 h) i
#align pgame.right_response_spec SetTheory.PGame.rightResponse_spec

/-- Given a game won by the left player when they play second, provide a response to any move by
right. -/
noncomputable def leftResponse {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    (x.moveRight j).LeftMoves :=
  Classical.choose <| (zero_le.1 h) j
#align pgame.left_response SetTheory.PGame.leftResponse

/-- Show that the response for left provided by `leftResponse` preserves the left-player-wins
condition. -/
theorem leftResponse_spec {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (leftResponse h j) :=
  Classical.choose_spec <| (zero_le.1 h) j
#align pgame.left_response_spec SetTheory.PGame.leftResponse_spec

#noalign pgame.upper_bound
#noalign pgame.upper_bound_right_moves_empty
#noalign pgame.le_upper_bound
#noalign pgame.upper_bound_mem_upper_bounds

/-- A small family of pre-games is bounded above. -/
lemma bddAbove_range_of_small [Small.{u} ι] (f : ι → PGame.{u}) : BddAbove (Set.range f) := by
  let x : PGame.{u} := ⟨Σ i, (f $ (equivShrink.{u} ι).symm i).LeftMoves, PEmpty,
    fun x ↦ moveLeft _ x.2, PEmpty.elim⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @moveLeft_lf x ⟨equivShrink ι i, j⟩

/-- A small set of pre-games is bounded above. -/
lemma bddAbove_of_small (s : Set PGame.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → PGame.{u})
#align pgame.bdd_above_of_small SetTheory.PGame.bddAbove_of_small

#noalign pgame.lower_bound
#noalign pgame.lower_bound_left_moves_empty
#noalign pgame.lower_bound_le
#noalign pgame.lower_bound_mem_lower_bounds

/-- A small family of pre-games is bounded below. -/
lemma bddBelow_range_of_small [Small.{u} ι] (f : ι → PGame.{u}) : BddBelow (Set.range f) := by
  let x : PGame.{u} := ⟨PEmpty, Σ i, (f $ (equivShrink.{u} ι).symm i).RightMoves, PEmpty.elim,
    fun x ↦ moveRight _ x.2⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @lf_moveRight x ⟨equivShrink ι i, j⟩

/-- A small set of pre-games is bounded below. -/
lemma bddBelow_of_small (s : Set PGame.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → PGame.{u})
#align pgame.bdd_below_of_small SetTheory.PGame.bddBelow_of_small

/-- The equivalence relation on pre-games. Two pre-games `x`, `y` are equivalent if `x ≤ y` and
`y ≤ x`.

If `x ≈ 0`, then the second player can always win `x`. -/
def Equiv (x y : PGame) : Prop :=
  x ≤ y ∧ y ≤ x
#align pgame.equiv SetTheory.PGame.Equiv

-- Porting note: deleted the scoped notation due to notation overloading with the setoid
-- instance and this causes the PGame.equiv docstring to not show up on hover.

instance : IsEquiv _ PGame.Equiv where
  refl _ := ⟨le_rfl, le_rfl⟩
  trans := fun _ _ _ ⟨xy, yx⟩ ⟨yz, zy⟩ => ⟨xy.trans yz, zy.trans yx⟩
  symm _ _ := And.symm

-- Porting note: moved the setoid instance from Basic.lean to here

instance setoid : Setoid PGame :=
  ⟨Equiv, refl, symm, Trans.trans⟩
#align pgame.setoid SetTheory.PGame.setoid

theorem Equiv.le {x y : PGame} (h : x ≈ y) : x ≤ y :=
  h.1
#align pgame.equiv.le SetTheory.PGame.Equiv.le

theorem Equiv.ge {x y : PGame} (h : x ≈ y) : y ≤ x :=
  h.2
#align pgame.equiv.ge SetTheory.PGame.Equiv.ge

@[refl, simp]
theorem equiv_rfl {x : PGame} : x ≈ x :=
  refl x
#align pgame.equiv_rfl SetTheory.PGame.equiv_rfl

theorem equiv_refl (x : PGame) : x ≈ x :=
  refl x
#align pgame.equiv_refl SetTheory.PGame.equiv_refl

@[symm]
protected theorem Equiv.symm {x y : PGame} : (x ≈ y) → (y ≈ x) :=
  symm
#align pgame.equiv.symm SetTheory.PGame.Equiv.symm

@[trans]
protected theorem Equiv.trans {x y z : PGame} : (x ≈ y) → (y ≈ z) → (x ≈ z) :=
  _root_.trans
#align pgame.equiv.trans SetTheory.PGame.Equiv.trans

protected theorem equiv_comm {x y : PGame} : (x ≈ y) ↔ (y ≈ x) :=
  comm
#align pgame.equiv_comm SetTheory.PGame.equiv_comm

theorem equiv_of_eq {x y : PGame} (h : x = y) : x ≈ y := by subst h; rfl
#align pgame.equiv_of_eq SetTheory.PGame.equiv_of_eq

@[trans]
theorem le_of_le_of_equiv {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  h₁.trans h₂.1
#align pgame.le_of_le_of_equiv SetTheory.PGame.le_of_le_of_equiv

instance : Trans
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_le_of_equiv

@[trans]
theorem le_of_equiv_of_le {x y z : PGame} (h₁ : x ≈ y) : y ≤ z → x ≤ z :=
  h₁.1.trans
#align pgame.le_of_equiv_of_le SetTheory.PGame.le_of_equiv_of_le

instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_equiv_of_le

theorem LF.not_equiv {x y : PGame} (h : x ⧏ y) : ¬(x ≈ y) := fun h' => h.not_ge h'.2
#align pgame.lf.not_equiv SetTheory.PGame.LF.not_equiv

theorem LF.not_equiv' {x y : PGame} (h : x ⧏ y) : ¬(y ≈ x) := fun h' => h.not_ge h'.1
#align pgame.lf.not_equiv' SetTheory.PGame.LF.not_equiv'

theorem LF.not_gt {x y : PGame} (h : x ⧏ y) : ¬y < x := fun h' => h.not_ge h'.le
#align pgame.lf.not_gt SetTheory.PGame.LF.not_gt

theorem le_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
  hx.2.trans (h.trans hy.1)
#align pgame.le_congr_imp SetTheory.PGame.le_congr_imp

theorem le_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
  ⟨le_congr_imp hx hy, le_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩
#align pgame.le_congr SetTheory.PGame.le_congr

theorem le_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
  le_congr hx equiv_rfl
#align pgame.le_congr_left SetTheory.PGame.le_congr_left

theorem le_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
  le_congr equiv_rfl hy
#align pgame.le_congr_right SetTheory.PGame.le_congr_right

theorem lf_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
  PGame.not_le.symm.trans <| (not_congr (le_congr hy hx)).trans PGame.not_le
#align pgame.lf_congr SetTheory.PGame.lf_congr

theorem lf_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
  (lf_congr hx hy).1
#align pgame.lf_congr_imp SetTheory.PGame.lf_congr_imp

theorem lf_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
  lf_congr hx equiv_rfl
#align pgame.lf_congr_left SetTheory.PGame.lf_congr_left

theorem lf_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
  lf_congr equiv_rfl hy
#align pgame.lf_congr_right SetTheory.PGame.lf_congr_right

@[trans]
theorem lf_of_lf_of_equiv {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
  lf_congr_imp equiv_rfl h₂ h₁
#align pgame.lf_of_lf_of_equiv SetTheory.PGame.lf_of_lf_of_equiv

@[trans]
theorem lf_of_equiv_of_lf {x y z : PGame} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  lf_congr_imp (Equiv.symm h₁) equiv_rfl
#align pgame.lf_of_equiv_of_lf SetTheory.PGame.lf_of_equiv_of_lf

@[trans]
theorem lt_of_lt_of_equiv {x y z : PGame} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1
#align pgame.lt_of_lt_of_equiv SetTheory.PGame.lt_of_lt_of_equiv

@[trans]
theorem lt_of_equiv_of_lt {x y z : PGame} (h₁ : x ≈ y) : y < z → x < z :=
  h₁.1.trans_lt
#align pgame.lt_of_equiv_of_lt SetTheory.PGame.lt_of_equiv_of_lt

instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_equiv_of_lt

theorem lt_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
  hx.2.trans_lt (h.trans_le hy.1)
#align pgame.lt_congr_imp SetTheory.PGame.lt_congr_imp

theorem lt_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  ⟨lt_congr_imp hx hy, lt_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩
#align pgame.lt_congr SetTheory.PGame.lt_congr

theorem lt_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
  lt_congr hx equiv_rfl
#align pgame.lt_congr_left SetTheory.PGame.lt_congr_left

theorem lt_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
  lt_congr equiv_rfl hy
#align pgame.lt_congr_right SetTheory.PGame.lt_congr_right

theorem lt_or_equiv_of_le {x y : PGame} (h : x ≤ y) : x < y ∨ (x ≈ y) :=
  and_or_left.mp ⟨h, (em <| y ≤ x).symm.imp_left PGame.not_le.1⟩
#align pgame.lt_or_equiv_of_le SetTheory.PGame.lt_or_equiv_of_le

theorem lf_or_equiv_or_gf (x y : PGame) : x ⧏ y ∨ (x ≈ y) ∨ y ⧏ x := by
  by_cases h : x ⧏ y
  · exact Or.inl h
  · right
    cases' lt_or_equiv_of_le (PGame.not_lf.1 h) with h' h'
    · exact Or.inr h'.lf
    · exact Or.inl (Equiv.symm h')
#align pgame.lf_or_equiv_or_gf SetTheory.PGame.lf_or_equiv_or_gf

theorem equiv_congr_left {y₁ y₂ : PGame} : (y₁ ≈ y₂) ↔ ∀ x₁, (x₁ ≈ y₁) ↔ (x₁ ≈ y₂) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans h' h, fun h' => Equiv.trans h' (Equiv.symm h)⟩,
   fun h => (h y₁).1 <| equiv_rfl⟩
#align pgame.equiv_congr_left SetTheory.PGame.equiv_congr_left

theorem equiv_congr_right {x₁ x₂ : PGame} : (x₁ ≈ x₂) ↔ ∀ y₁, (x₁ ≈ y₁) ↔ (x₂ ≈ y₁) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans (Equiv.symm h) h', fun h' => Equiv.trans h h'⟩,
   fun h => (h x₂).2 <| equiv_rfl⟩
#align pgame.equiv_congr_right SetTheory.PGame.equiv_congr_right

theorem equiv_of_mk_equiv {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j, x.moveRight j ≈ y.moveRight (R j)) : x ≈ y := by
  constructor <;> rw [le_def]
  · exact ⟨fun i => Or.inl ⟨_, (hl i).1⟩, fun j => Or.inr ⟨_, by simpa using (hr (R.symm j)).1⟩⟩
  · exact ⟨fun i => Or.inl ⟨_, by simpa using (hl (L.symm i)).2⟩, fun j => Or.inr ⟨_, (hr j).2⟩⟩
#align pgame.equiv_of_mk_equiv SetTheory.PGame.equiv_of_mk_equiv

/-- The fuzzy, confused, or incomparable relation on pre-games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy (x y : PGame) : Prop :=
  x ⧏ y ∧ y ⧏ x
#align pgame.fuzzy SetTheory.PGame.Fuzzy

@[inherit_doc]
scoped infixl:50 " ‖ " => PGame.Fuzzy

@[symm]
theorem Fuzzy.swap {x y : PGame} : x ‖ y → y ‖ x :=
  And.symm
#align pgame.fuzzy.swap SetTheory.PGame.Fuzzy.swap

instance : IsSymm _ (· ‖ ·) :=
  ⟨fun _ _ => Fuzzy.swap⟩

theorem Fuzzy.swap_iff {x y : PGame} : x ‖ y ↔ y ‖ x :=
  ⟨Fuzzy.swap, Fuzzy.swap⟩
#align pgame.fuzzy.swap_iff SetTheory.PGame.Fuzzy.swap_iff

theorem fuzzy_irrefl (x : PGame) : ¬x ‖ x := fun h => lf_irrefl x h.1
#align pgame.fuzzy_irrefl SetTheory.PGame.fuzzy_irrefl

instance : IsIrrefl _ (· ‖ ·) :=
  ⟨fuzzy_irrefl⟩

theorem lf_iff_lt_or_fuzzy {x y : PGame} : x ⧏ y ↔ x < y ∨ x ‖ y := by
  simp only [lt_iff_le_and_lf, Fuzzy, ← PGame.not_le]
  tauto
#align pgame.lf_iff_lt_or_fuzzy SetTheory.PGame.lf_iff_lt_or_fuzzy

theorem lf_of_fuzzy {x y : PGame} (h : x ‖ y) : x ⧏ y :=
  lf_iff_lt_or_fuzzy.2 (Or.inr h)
#align pgame.lf_of_fuzzy SetTheory.PGame.lf_of_fuzzy

alias Fuzzy.lf := lf_of_fuzzy
#align pgame.fuzzy.lf SetTheory.PGame.Fuzzy.lf

theorem lt_or_fuzzy_of_lf {x y : PGame} : x ⧏ y → x < y ∨ x ‖ y :=
  lf_iff_lt_or_fuzzy.1
#align pgame.lt_or_fuzzy_of_lf SetTheory.PGame.lt_or_fuzzy_of_lf

theorem Fuzzy.not_equiv {x y : PGame} (h : x ‖ y) : ¬(x ≈ y) := fun h' => h'.1.not_gf h.2
#align pgame.fuzzy.not_equiv SetTheory.PGame.Fuzzy.not_equiv

theorem Fuzzy.not_equiv' {x y : PGame} (h : x ‖ y) : ¬(y ≈ x) := fun h' => h'.2.not_gf h.2
#align pgame.fuzzy.not_equiv' SetTheory.PGame.Fuzzy.not_equiv'

theorem not_fuzzy_of_le {x y : PGame} (h : x ≤ y) : ¬x ‖ y := fun h' => h'.2.not_ge h
#align pgame.not_fuzzy_of_le SetTheory.PGame.not_fuzzy_of_le

theorem not_fuzzy_of_ge {x y : PGame} (h : y ≤ x) : ¬x ‖ y := fun h' => h'.1.not_ge h
#align pgame.not_fuzzy_of_ge SetTheory.PGame.not_fuzzy_of_ge

theorem Equiv.not_fuzzy {x y : PGame} (h : x ≈ y) : ¬x ‖ y :=
  not_fuzzy_of_le h.1
#align pgame.equiv.not_fuzzy SetTheory.PGame.Equiv.not_fuzzy

theorem Equiv.not_fuzzy' {x y : PGame} (h : x ≈ y) : ¬y ‖ x :=
  not_fuzzy_of_le h.2
#align pgame.equiv.not_fuzzy' SetTheory.PGame.Equiv.not_fuzzy'

theorem fuzzy_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ ↔ x₂ ‖ y₂ :=
  show _ ∧ _ ↔ _ ∧ _ by rw [lf_congr hx hy, lf_congr hy hx]
#align pgame.fuzzy_congr SetTheory.PGame.fuzzy_congr

theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ → x₂ ‖ y₂ :=
  (fuzzy_congr hx hy).1
#align pgame.fuzzy_congr_imp SetTheory.PGame.fuzzy_congr_imp

theorem fuzzy_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ‖ y ↔ x₂ ‖ y :=
  fuzzy_congr hx equiv_rfl
#align pgame.fuzzy_congr_left SetTheory.PGame.fuzzy_congr_left

theorem fuzzy_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ‖ y₁ ↔ x ‖ y₂ :=
  fuzzy_congr equiv_rfl hy
#align pgame.fuzzy_congr_right SetTheory.PGame.fuzzy_congr_right

@[trans]
theorem fuzzy_of_fuzzy_of_equiv {x y z : PGame} (h₁ : x ‖ y) (h₂ : y ≈ z) : x ‖ z :=
  (fuzzy_congr_right h₂).1 h₁
#align pgame.fuzzy_of_fuzzy_of_equiv SetTheory.PGame.fuzzy_of_fuzzy_of_equiv

@[trans]
theorem fuzzy_of_equiv_of_fuzzy {x y z : PGame} (h₁ : x ≈ y) (h₂ : y ‖ z) : x ‖ z :=
  (fuzzy_congr_left h₁).2 h₂
#align pgame.fuzzy_of_equiv_of_fuzzy SetTheory.PGame.fuzzy_of_equiv_of_fuzzy

/-- Exactly one of the following is true (although we don't prove this here). -/
theorem lt_or_equiv_or_gt_or_fuzzy (x y : PGame) : x < y ∨ (x ≈ y) ∨ y < x ∨ x ‖ y := by
  cases' le_or_gf x y with h₁ h₁ <;> cases' le_or_gf y x with h₂ h₂
  · right
    left
    exact ⟨h₁, h₂⟩
  · left
    exact ⟨h₁, h₂⟩
  · right
    right
    left
    exact ⟨h₂, h₁⟩
  · right
    right
    right
    exact ⟨h₂, h₁⟩
#align pgame.lt_or_equiv_or_gt_or_fuzzy SetTheory.PGame.lt_or_equiv_or_gt_or_fuzzy

theorem lt_or_equiv_or_gf (x y : PGame) : x < y ∨ (x ≈ y) ∨ y ⧏ x := by
  rw [lf_iff_lt_or_fuzzy, Fuzzy.swap_iff]
  exact lt_or_equiv_or_gt_or_fuzzy x y
#align pgame.lt_or_equiv_or_gf SetTheory.PGame.lt_or_equiv_or_gf

/-! ### Relabellings -/


/-- `Relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `Relabelling`s for the consequent games.
-/
inductive Relabelling : PGame.{u} → PGame.{u} → Type (u + 1)
  |
  mk :
    ∀ {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves),
      (∀ i, Relabelling (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j, Relabelling (x.moveRight j) (y.moveRight (R j))) → Relabelling x y
#align pgame.relabelling SetTheory.PGame.Relabelling

@[inherit_doc]
scoped infixl:50 " ≡r " => PGame.Relabelling

namespace Relabelling

variable {x y : PGame.{u}}

/-- A constructor for relabellings swapping the equivalences. -/
def mk' (L : y.LeftMoves ≃ x.LeftMoves) (R : y.RightMoves ≃ x.RightMoves)
    (hL : ∀ i, x.moveLeft (L i) ≡r y.moveLeft i) (hR : ∀ j, x.moveRight (R j) ≡r y.moveRight j) :
    x ≡r y :=
  ⟨L.symm, R.symm, fun i => by simpa using hL (L.symm i), fun j => by simpa using hR (R.symm j)⟩
#align pgame.relabelling.mk' SetTheory.PGame.Relabelling.mk'

/-- The equivalence between left moves of `x` and `y` given by the relabelling. -/
def leftMovesEquiv : x ≡r y → x.LeftMoves ≃ y.LeftMoves
  | ⟨L,_, _,_⟩ => L
#align pgame.relabelling.left_moves_equiv SetTheory.PGame.Relabelling.leftMovesEquiv

@[simp]
theorem mk_leftMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).leftMovesEquiv = L :=
  rfl
#align pgame.relabelling.mk_left_moves_equiv SetTheory.PGame.Relabelling.mk_leftMovesEquiv

@[simp]
theorem mk'_leftMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).leftMovesEquiv = L.symm :=
  rfl
#align pgame.relabelling.mk'_left_moves_equiv SetTheory.PGame.Relabelling.mk'_leftMovesEquiv

/-- The equivalence between right moves of `x` and `y` given by the relabelling. -/
def rightMovesEquiv : x ≡r y → x.RightMoves ≃ y.RightMoves
  | ⟨_, R, _, _⟩ => R
#align pgame.relabelling.right_moves_equiv SetTheory.PGame.Relabelling.rightMovesEquiv

@[simp]
theorem mk_rightMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).rightMovesEquiv = R :=
  rfl
#align pgame.relabelling.mk_right_moves_equiv SetTheory.PGame.Relabelling.mk_rightMovesEquiv

@[simp]
theorem mk'_rightMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).rightMovesEquiv = R.symm :=
  rfl
#align pgame.relabelling.mk'_right_moves_equiv SetTheory.PGame.Relabelling.mk'_rightMovesEquiv

/-- A left move of `x` is a relabelling of a left move of `y`. -/
def moveLeft : ∀ (r : x ≡r y) (i : x.LeftMoves), x.moveLeft i ≡r y.moveLeft (r.leftMovesEquiv i)
  | ⟨_, _, hL, _⟩ => hL
#align pgame.relabelling.move_left SetTheory.PGame.Relabelling.moveLeft

/-- A left move of `y` is a relabelling of a left move of `x`. -/
def moveLeftSymm :
    ∀ (r : x ≡r y) (i : y.LeftMoves), x.moveLeft (r.leftMovesEquiv.symm i) ≡r y.moveLeft i
  | ⟨L, R, hL, hR⟩, i => by simpa using hL (L.symm i)
#align pgame.relabelling.move_left_symm SetTheory.PGame.Relabelling.moveLeftSymm

/-- A right move of `x` is a relabelling of a right move of `y`. -/
def moveRight :
    ∀ (r : x ≡r y) (i : x.RightMoves), x.moveRight i ≡r y.moveRight (r.rightMovesEquiv i)
  | ⟨_, _, _, hR⟩ => hR
#align pgame.relabelling.move_right SetTheory.PGame.Relabelling.moveRight

/-- A right move of `y` is a relabelling of a right move of `x`. -/
def moveRightSymm :
    ∀ (r : x ≡r y) (i : y.RightMoves), x.moveRight (r.rightMovesEquiv.symm i) ≡r y.moveRight i
  | ⟨L, R, hL, hR⟩, i => by simpa using hR (R.symm i)
#align pgame.relabelling.move_right_symm SetTheory.PGame.Relabelling.moveRightSymm

/-- The identity relabelling. -/
@[refl]
def refl (x : PGame) : x ≡r x :=
  ⟨Equiv.refl _, Equiv.refl _, fun i => refl _, fun j => refl _⟩
termination_by x
#align pgame.relabelling.refl SetTheory.PGame.Relabelling.refl

instance (x : PGame) : Inhabited (x ≡r x) :=
  ⟨refl _⟩

/-- Flip a relabelling. -/
@[symm]
def symm : ∀ {x y : PGame}, x ≡r y → y ≡r x
  | _, _, ⟨L, R, hL, hR⟩ => mk' L R (fun i => (hL i).symm) fun j => (hR j).symm
#align pgame.relabelling.symm SetTheory.PGame.Relabelling.symm

theorem le {x y : PGame} (r : x ≡r y) : x ≤ y :=
  le_def.2
    ⟨fun i => Or.inl ⟨_, (r.moveLeft i).le⟩, fun j =>
      Or.inr ⟨_, (r.moveRightSymm j).le⟩⟩
termination_by x
#align pgame.relabelling.le SetTheory.PGame.Relabelling.le

theorem ge {x y : PGame} (r : x ≡r y) : y ≤ x :=
  r.symm.le
#align pgame.relabelling.ge SetTheory.PGame.Relabelling.ge

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.ge⟩
#align pgame.relabelling.equiv SetTheory.PGame.Relabelling.equiv

/-- Transitivity of relabelling. -/
@[trans]
def trans : ∀ {x y z : PGame}, x ≡r y → y ≡r z → x ≡r z
  | _, _, _, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ j).trans (hR₂ _)⟩
#align pgame.relabelling.trans SetTheory.PGame.Relabelling.trans

/-- Any game without left or right moves is a relabelling of 0. -/
def isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equiv.equivPEmpty _, Equiv.equivOfIsEmpty _ _, isEmptyElim, isEmptyElim⟩
#align pgame.relabelling.is_empty SetTheory.PGame.Relabelling.isEmpty

end Relabelling

theorem Equiv.isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≈ 0 :=
  (Relabelling.isEmpty x).equiv
#align pgame.equiv.is_empty SetTheory.PGame.Equiv.isEmpty

instance {x y : PGame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) : PGame :=
  ⟨xl', xr', x.moveLeft ∘ el, x.moveRight ∘ er⟩
#align pgame.relabel SetTheory.PGame.relabel

@[simp]
theorem relabel_moveLeft' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : xl') : moveLeft (relabel el er) i = x.moveLeft (el i) :=
  rfl
#align pgame.relabel_move_left' SetTheory.PGame.relabel_moveLeft'

theorem relabel_moveLeft {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : x.LeftMoves) : moveLeft (relabel el er) (el.symm i) = x.moveLeft i := by simp
#align pgame.relabel_move_left SetTheory.PGame.relabel_moveLeft

@[simp]
theorem relabel_moveRight' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : xr') : moveRight (relabel el er) j = x.moveRight (er j) :=
  rfl
#align pgame.relabel_move_right' SetTheory.PGame.relabel_moveRight'

theorem relabel_moveRight {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : x.RightMoves) : moveRight (relabel el er) (er.symm j) = x.moveRight j := by simp
#align pgame.relabel_move_right SetTheory.PGame.relabel_moveRight

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabelRelabelling {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) :
    x ≡r relabel el er :=
  -- Porting note: needed to add `rfl`
  Relabelling.mk' el er (fun i => by simp; rfl) (fun j => by simp; rfl)
#align pgame.relabel_relabelling SetTheory.PGame.relabelRelabelling

/-! ### Negation -/


/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : PGame → PGame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩
#align pgame.neg SetTheory.PGame.neg

instance : Neg PGame :=
  ⟨neg⟩

@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (fun j => -xR j) fun i => -xL i :=
  rfl
#align pgame.neg_def SetTheory.PGame.neg_def

instance : InvolutiveNeg PGame :=
  { inferInstanceAs (Neg PGame) with
    neg_neg := fun x => by
      induction' x with xl xr xL xR ihL ihR
      simp_rw [neg_def, ihL, ihR] }

instance : NegZeroClass PGame :=
  { inferInstanceAs (Zero PGame), inferInstanceAs (Neg PGame) with
    neg_zero := by
      dsimp [Zero.zero, Neg.neg, neg]
      congr <;> funext i <;> cases i }

@[simp]
theorem neg_ofLists (L R : List PGame) :
    -ofLists L R = ofLists (R.map fun x => -x) (L.map fun x => -x) := by
  simp only [ofLists, neg_def, List.get_map, mk.injEq, List.length_map, true_and]
  constructor
  all_goals
    apply hfunext
    · simp
    · rintro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩ h
      have :
        ∀ {m n} (_ : m = n) {b : ULift (Fin m)} {c : ULift (Fin n)} (_ : HEq b c),
          (b.down : ℕ) = ↑c.down := by
        rintro m n rfl b c
        simp only [heq_eq_eq]
        rintro rfl
        rfl
      congr 5
      exact this (List.length_map _ _).symm h
#align pgame.neg_of_lists SetTheory.PGame.neg_ofLists

theorem isOption_neg {x y : PGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  rw [isOption_iff, isOption_iff, or_comm]
  cases y;
  apply or_congr <;>
    · apply exists_congr
      intro
      rw [neg_eq_iff_eq_neg]
      rfl
#align pgame.is_option_neg SetTheory.PGame.isOption_neg

@[simp]
theorem isOption_neg_neg {x y : PGame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]
#align pgame.is_option_neg_neg SetTheory.PGame.isOption_neg_neg

theorem leftMoves_neg : ∀ x : PGame, (-x).LeftMoves = x.RightMoves
  | ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_neg SetTheory.PGame.leftMoves_neg

theorem rightMoves_neg : ∀ x : PGame, (-x).RightMoves = x.LeftMoves
  | ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_neg SetTheory.PGame.rightMoves_neg

/-- Turns a right move for `x` into a left move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesNeg {x : PGame} : x.RightMoves ≃ (-x).LeftMoves :=
  Equiv.cast (leftMoves_neg x).symm
#align pgame.to_left_moves_neg SetTheory.PGame.toLeftMovesNeg

/-- Turns a left move for `x` into a right move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesNeg {x : PGame} : x.LeftMoves ≃ (-x).RightMoves :=
  Equiv.cast (rightMoves_neg x).symm
#align pgame.to_right_moves_neg SetTheory.PGame.toRightMovesNeg

theorem moveLeft_neg {x : PGame} (i) : (-x).moveLeft (toLeftMovesNeg i) = -x.moveRight i := by
  cases x
  rfl
#align pgame.move_left_neg SetTheory.PGame.moveLeft_neg

@[simp]
theorem moveLeft_neg' {x : PGame} (i) : (-x).moveLeft i = -x.moveRight (toLeftMovesNeg.symm i) := by
  cases x
  rfl
#align pgame.move_left_neg' SetTheory.PGame.moveLeft_neg'

theorem moveRight_neg {x : PGame} (i) : (-x).moveRight (toRightMovesNeg i) = -x.moveLeft i := by
  cases x
  rfl
#align pgame.move_right_neg SetTheory.PGame.moveRight_neg

@[simp]
theorem moveRight_neg' {x : PGame} (i) :
    (-x).moveRight i = -x.moveLeft (toRightMovesNeg.symm i) := by
  cases x
  rfl
#align pgame.move_right_neg' SetTheory.PGame.moveRight_neg'

theorem moveLeft_neg_symm {x : PGame} (i) :
    x.moveLeft (toRightMovesNeg.symm i) = -(-x).moveRight i := by simp
#align pgame.move_left_neg_symm SetTheory.PGame.moveLeft_neg_symm

theorem moveLeft_neg_symm' {x : PGame} (i) :
    x.moveLeft i = -(-x).moveRight (toRightMovesNeg i) := by simp
#align pgame.move_left_neg_symm' SetTheory.PGame.moveLeft_neg_symm'

theorem moveRight_neg_symm {x : PGame} (i) :
    x.moveRight (toLeftMovesNeg.symm i) = -(-x).moveLeft i := by simp
#align pgame.move_right_neg_symm SetTheory.PGame.moveRight_neg_symm

theorem moveRight_neg_symm' {x : PGame} (i) :
    x.moveRight i = -(-x).moveLeft (toLeftMovesNeg i) := by simp
#align pgame.move_right_neg_symm' SetTheory.PGame.moveRight_neg_symm'

/-- If `x` has the same moves as `y`, then `-x` has the same moves as `-y`. -/
def Relabelling.negCongr : ∀ {x y : PGame}, x ≡r y → -x ≡r -y
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun j => (hR j).negCongr, fun i => (hL i).negCongr⟩
#align pgame.relabelling.neg_congr SetTheory.PGame.Relabelling.negCongr

private theorem neg_le_lf_neg_iff : ∀ {x y : PGame.{u}}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def]
    constructor
    · rw [and_comm]
      apply and_congr <;> exact forall_congr' fun _ => neg_le_lf_neg_iff.2
    · rw [or_comm]
      apply or_congr <;> exact exists_congr fun _ => neg_le_lf_neg_iff.1
termination_by x y => (x, y)

@[simp]
theorem neg_le_neg_iff {x y : PGame} : -y ≤ -x ↔ x ≤ y :=
  neg_le_lf_neg_iff.1
#align pgame.neg_le_neg_iff SetTheory.PGame.neg_le_neg_iff

@[simp]
theorem neg_lf_neg_iff {x y : PGame} : -y ⧏ -x ↔ x ⧏ y :=
  neg_le_lf_neg_iff.2
#align pgame.neg_lf_neg_iff SetTheory.PGame.neg_lf_neg_iff

@[simp]
theorem neg_lt_neg_iff {x y : PGame} : -y < -x ↔ x < y := by
  rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]
#align pgame.neg_lt_neg_iff SetTheory.PGame.neg_lt_neg_iff

@[simp]
theorem neg_equiv_neg_iff {x y : PGame} : (-x ≈ -y) ↔ (x ≈ y) := by
  show Equiv (-x) (-y) ↔ Equiv x y
  rw [Equiv, Equiv, neg_le_neg_iff, neg_le_neg_iff, and_comm]
#align pgame.neg_equiv_neg_iff SetTheory.PGame.neg_equiv_neg_iff

@[simp]
theorem neg_fuzzy_neg_iff {x y : PGame} : -x ‖ -y ↔ x ‖ y := by
  rw [Fuzzy, Fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and_comm]
#align pgame.neg_fuzzy_neg_iff SetTheory.PGame.neg_fuzzy_neg_iff

theorem neg_le_iff {x y : PGame} : -y ≤ x ↔ -x ≤ y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]
#align pgame.neg_le_iff SetTheory.PGame.neg_le_iff

theorem neg_lf_iff {x y : PGame} : -y ⧏ x ↔ -x ⧏ y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]
#align pgame.neg_lf_iff SetTheory.PGame.neg_lf_iff

theorem neg_lt_iff {x y : PGame} : -y < x ↔ -x < y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]
#align pgame.neg_lt_iff SetTheory.PGame.neg_lt_iff

theorem neg_equiv_iff {x y : PGame} : (-x ≈ y) ↔ (x ≈ -y) := by
  rw [← neg_neg y, neg_equiv_neg_iff, neg_neg]
#align pgame.neg_equiv_iff SetTheory.PGame.neg_equiv_iff

theorem neg_fuzzy_iff {x y : PGame} : -x ‖ y ↔ x ‖ -y := by
  rw [← neg_neg y, neg_fuzzy_neg_iff, neg_neg]
#align pgame.neg_fuzzy_iff SetTheory.PGame.neg_fuzzy_iff

theorem le_neg_iff {x y : PGame} : y ≤ -x ↔ x ≤ -y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]
#align pgame.le_neg_iff SetTheory.PGame.le_neg_iff

theorem lf_neg_iff {x y : PGame} : y ⧏ -x ↔ x ⧏ -y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]
#align pgame.lf_neg_iff SetTheory.PGame.lf_neg_iff

theorem lt_neg_iff {x y : PGame} : y < -x ↔ x < -y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]
#align pgame.lt_neg_iff SetTheory.PGame.lt_neg_iff

@[simp]
theorem neg_le_zero_iff {x : PGame} : -x ≤ 0 ↔ 0 ≤ x := by rw [neg_le_iff, neg_zero]
#align pgame.neg_le_zero_iff SetTheory.PGame.neg_le_zero_iff

@[simp]
theorem zero_le_neg_iff {x : PGame} : 0 ≤ -x ↔ x ≤ 0 := by rw [le_neg_iff, neg_zero]
#align pgame.zero_le_neg_iff SetTheory.PGame.zero_le_neg_iff

@[simp]
theorem neg_lf_zero_iff {x : PGame} : -x ⧏ 0 ↔ 0 ⧏ x := by rw [neg_lf_iff, neg_zero]
#align pgame.neg_lf_zero_iff SetTheory.PGame.neg_lf_zero_iff

@[simp]
theorem zero_lf_neg_iff {x : PGame} : 0 ⧏ -x ↔ x ⧏ 0 := by rw [lf_neg_iff, neg_zero]
#align pgame.zero_lf_neg_iff SetTheory.PGame.zero_lf_neg_iff

@[simp]
theorem neg_lt_zero_iff {x : PGame} : -x < 0 ↔ 0 < x := by rw [neg_lt_iff, neg_zero]
#align pgame.neg_lt_zero_iff SetTheory.PGame.neg_lt_zero_iff

@[simp]
theorem zero_lt_neg_iff {x : PGame} : 0 < -x ↔ x < 0 := by rw [lt_neg_iff, neg_zero]
#align pgame.zero_lt_neg_iff SetTheory.PGame.zero_lt_neg_iff

@[simp]
theorem neg_equiv_zero_iff {x : PGame} : (-x ≈ 0) ↔ (x ≈ 0) := by rw [neg_equiv_iff, neg_zero]
#align pgame.neg_equiv_zero_iff SetTheory.PGame.neg_equiv_zero_iff

@[simp]
theorem neg_fuzzy_zero_iff {x : PGame} : -x ‖ 0 ↔ x ‖ 0 := by rw [neg_fuzzy_iff, neg_zero]
#align pgame.neg_fuzzy_zero_iff SetTheory.PGame.neg_fuzzy_zero_iff

@[simp]
theorem zero_equiv_neg_iff {x : PGame} : (0 ≈ -x) ↔ (0 ≈ x) := by rw [← neg_equiv_iff, neg_zero]
#align pgame.zero_equiv_neg_iff SetTheory.PGame.zero_equiv_neg_iff

@[simp]
theorem zero_fuzzy_neg_iff {x : PGame} : 0 ‖ -x ↔ 0 ‖ x := by rw [← neg_fuzzy_iff, neg_zero]
#align pgame.zero_fuzzy_neg_iff SetTheory.PGame.zero_fuzzy_neg_iff

/-! ### Addition and subtraction -/

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add PGame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr _ _ IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine ⟨Sum xl yl, Sum xr yr, Sum.rec ?_ ?_, Sum.rec ?_ ?_⟩
    · exact fun i => IHxl i y
    · exact IHyl
    · exact fun i => IHxr i y
    · exact IHyr⟩

/-- The pre-game `((0+1)+⋯)+1`. -/
instance : NatCast PGame :=
  ⟨Nat.unaryCast⟩

@[simp]
protected theorem nat_succ (n : ℕ) : ((n + 1 : ℕ) : PGame) = n + 1 :=
  rfl
#align pgame.nat_succ SetTheory.PGame.nat_succ

instance isEmpty_leftMoves_add (x y : PGame.{u}) [IsEmpty x.LeftMoves] [IsEmpty y.LeftMoves] :
    IsEmpty (x + y).LeftMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'
#align pgame.is_empty_left_moves_add SetTheory.PGame.isEmpty_leftMoves_add

instance isEmpty_rightMoves_add (x y : PGame.{u}) [IsEmpty x.RightMoves] [IsEmpty y.RightMoves] :
    IsEmpty (x + y).RightMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'
#align pgame.is_empty_right_moves_add SetTheory.PGame.isEmpty_rightMoves_add

/-- `x + 0` has exactly the same moves as `x`. -/
def addZeroRelabelling : ∀ x : PGame.{u}, x + 0 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.sumEmpty xl PEmpty, Equiv.sumEmpty xr PEmpty, ?_, ?_⟩ <;> rintro (⟨i⟩ | ⟨⟨⟩⟩) <;>
      apply addZeroRelabelling
termination_by x => x
#align pgame.add_zero_relabelling SetTheory.PGame.addZeroRelabelling

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : PGame.{u}) : x + 0 ≈ x :=
  (addZeroRelabelling x).equiv
#align pgame.add_zero_equiv SetTheory.PGame.add_zero_equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zeroAddRelabelling : ∀ x : PGame.{u}, 0 + x ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.emptySum PEmpty xl, Equiv.emptySum PEmpty xr, ?_, ?_⟩ <;> rintro (⟨⟨⟩⟩ | ⟨i⟩) <;>
      apply zeroAddRelabelling
#align pgame.zero_add_relabelling SetTheory.PGame.zeroAddRelabelling

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : PGame.{u}) : 0 + x ≈ x :=
  (zeroAddRelabelling x).equiv
#align pgame.zero_add_equiv SetTheory.PGame.zero_add_equiv

theorem leftMoves_add : ∀ x y : PGame.{u}, (x + y).LeftMoves = Sum x.LeftMoves y.LeftMoves
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_add SetTheory.PGame.leftMoves_add

theorem rightMoves_add : ∀ x y : PGame.{u}, (x + y).RightMoves = Sum x.RightMoves y.RightMoves
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_add SetTheory.PGame.rightMoves_add

/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesAdd {x y : PGame} : Sum x.LeftMoves y.LeftMoves ≃ (x + y).LeftMoves :=
  Equiv.cast (leftMoves_add x y).symm
#align pgame.to_left_moves_add SetTheory.PGame.toLeftMovesAdd

/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesAdd {x y : PGame} : Sum x.RightMoves y.RightMoves ≃ (x + y).RightMoves :=
  Equiv.cast (rightMoves_add x y).symm
#align pgame.to_right_moves_add SetTheory.PGame.toRightMovesAdd

@[simp]
theorem mk_add_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inl i) =
      (mk xl xr xL xR).moveLeft i + mk yl yr yL yR :=
  rfl
#align pgame.mk_add_move_left_inl SetTheory.PGame.mk_add_moveLeft_inl

@[simp]
theorem add_moveLeft_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inl i)) = x.moveLeft i + y := by
  cases x
  cases y
  rfl
#align pgame.add_move_left_inl SetTheory.PGame.add_moveLeft_inl

@[simp]
theorem mk_add_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inl i) =
      (mk xl xr xL xR).moveRight i + mk yl yr yL yR :=
  rfl
#align pgame.mk_add_move_right_inl SetTheory.PGame.mk_add_moveRight_inl

@[simp]
theorem add_moveRight_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inl i)) = x.moveRight i + y := by
  cases x
  cases y
  rfl
#align pgame.add_move_right_inl SetTheory.PGame.add_moveRight_inl

@[simp]
theorem mk_add_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveLeft i :=
  rfl
#align pgame.mk_add_move_left_inr SetTheory.PGame.mk_add_moveLeft_inr

@[simp]
theorem add_moveLeft_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inr i)) = x + y.moveLeft i := by
  cases x
  cases y
  rfl
#align pgame.add_move_left_inr SetTheory.PGame.add_moveLeft_inr

@[simp]
theorem mk_add_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveRight i :=
  rfl
#align pgame.mk_add_move_right_inr SetTheory.PGame.mk_add_moveRight_inr

@[simp]
theorem add_moveRight_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inr i)) = x + y.moveRight i := by
  cases x
  cases y
  rfl
#align pgame.add_move_right_inr SetTheory.PGame.add_moveRight_inr

theorem leftMoves_add_cases {x y : PGame} (k) {P : (x + y).LeftMoves → Prop}
    (hl : ∀ i, P <| toLeftMovesAdd (Sum.inl i)) (hr : ∀ i, P <| toLeftMovesAdd (Sum.inr i)) :
    P k := by
  rw [← toLeftMovesAdd.apply_symm_apply k]
  cases' toLeftMovesAdd.symm k with i i
  · exact hl i
  · exact hr i
#align pgame.left_moves_add_cases SetTheory.PGame.leftMoves_add_cases

theorem rightMoves_add_cases {x y : PGame} (k) {P : (x + y).RightMoves → Prop}
    (hl : ∀ j, P <| toRightMovesAdd (Sum.inl j)) (hr : ∀ j, P <| toRightMovesAdd (Sum.inr j)) :
    P k := by
  rw [← toRightMovesAdd.apply_symm_apply k]
  cases' toRightMovesAdd.symm k with i i
  · exact hl i
  · exact hr i
#align pgame.right_moves_add_cases SetTheory.PGame.rightMoves_add_cases

instance isEmpty_nat_rightMoves : ∀ n : ℕ, IsEmpty (RightMoves n)
  | 0 => inferInstanceAs (IsEmpty PEmpty)
  | n + 1 => by
    haveI := isEmpty_nat_rightMoves n
    rw [PGame.nat_succ, rightMoves_add]
    infer_instance
#align pgame.is_empty_nat_right_moves SetTheory.PGame.isEmpty_nat_rightMoves

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def Relabelling.addCongr : ∀ {w x y z : PGame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
  | ⟨wl, wr, wL, wR⟩, ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩, ⟨L₁, R₁, hL₁, hR₁⟩,
    ⟨L₂, R₂, hL₂, hR₂⟩ => by
    let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩
    let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩
    refine ⟨Equiv.sumCongr L₁ L₂, Equiv.sumCongr R₁ R₂, ?_, ?_⟩ <;> rintro (i | j)
    · exact (hL₁ i).addCongr Hyz
    · exact Hwx.addCongr (hL₂ j)
    · exact (hR₁ i).addCongr Hyz
    · exact Hwx.addCongr (hR₂ j)
termination_by _ x _ z => (x, z)
#align pgame.relabelling.add_congr SetTheory.PGame.Relabelling.addCongr

instance : Sub PGame :=
  ⟨fun x y => x + -y⟩

@[simp]
theorem sub_zero (x : PGame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by rw [neg_zero]
#align pgame.sub_zero SetTheory.PGame.sub_zero

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def Relabelling.subCongr {w x y z : PGame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr
#align pgame.relabelling.sub_congr SetTheory.PGame.Relabelling.subCongr

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def negAddRelabelling : ∀ x y : PGame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.refl _, Equiv.refl _, ?_, ?_⟩
    all_goals
      exact fun j =>
        Sum.casesOn j (fun j => negAddRelabelling _ _) fun j =>
          negAddRelabelling ⟨xl, xr, xL, xR⟩ _
termination_by x y => (x, y)
#align pgame.neg_add_relabelling SetTheory.PGame.negAddRelabelling

theorem neg_add_le {x y : PGame} : -(x + y) ≤ -x + -y :=
  (negAddRelabelling x y).le
#align pgame.neg_add_le SetTheory.PGame.neg_add_le

/-- `x + y` has exactly the same moves as `y + x`. -/
def addCommRelabelling : ∀ x y : PGame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;> rintro (_ | _) <;>
      · dsimp
        apply addCommRelabelling
termination_by x y => (x, y)
#align pgame.add_comm_relabelling SetTheory.PGame.addCommRelabelling

theorem add_comm_le {x y : PGame} : x + y ≤ y + x :=
  (addCommRelabelling x y).le
#align pgame.add_comm_le SetTheory.PGame.add_comm_le

theorem add_comm_equiv {x y : PGame} : x + y ≈ y + x :=
  (addCommRelabelling x y).equiv
#align pgame.add_comm_equiv SetTheory.PGame.add_comm_equiv

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def addAssocRelabelling : ∀ x y z : PGame.{u}, x + y + z ≡r x + (y + z)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩ => by
    refine ⟨Equiv.sumAssoc _ _ _, Equiv.sumAssoc _ _ _, ?_, ?_⟩
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yL i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zL i)
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yR i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zR i)
termination_by x y z => (x, y, z)
#align pgame.add_assoc_relabelling SetTheory.PGame.addAssocRelabelling

theorem add_assoc_equiv {x y z : PGame} : x + y + z ≈ x + (y + z) :=
  (addAssocRelabelling x y z).equiv
#align pgame.add_assoc_equiv SetTheory.PGame.add_assoc_equiv

theorem add_left_neg_le_zero : ∀ x : PGame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ =>
    le_zero.2 fun i => by
      cases' i with i i
      · -- If Left played in -x, Right responds with the same move in x.
        refine ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), ?_⟩
        convert @add_left_neg_le_zero (xR i)
        apply add_moveRight_inr
      · -- If Left in x, Right responds with the same move in -x.
        dsimp
        refine ⟨@toRightMovesAdd ⟨_, _, _, _⟩ _ (Sum.inl i), ?_⟩
        convert @add_left_neg_le_zero (xL i)
        apply add_moveRight_inl
#align pgame.add_left_neg_le_zero SetTheory.PGame.add_left_neg_le_zero

theorem zero_le_add_left_neg (x : PGame) : 0 ≤ -x + x := by
  rw [← neg_le_neg_iff, neg_zero]
  exact neg_add_le.trans (add_left_neg_le_zero _)
#align pgame.zero_le_add_left_neg SetTheory.PGame.zero_le_add_left_neg

theorem add_left_neg_equiv (x : PGame) : -x + x ≈ 0 :=
  ⟨add_left_neg_le_zero x, zero_le_add_left_neg x⟩
#align pgame.add_left_neg_equiv SetTheory.PGame.add_left_neg_equiv

theorem add_right_neg_le_zero (x : PGame) : x + -x ≤ 0 :=
  add_comm_le.trans (add_left_neg_le_zero x)
#align pgame.add_right_neg_le_zero SetTheory.PGame.add_right_neg_le_zero

theorem zero_le_add_right_neg (x : PGame) : 0 ≤ x + -x :=
  (zero_le_add_left_neg x).trans add_comm_le
#align pgame.zero_le_add_right_neg SetTheory.PGame.zero_le_add_right_neg

theorem add_right_neg_equiv (x : PGame) : x + -x ≈ 0 :=
  ⟨add_right_neg_le_zero x, zero_le_add_right_neg x⟩
#align pgame.add_right_neg_equiv SetTheory.PGame.add_right_neg_equiv

theorem sub_self_equiv : ∀ (x : PGame), x - x ≈ 0 :=
  add_right_neg_equiv
#align pgame.sub_self_equiv SetTheory.PGame.sub_self_equiv

private theorem add_le_add_right' : ∀ {x y z : PGame}, x ≤ y → x + z ≤ y + z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => fun h => by
    refine le_def.2 ⟨fun i => ?_, fun i => ?_⟩ <;> cases' i with i i
    · rw [le_def] at h
      cases' h with h_left h_right
      rcases h_left i with (⟨i', ih⟩ | ⟨j, jh⟩)
      · exact Or.inl ⟨toLeftMovesAdd (Sum.inl i'), add_le_add_right' ih⟩
      · refine Or.inr ⟨toRightMovesAdd (Sum.inl j), ?_⟩
        convert add_le_add_right' jh
        apply add_moveRight_inl
    · exact Or.inl ⟨@toLeftMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
    · rw [le_def] at h
      rcases h.right i with (⟨i, ih⟩ | ⟨j', jh⟩)
      · refine Or.inl ⟨toLeftMovesAdd (Sum.inl i), ?_⟩
        convert add_le_add_right' ih
        apply add_moveLeft_inl
      · exact Or.inr ⟨toRightMovesAdd (Sum.inl j'), add_le_add_right' jh⟩
    · exact
        Or.inr ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
termination_by x y z => (x, y, z)

instance covariantClass_swap_add_le : CovariantClass PGame PGame (swap (· + ·)) (· ≤ ·) :=
  ⟨fun _ _ _ => add_le_add_right'⟩
#align pgame.covariant_class_swap_add_le SetTheory.PGame.covariantClass_swap_add_le

instance covariantClass_add_le : CovariantClass PGame PGame (· + ·) (· ≤ ·) :=
  ⟨fun x _ _ h => (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩
#align pgame.covariant_class_add_le SetTheory.PGame.covariantClass_add_le

theorem add_lf_add_right {y z : PGame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
  suffices z + x ≤ y + x → z ≤ y by
    rw [← PGame.not_le] at h ⊢
    exact mt this h
  fun w =>
  calc
    z ≤ z + 0 := (addZeroRelabelling _).symm.le
    _ ≤ z + (x + -x) := add_le_add_left (zero_le_add_right_neg x) _
    _ ≤ z + x + -x := (addAssocRelabelling _ _ _).symm.le
    _ ≤ y + x + -x := add_le_add_right w _
    _ ≤ y + (x + -x) := (addAssocRelabelling _ _ _).le
    _ ≤ y + 0 := add_le_add_left (add_right_neg_le_zero x) _
    _ ≤ y := (addZeroRelabelling _).le

#align pgame.add_lf_add_right SetTheory.PGame.add_lf_add_right

theorem add_lf_add_left {y z : PGame} (h : y ⧏ z) (x) : x + y ⧏ x + z := by
  rw [lf_congr add_comm_equiv add_comm_equiv]
  apply add_lf_add_right h
#align pgame.add_lf_add_left SetTheory.PGame.add_lf_add_left

instance covariantClass_swap_add_lt : CovariantClass PGame PGame (swap (· + ·)) (· < ·) :=
  ⟨fun x _ _ h => ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩⟩
#align pgame.covariant_class_swap_add_lt SetTheory.PGame.covariantClass_swap_add_lt

instance covariantClass_add_lt : CovariantClass PGame PGame (· + ·) (· < ·) :=
  ⟨fun x _ _ h => ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩⟩
#align pgame.covariant_class_add_lt SetTheory.PGame.covariantClass_add_lt

theorem add_lf_add_of_lf_of_le {w x y z : PGame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
  lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)
#align pgame.add_lf_add_of_lf_of_le SetTheory.PGame.add_lf_add_of_lf_of_le

theorem add_lf_add_of_le_of_lf {w x y z : PGame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
  lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)
#align pgame.add_lf_add_of_le_of_lf SetTheory.PGame.add_lf_add_of_le_of_lf

theorem add_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
  ⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
    (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩
#align pgame.add_congr SetTheory.PGame.add_congr

theorem add_congr_left {x y z : PGame} (h : x ≈ y) : x + z ≈ y + z :=
  add_congr h equiv_rfl
#align pgame.add_congr_left SetTheory.PGame.add_congr_left

theorem add_congr_right {x y z : PGame} : (y ≈ z) → (x + y ≈ x + z) :=
  add_congr equiv_rfl
#align pgame.add_congr_right SetTheory.PGame.add_congr_right

theorem sub_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
  add_congr h₁ (neg_equiv_neg_iff.2 h₂)
#align pgame.sub_congr SetTheory.PGame.sub_congr

theorem sub_congr_left {x y z : PGame} (h : x ≈ y) : x - z ≈ y - z :=
  sub_congr h equiv_rfl
#align pgame.sub_congr_left SetTheory.PGame.sub_congr_left

theorem sub_congr_right {x y z : PGame} : (y ≈ z) → (x - y ≈ x - z) :=
  sub_congr equiv_rfl
#align pgame.sub_congr_right SetTheory.PGame.sub_congr_right

theorem le_iff_sub_nonneg {x y : PGame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => (zero_le_add_right_neg x).trans (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ≤ y - x + x := add_le_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩
#align pgame.le_iff_sub_nonneg SetTheory.PGame.le_iff_sub_nonneg

theorem lf_iff_sub_zero_lf {x y : PGame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h => (zero_le_add_right_neg x).trans_lf (add_lf_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ⧏ y - x + x := add_lf_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩
#align pgame.lf_iff_sub_zero_lf SetTheory.PGame.lf_iff_sub_zero_lf

theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (zero_le_add_right_neg x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ < y - x + x := add_lt_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩
#align pgame.lt_iff_sub_pos SetTheory.PGame.lt_iff_sub_pos

/-! ### Special pre-games -/


/-- The pre-game `star`, which is fuzzy with zero. -/
def star : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => 0⟩
#align pgame.star SetTheory.PGame.star

@[simp]
theorem star_leftMoves : star.LeftMoves = PUnit :=
  rfl
#align pgame.star_left_moves SetTheory.PGame.star_leftMoves

@[simp]
theorem star_rightMoves : star.RightMoves = PUnit :=
  rfl
#align pgame.star_right_moves SetTheory.PGame.star_rightMoves

@[simp]
theorem star_moveLeft (x) : star.moveLeft x = 0 :=
  rfl
#align pgame.star_move_left SetTheory.PGame.star_moveLeft

@[simp]
theorem star_moveRight (x) : star.moveRight x = 0 :=
  rfl
#align pgame.star_move_right SetTheory.PGame.star_moveRight

instance uniqueStarLeftMoves : Unique star.LeftMoves :=
  PUnit.unique
#align pgame.unique_star_left_moves SetTheory.PGame.uniqueStarLeftMoves

instance uniqueStarRightMoves : Unique star.RightMoves :=
  PUnit.unique
#align pgame.unique_star_right_moves SetTheory.PGame.uniqueStarRightMoves

theorem star_fuzzy_zero : star ‖ 0 :=
  ⟨by
    rw [lf_zero]
    use default
    rintro ⟨⟩,
   by
    rw [zero_lf]
    use default
    rintro ⟨⟩⟩
#align pgame.star_fuzzy_zero SetTheory.PGame.star_fuzzy_zero

@[simp]
theorem neg_star : -star = star := by simp [star]
#align pgame.neg_star SetTheory.PGame.neg_star

@[simp]
protected theorem zero_lt_one : (0 : PGame) < 1 :=
  lt_of_le_of_lf (zero_le_of_isEmpty_rightMoves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)
#align pgame.zero_lt_one SetTheory.PGame.zero_lt_one

instance : ZeroLEOneClass PGame :=
  ⟨PGame.zero_lt_one.le⟩

@[simp]
theorem zero_lf_one : (0 : PGame) ⧏ 1 :=
  PGame.zero_lt_one.lf
#align pgame.zero_lf_one SetTheory.PGame.zero_lf_one

end PGame
