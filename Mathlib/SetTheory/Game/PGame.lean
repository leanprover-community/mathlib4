/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Yuyang Zhao
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

Combinatorial games themselves, as a quotient of pregames, are constructed in
`SetTheory.Game.Basic`.

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

namespace SetTheory

open Function Relation

/-- The typeclass behind the notation `x ∈ₗ y : Prop` and `x ∈ᵣ y : Prop` where `x y : α`. -/
class LeftRightOption (α : Type*) where
  /-- The left option relation `x ∈ₗ y`. -/
  memₗ : α → α → Prop
  /-- The right option relation `x ∈ₗ y`. -/
  memᵣ : α → α → Prop

@[inherit_doc] scoped infix:50 " ∈ₗ " => LeftRightOption.memₗ
@[inherit_doc] scoped infix:50 " ∈ᵣ " => LeftRightOption.memᵣ
@[inherit_doc LeftRightOption.memₗ] scoped binder_predicate x " ∈ₗ " y:term => `($x ∈ₗ $y)
@[inherit_doc LeftRightOption.memᵣ] scoped binder_predicate x " ∈ᵣ " y:term => `($x ∈ᵣ $y)

/-! ### Pre-game moves -/

universe u

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

lemma ext' {x y : PGame} (hl : x.LeftMoves = y.LeftMoves) (hr : x.RightMoves = y.RightMoves)
    (hL : HEq x.moveLeft y.moveLeft) (hR : HEq x.moveRight y.moveRight) :
    x = y := by
  cases x; cases y; cases hl; cases hr; cases hL; cases hR; rfl

lemma ext {x y : PGame} (hl : x.LeftMoves = y.LeftMoves) (hr : x.RightMoves = y.RightMoves)
    (hL : ∀ i j, HEq i j → x.moveLeft i = y.moveLeft j)
    (hR : ∀ i j, HEq i j → x.moveRight i = y.moveRight j) :
    x = y :=
  ext' hl hr (hfunext hl (heq_of_eq <| hL · · ·)) (hfunext hr (heq_of_eq <| hR · · ·))

-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
def ofLists (L R : List PGame.{u}) : PGame.{u} :=
  mk (ULift (Fin L.length)) (ULift (Fin R.length)) (fun i => L[i.down.1]) fun j ↦ R[j.down.1]
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

variable {xl xr : Type u}

-- This is different from mk_right from the POV of the simplifier,
-- because the unifier can't solve `xr =?= RightMoves (mk xl xr xL xR)` at reducible transparency.
@[simp]
theorem Subsequent.mk_right' (xL : xl → PGame) (xR : xr → PGame) (j : RightMoves (mk xl xr xL xR)) :
    Subsequent (xR j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveRight_mk_left {xR : xr → PGame} {i : xl} (xL : xl → PGame) (j) :
    Subsequent ((xL i).moveRight j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveRight_mk_right {xL : xl → PGame} {i : xr} (xR : xr → PGame) (j) :
    Subsequent ((xR i).moveRight j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveLeft_mk_left {xR : xr → PGame} {i : xl} (xL : xl → PGame) (j) :
    Subsequent ((xL i).moveLeft j) (mk xl xr xL xR) := by
  pgame_wf_tac

@[simp] theorem Subsequent.moveLeft_mk_right {xL : xl → PGame} {i : xr} (xR : xr → PGame) (j) :
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

/-! ### Identity -/

/-- Two pre-games are identical if their left and right sets are identical.
That is, `Identical x y` if every left move of `x` is identical to some left move of `y`,
every right move of `x` is identical to some right move of `y`, and vice versa. -/
def Identical : ∀ (_ _ : PGame), Prop
  | mk _ _ xL xR, mk _ _ yL yR =>
    Relator.BiTotal (fun i j ↦ Identical (xL i) (yL j)) ∧
      Relator.BiTotal (fun i j ↦ Identical (xR i) (yR j))

@[inherit_doc] scoped infix:50 " ≡ " => PGame.Identical

instance : LeftRightOption PGame where
  memₗ x y := ∃ b, x ≡ (y.moveLeft b)
  memᵣ x y := ∃ b, x ≡ (y.moveRight b)

theorem identical_iff : ∀ {x y : PGame}, Identical x y ↔
    Relator.BiTotal (x.moveLeft · ≡ y.moveLeft ·) ∧ Relator.BiTotal (x.moveRight · ≡ y.moveRight ·)
  | mk _ _ _ _, mk _ _ _ _ => Iff.rfl

@[refl, simp] protected theorem Identical.refl (x) : x ≡ x :=
  PGame.recOn x fun _ _ _ _ IHL IHR ↦ ⟨Relator.BiTotal.refl IHL, Relator.BiTotal.refl IHR⟩

protected theorem Identical.rfl {x} : x ≡ x := Identical.refl x

@[symm] protected theorem Identical.symm : ∀ {x y}, x ≡ y → y ≡ x
  | mk _ _ _ _, mk _ _ _ _, ⟨hL, hR⟩ => ⟨hL.symm fun _ _ h ↦ h.symm, hR.symm fun _ _ h ↦ h.symm⟩

theorem identical_comm {x y} : x ≡ y ↔ y ≡ x :=
  ⟨Identical.symm, Identical.symm⟩

@[trans] protected theorem Identical.trans : ∀ {x y z}, x ≡ y → y ≡ z → x ≡ z
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _, ⟨hL₁, hR₁⟩, ⟨hL₂, hR₂⟩ =>
    ⟨hL₁.trans (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) hL₂, hR₁.trans (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) hR₂⟩

theorem identical_of_is_empty (x y : PGame)
    [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves]
    [IsEmpty y.LeftMoves] [IsEmpty y.RightMoves] : x ≡ y :=
  identical_iff.2 <| by simp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal]

/-- `Identical` as a `Setoid`. -/
def identicalSetoid : Setoid PGame :=
  ⟨Identical, Identical.refl, Identical.symm, Identical.trans⟩

instance : IsRefl PGame (· ≡ ·) := ⟨Identical.refl⟩
instance : IsSymm PGame (· ≡ ·) := ⟨fun _ _ ↦ Identical.symm⟩
instance : IsTrans PGame (· ≡ ·) := ⟨fun _ _ _ ↦ Identical.trans⟩
instance : IsEquiv PGame (· ≡ ·) := { }

set_option linter.unusedVariables false in
/-- A left move of `x` is identical to some left move of `y`. -/
lemma Identical.moveLeft : ∀ {x y} (r : x ≡ y) (i : x.LeftMoves),
    ∃ j, x.moveLeft i ≡ y.moveLeft j
  | mk _ _ _ _, mk _ _ _ _, ⟨hl, hr⟩, i => hl.1 i

set_option linter.unusedVariables false in
/-- A left move of `y` is identical to some left move of `x`. -/
lemma Identical.moveLeft_symm : ∀ {x y} (r : x ≡ y) (i : y.LeftMoves),
    ∃ j, x.moveLeft j ≡ y.moveLeft i
  | mk _ _ _ _, mk _ _ _ _, ⟨hl, hr⟩, i => hl.2 i

set_option linter.unusedVariables false in
/-- A right move of `x` is identical to some right move of `y`. -/
lemma Identical.moveRight : ∀ {x y} (r : x ≡ y) (i : x.RightMoves),
    ∃ j, x.moveRight i ≡ y.moveRight j
  | mk _ _ _ _, mk _ _ _ _, ⟨hl, hr⟩, i => hr.1 i

set_option linter.unusedVariables false in
/-- A right move of `y` is identical to some right move of `x`. -/
lemma Identical.moveRight_symm : ∀ {x y} (r : x ≡ y) (i : y.RightMoves),
    ∃ j, x.moveRight j ≡ y.moveRight i
  | mk _ _ _ _, mk _ _ _ _, ⟨hl, hr⟩, i => hr.2 i

lemma Identical.trans_eq {x y z} (h₁ : x ≡ y) (h₂ : y = z) : x ≡ z := h₁.trans (of_eq h₂)

theorem identical_iff' : ∀ {x y : PGame}, x ≡ y ↔
    ((∀ i, x.moveLeft i ∈ₗ y) ∧ (∀ j, y.moveLeft j ∈ₗ x)) ∧
      ((∀ i, x.moveRight i ∈ᵣ y) ∧ (∀ j, y.moveRight j ∈ᵣ x))
  | mk xl xr xL xR, mk yl yr yL yR => by
    convert identical_iff <;>
    dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal] <;>
    congr! <;>
    exact exists_congr <| fun _ ↦ identical_comm

set_option linter.unusedVariables false in
theorem memₗ.congr_right : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, w ∈ₗ x ↔ w ∈ₗ y)
  | mk xl xr xL xR, mk yl yr yL yR, ⟨⟨h₁, h₂⟩, _⟩, _w =>
    ⟨fun ⟨i, hi⟩ ↦ (h₁ i).imp (fun _ ↦ hi.trans),
      fun ⟨j, hj⟩ ↦ (h₂ j).imp (fun _ hi ↦ hj.trans hi.symm)⟩

set_option linter.unusedVariables false in
theorem memᵣ.congr_right : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, w ∈ᵣ x ↔ w ∈ᵣ y)
  | mk xl xr xL xR, mk yl yt yL yR, ⟨_, ⟨h₁, h₂⟩⟩, _w =>
    ⟨fun ⟨i, hi⟩ ↦ (h₁ i).imp (fun _ ↦ hi.trans),
      fun ⟨j, hj⟩ ↦ (h₂ j).imp (fun _ hi ↦ hj.trans hi.symm)⟩

set_option linter.unusedVariables false in
theorem memₗ.congr_left : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, x ∈ₗ w ↔ y ∈ₗ w)
  | x, y, h, mk l r L R => ⟨fun ⟨i, hi⟩ ↦ ⟨i, h.symm.trans hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, h.trans hi⟩⟩

set_option linter.unusedVariables false in
theorem memᵣ.congr_left : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, x ∈ᵣ w ↔ y ∈ᵣ w)
  | x, y, h, mk l r L R => ⟨fun ⟨i, hi⟩ ↦ ⟨i, h.symm.trans hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, h.trans hi⟩⟩

set_option linter.unusedVariables false in
lemma Identical.ext : ∀ {x y} (hl : ∀ z, z ∈ₗ x ↔ z ∈ₗ y) (hr : ∀ z, z ∈ᵣ x ↔ z ∈ᵣ y), x ≡ y
  | mk xl xr xL xR, mk yl yr yL yR, hl, hr => identical_iff'.mpr
    ⟨⟨fun i ↦ (hl _).mp ⟨i, refl _⟩, fun j ↦ (hl _).mpr ⟨j, refl _⟩⟩,
      ⟨fun i ↦ (hr _).mp ⟨i, refl _⟩, fun j ↦ (hr _).mpr ⟨j, refl _⟩⟩⟩

lemma Identical.ext_iff {x y} : x ≡ y ↔ (∀ z, z ∈ₗ x ↔ z ∈ₗ y) ∧ (∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) :=
  ⟨fun h ↦ ⟨@memₗ.congr_right _ _ h, @memᵣ.congr_right _ _ h⟩, fun h ↦ h.elim Identical.ext⟩

lemma Identical.congr_right {x y z} (h : x ≡ y) : z ≡ x ↔ z ≡ y :=
  ⟨fun hz ↦ hz.trans h, fun hz ↦ hz.trans h.symm⟩

lemma Identical.congr_left {x y z} (h : x ≡ y) : x ≡ z ↔ y ≡ z :=
  ⟨fun hz ↦ h.symm.trans hz, fun hz ↦ h.trans hz⟩

lemma Identical.of_fn {x y : PGame}
    (l : x.LeftMoves → y.LeftMoves) (il : y.LeftMoves → x.LeftMoves)
    (r : x.RightMoves → y.RightMoves) (ir : y.RightMoves → x.RightMoves)
    (hl : ∀ i, x.moveLeft i ≡ y.moveLeft (l i))
    (hil : ∀ i, x.moveLeft (il i) ≡ y.moveLeft i)
    (hr : ∀ i, x.moveRight i ≡ y.moveRight (r i))
    (hir : ∀ i, x.moveRight (ir i) ≡ y.moveRight i) : x ≡ y :=
  identical_iff.mpr
    ⟨⟨fun i ↦ ⟨l i, hl i⟩, fun i ↦ ⟨il i, hil i⟩⟩,
      ⟨fun i ↦ ⟨r i, hr i⟩, fun i ↦ ⟨ir i, hir i⟩⟩⟩

lemma Identical.of_equiv {x y : PGame}
    (l : x.LeftMoves ≃ y.LeftMoves) (r : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i, x.moveLeft i ≡ y.moveLeft (l i)) (hr : ∀ i, x.moveRight i ≡ y.moveRight (r i)) :
    x ≡ y :=
  .of_fn l l.symm r r.symm hl (by simpa using hl <| l.symm ·) hr (by simpa using hr <| r.symm ·)

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
  absurd
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

set_option linter.unusedVariables false in
lemma Identical.le : ∀ {x y}, x ≡ y → x ≤ y
  | mk xl xr xL xR, mk yl yr yL yR, ⟨hL, hR⟩ => le_of_forall_lf
    (fun i ↦ let ⟨_, hj⟩ := hL.1 i; lf_of_le_moveLeft hj.le)
    (fun i ↦ let ⟨_, hj⟩ := hR.2 i; lf_of_moveRight_le hj.le)

lemma Identical.ge {x y} (h : x ≡ y) : y ≤ x := h.symm.le

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
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddAbove (Set.range f) := by
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
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddBelow (Set.range f) := by
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

theorem equiv_def {x y : PGame} : x ≈ y ↔ x ≤ y ∧ y ≤ x := Iff.rfl

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

lemma Identical.equiv {x y} (h : x ≡ y) : x ≈ y := ⟨h.le, h.symm.le⟩

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

instance : Trans (· ⧏ ·) (· ≈ ·) (· ⧏ ·) := ⟨lf_of_lf_of_equiv⟩

@[trans]
theorem lf_of_equiv_of_lf {x y z : PGame} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  lf_congr_imp (Equiv.symm h₁) equiv_rfl
#align pgame.lf_of_equiv_of_lf SetTheory.PGame.lf_of_equiv_of_lf

instance : Trans (· ≈ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_equiv_of_lf⟩

@[trans]
theorem lt_of_lt_of_equiv {x y z : PGame} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1
#align pgame.lt_of_lt_of_equiv SetTheory.PGame.lt_of_lt_of_equiv

instance : Trans
    ((· < ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_lt_of_equiv

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

theorem Equiv.ext {x y : PGame}
    (hl : Relator.BiTotal (fun i j ↦ x.moveLeft i ≈ y.moveLeft j))
    (hr : Relator.BiTotal (fun i j ↦ x.moveRight i ≈ y.moveRight j)) : x ≈ y := by
  constructor <;> rw [le_def]
  · exact ⟨fun i ↦ .inl <| (hl.1 i).imp (fun _ ↦ (·.1)),
      fun j ↦ .inr <| (hr.2 j).imp (fun _ ↦ (·.1))⟩
  · exact ⟨fun i ↦ .inl <| (hl.2 i).imp (fun _ ↦ (·.2)),
      fun j ↦ .inr <| (hr.1 j).imp (fun _ ↦ (·.2))⟩

lemma Equiv.of_fn {x y : PGame}
    (l : x.LeftMoves → y.LeftMoves) (il : y.LeftMoves → x.LeftMoves)
    (r : x.RightMoves → y.RightMoves) (ir : y.RightMoves → x.RightMoves)
    (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (l i))
    (hil : ∀ i, x.moveLeft (il i) ≈ y.moveLeft i)
    (hr : ∀ i, x.moveRight i ≈ y.moveRight (r i))
    (hir : ∀ i, x.moveRight (ir i) ≈ y.moveRight i) : x ≈ y :=
  .ext ⟨fun i ↦ ⟨l i, hl i⟩, fun i ↦ ⟨il i, hil i⟩⟩ ⟨fun i ↦ ⟨r i, hr i⟩, fun i ↦ ⟨ir i, hir i⟩⟩

lemma Equiv.of_equiv {x y : PGame}
    (l : x.LeftMoves ≃ y.LeftMoves) (r : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (l i)) (hr : ∀ i, x.moveRight i ≈ y.moveRight (r i)) :
    x ≈ y :=
  .of_fn l l.symm r r.symm hl (by simpa using hl <| l.symm ·) hr (by simpa using hr <| r.symm ·)
#align pgame.equiv_of_mk_equiv SetTheory.PGame.Equiv.of_equiv

theorem Equiv.ext' {x y : PGame}
    (hl : (∀ a ∈ₗ x, ∃ b ∈ₗ y, a ≈ b) ∧ (∀ b ∈ₗ y, ∃ a ∈ₗ x, a ≈ b))
    (hr : (∀ a ∈ᵣ x, ∃ b ∈ᵣ y, a ≈ b) ∧ (∀ b ∈ᵣ y, ∃ a ∈ᵣ x, a ≈ b)) :
    x ≈ y := by
  refine' Equiv.ext (hl.imp (fun h i ↦ _) (fun h i ↦ _)) (hr.imp (fun h i ↦ _) (fun h i ↦ _)) <;>
    obtain ⟨_, ⟨i, hi⟩, h⟩ := h _ ⟨i, refl _⟩
  · exact ⟨i, Equiv.trans h hi.equiv⟩
  · exact ⟨i, Equiv.trans hi.symm.equiv h⟩
  · exact ⟨i, Equiv.trans h hi.equiv⟩
  · exact ⟨i, Equiv.trans hi.symm.equiv h⟩

theorem Equiv.ext'' {x y : PGame}
    (hl : Relator.BiTotal fun (a : {a // a ∈ₗ x}) (b : {b // b ∈ₗ y}) ↦ a.1 ≈ b.1)
    (hr : Relator.BiTotal fun (a : {a // a ∈ᵣ x}) (b : {b // b ∈ᵣ y}) ↦ a.1 ≈ b.1) :
    x ≈ y := by
  refine' Equiv.ext (hl.imp (fun h i ↦ _) (fun h i ↦ _)) (hr.imp (fun h i ↦ _) (fun h i ↦ _)) <;>
    obtain ⟨⟨_, i, hi⟩, h⟩ := h ⟨_, ⟨i, refl _⟩⟩
  · exact ⟨i, Equiv.trans h hi.equiv⟩
  · exact ⟨i, Equiv.trans hi.symm.equiv h⟩
  · exact ⟨i, Equiv.trans h hi.equiv⟩
  · exact ⟨i, Equiv.trans hi.symm.equiv h⟩

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

/-! ### Negation -/


/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : PGame → PGame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩
#align pgame.neg SetTheory.PGame.neg

instance : Neg PGame :=
  ⟨neg⟩

@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (-xR ·) (-xL ·) :=
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
  simp only [ofLists, neg_def, List.getElem_map, mk.injEq, List.length_map, true_and]
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
      simp only [heq_eq_eq]
      congr 5
      exact this (List.length_map _ _).symm h
#align pgame.neg_of_lists SetTheory.PGame.neg_ofLists

theorem isOption_neg {x y : PGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  rw [isOption_iff, isOption_iff, or_comm]
  cases y
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

lemma memₗ_neg_iff : ∀ {x y : PGame},
    x ∈ₗ -y ↔ ∃ i, x ≡ -y.moveRight i
  | mk _ _ _ _, mk _ _ _ _ => Iff.rfl

lemma memᵣ_neg_iff : ∀ {x y : PGame},
    x ∈ᵣ -y ↔ ∃ i, x ≡ -y.moveLeft i
  | mk _ _ _ _, mk _ _ _ _ => Iff.rfl

set_option linter.unusedVariables false in
/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
lemma Identical.neg : ∀ {x₁ x₂ : PGame} (hx : x₁ ≡ x₂), -x₁ ≡ -x₂
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, ⟨⟨hL₁, hL₂⟩, ⟨hR₁, hR₂⟩⟩ =>
    ⟨⟨fun i ↦ (hR₁ i).imp (fun _ ↦ Identical.neg), fun j ↦ (hR₂ j).imp (fun _ ↦ Identical.neg)⟩,
      ⟨fun i ↦ (hL₁ i).imp (fun _ ↦ Identical.neg), fun j ↦ (hL₂ j).imp (fun _ ↦ Identical.neg)⟩⟩

set_option linter.unusedVariables false in
/-- If `-x` has the same moves as `-y`, then `x` has the sames moves as `y`. -/
lemma Identical.of_neg : ∀ {x₁ x₂ : PGame} (hx : -x₁ ≡ -x₂), x₁ ≡ x₂
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R => by
    simpa using Identical.neg (x₁ := mk _ _ (-x₁R ·) (-x₁L ·)) (x₂ := mk _ _ (-x₂R ·) (-x₂L ·))

set_option linter.unusedVariables false in
lemma memₗ_neg_iff' : ∀ {x y : PGame},
    x ∈ₗ -y ↔ ∃ z ∈ᵣ y, x ≡ -z
  | mk xl xr xL xR, mk yl yr yL yR => memₗ_neg_iff.trans
    ⟨fun ⟨_i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.neg⟩⟩

set_option linter.unusedVariables false in
lemma memᵣ_neg_iff' : ∀ {x y : PGame},
    x ∈ᵣ -y ↔ ∃ z ∈ₗ y, x ≡ -z
  | mk xl xr xL xR, mk yl yr yL yR => memᵣ_neg_iff.trans
    ⟨fun ⟨_i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.neg⟩⟩

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
theorem neg_identical_neg_iff {x y : PGame} : (-x ≡ -y) ↔ (x ≡ y) :=
  ⟨Identical.of_neg, Identical.neg⟩

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

@[simp]
lemma leftMoves_mk_add {xl xr yl yr} {xL xR yL yR} :
    (mk xl xr xL xR + mk yl yr yL yR).LeftMoves =
      ((mk xl xr xL xR).LeftMoves ⊕ (mk yl yr yL yR).LeftMoves) :=
  rfl

@[simp]
lemma rightMoves_mk_add {xl xr yl yr} {xL xR yL yR} :
    (mk xl xr xL xR + mk yl yr yL yR).RightMoves =
      ((mk xl xr xL xR).RightMoves ⊕ (mk yl yr yL yR).RightMoves) :=
  rfl

@[simp]
theorem mk_add_moveLeft {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft i =
      i.elim (xL · + mk yl yr yL yR) (mk xl xr xL xR + yL ·) :=
  rfl

@[simp]
theorem mk_add_moveRight {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight i =
      i.elim (xR · + mk yl yr yL yR) (mk xl xr xL xR + yR ·) :=
  rfl

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

theorem leftMoves_add : ∀ x y : PGame.{u}, (x + y).LeftMoves = (x.LeftMoves ⊕ y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_add SetTheory.PGame.leftMoves_add

theorem rightMoves_add : ∀ x y : PGame.{u}, (x + y).RightMoves = (x.RightMoves ⊕ y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_add SetTheory.PGame.rightMoves_add

/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesAdd {x y : PGame} : (x.LeftMoves ⊕ y.LeftMoves) ≃ (x + y).LeftMoves :=
  Equiv.cast (leftMoves_add x y).symm
#align pgame.to_left_moves_add SetTheory.PGame.toLeftMovesAdd

/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesAdd {x y : PGame} : (x.RightMoves ⊕ y.RightMoves) ≃ (x + y).RightMoves :=
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

lemma LeftMovesAdd.exists {x y : PGame} {p : (x + y).LeftMoves → Prop} :
    (∃ i, p i) ↔ (∃ i, p (toLeftMovesAdd (.inl i))) ∨ (∃ i, p (toLeftMovesAdd (.inr i))) := by
  cases' x with xl xr xL xR
  cases' y with yl yr yL yR
  constructor
  · rintro ⟨(i | i), hi⟩
    exacts [.inl ⟨i, hi⟩, .inr ⟨i, hi⟩]
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    exacts [⟨_, hi⟩, ⟨_, hi⟩]

lemma RightMovesAdd.exists {x y : PGame} {p : (x + y).RightMoves → Prop} :
    (∃ i, p i) ↔ (∃ i, p (toRightMovesAdd (.inl i))) ∨ (∃ i, p (toRightMovesAdd (.inr i))) := by
  cases' x with xl xr xL xR
  cases' y with yl yr yL yR
  constructor
  · rintro ⟨(i | i), hi⟩
    exacts [.inl ⟨i, hi⟩, .inr ⟨i, hi⟩]
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    exacts [⟨_, hi⟩, ⟨_, hi⟩]

lemma memₗ_add_iff : ∀ {x y₁ y₂ : PGame},
    x ∈ₗ y₁ + y₂ ↔ (∃ i, x ≡ (y₁.moveLeft i) + y₂) ∨ (∃ i, x ≡ y₁ + (y₂.moveLeft i))
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _ => LeftMovesAdd.exists

lemma memᵣ_add_iff : ∀ {x y₁ y₂ : PGame},
    x ∈ᵣ y₁ + y₂ ↔ (∃ i, x ≡ (y₁.moveRight i) + y₂) ∨ (∃ i, x ≡ y₁ + (y₂.moveRight i))
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _ => RightMovesAdd.exists

/-- `x + y` has exactly the same moves as `y + x`. -/
protected lemma add_comm (x y : PGame) : x + y ≡ y + x :=
  match x, y with
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine Identical.of_equiv (Equiv.sumComm _ _) (Equiv.sumComm _ _) ?_ ?_ <;>
    · rintro (_ | _) <;>
      · dsimp; exact PGame.add_comm _ _
  termination_by (x, y)

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
protected lemma add_assoc (x y z : PGame) : x + y + z ≡ x + (y + z) :=
  match x, y, z with
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    refine Identical.of_equiv (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) ?_ ?_ <;>
    · rintro ((_ | _) | _)
      · exact PGame.add_assoc _ _ _
      · exact PGame.add_assoc (mk _ _ _ _) _ _
      · exact PGame.add_assoc (mk _ _ _ _) (mk _ _ _ _) _
  termination_by (x, y, z)

/-- `x + 0` has exactly the same moves as `x`. -/
protected lemma add_zero : ∀ (x : PGame), x + 0 ≡ x
  | mk xl xr xL xR => by
    refine Identical.of_equiv (Equiv.sumEmpty _ _) (Equiv.sumEmpty _ _) ?_ ?_ <;>
    · rintro (_ | ⟨⟨⟩⟩)
      exact PGame.add_zero _

/-- `0 + x` has exactly the same moves as `x`. -/
protected lemma zero_add (x : PGame) : 0 + x ≡ x :=
  (PGame.add_comm _ _).trans x.add_zero

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : PGame.{u}) : x + 0 ≈ x :=
  x.add_zero.equiv
#align pgame.add_zero_equiv SetTheory.PGame.add_zero_equiv

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : PGame.{u}) : 0 + x ≈ x :=
  x.zero_add.equiv
#align pgame.zero_add_equiv SetTheory.PGame.zero_add_equiv

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
protected lemma neg_add (x y : PGame) : -(x + y) = -x + -y :=
  match x, y with
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ext rfl rfl ?_ ?_ <;>
    · rintro (i | i) _ ⟨rfl⟩
      · exact PGame.neg_add _ _
      · simpa [Equiv.refl] using PGame.neg_add _ _
  termination_by (x, y)

/-- `-(x + y)` has exactly the same moves as `-y + -x`. -/
protected lemma neg_add_rev (x y : PGame) : -(x + y) ≡ -y + -x :=
  Identical.trans (of_eq (x.neg_add y)) (PGame.add_comm _ _)

lemma identical_zero_iff : ∀ (x : PGame),
    x ≡ 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves
  | mk xl xr xL xR => by
    constructor
    · rintro ⟨h₁, h₂⟩
      dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal] at h₁ h₂
      simp_rw [IsEmpty.forall_iff, and_true, IsEmpty.exists_iff] at h₁ h₂
      exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
    · rintro ⟨h₁, h₂⟩
      exact identical_of_is_empty _ _

/-- Any game without left or right moves is identival to 0. -/
lemma identical_zero (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡ 0 :=
  x.identical_zero_iff.mpr ⟨by infer_instance, by infer_instance⟩

theorem equiv_zero (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≈ 0 :=
  (identical_zero x).equiv
#align pgame.equiv.is_empty SetTheory.PGame.equiv_zero

lemma add_eq_zero_iff' : ∀ (x y : PGame), x + y ≡ 0 ↔ x ≡ 0 ∧ y ≡ 0
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [identical_zero_iff, leftMoves_add, rightMoves_add, isEmpty_sum]
    tauto

lemma add_eq_zero_iff (x y : PGame.{u}) :
    x + y ≡ (0 : PGame.{u}) ↔ x ≡ (0 : PGame.{u}) ∧ y ≡ (0 : PGame.{u}) :=
  add_eq_zero_iff' _ _

lemma Identical.add_right {x₁ x₂ y} : x₁ ≡ x₂ → x₁ + y ≡ x₂ + y :=
  match x₁, x₂, y with
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => by
    intro h
    refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;> rintro (_ | _) <;> try exact ⟨.inr _, h.add_right⟩
    · exact (h.1.1 _).elim (⟨.inl ·, ·.add_right⟩)
    · exact (h.1.2 _).elim (⟨.inl ·, ·.add_right⟩)
    · exact (h.2.1 _).elim (⟨.inl ·, ·.add_right⟩)
    · exact (h.2.2 _).elim (⟨.inl ·, ·.add_right⟩)
  termination_by (x₁, x₂, y)

lemma Identical.add_left {x y₁ y₂} (hy : y₁ ≡ y₂) : x + y₁ ≡ x + y₂ :=
  (x.add_comm y₁).trans (hy.add_right.trans (y₂.add_comm x))

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
lemma Identical.add {x₁ x₂ y₁ y₂ : PGame.{u}} (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) : x₁ + y₁ ≡ x₂ + y₂ :=
  hx.add_right.trans hy.add_left

set_option linter.unusedVariables false in
lemma memₗ_add_iff' : ∀ {x y₁ y₂ : PGame},
    x ∈ₗ y₁ + y₂ ↔ (∃ z ∈ₗ y₁, x ≡ z + y₂) ∨ (∃ z ∈ₗ y₂, x ≡ y₁ + z)
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => memₗ_add_iff.trans <| or_congr
    ⟨fun ⟨i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.add_right⟩⟩
    ⟨fun ⟨i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.add_left⟩⟩

set_option linter.unusedVariables false in
lemma memᵣ_add_iff' : ∀ {x y₁ y₂ : PGame},
    x ∈ᵣ y₁ + y₂ ↔ (∃ z ∈ᵣ y₁, x ≡ z + y₂) ∨ (∃ z ∈ᵣ y₂, x ≡ y₁ + z)
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => memᵣ_add_iff.trans <| or_congr
    ⟨fun ⟨i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.add_right⟩⟩
    ⟨fun ⟨i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.add_left⟩⟩

instance : Sub PGame :=
  ⟨fun x y => x + -y⟩

@[simp]
theorem sub_zero_eq_add_zero (x : PGame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by rw [neg_zero]
#align pgame.sub_zero SetTheory.PGame.sub_zero_eq_add_zero

protected lemma sub_zero (x : PGame) : x - 0 ≡ x :=
  _root_.trans (of_eq x.sub_zero_eq_add_zero) x.add_zero

/-- Use the same name convention as global lemmas. -/
protected lemma neg_sub' (x y : PGame) : -(x - y) = -x - -y := PGame.neg_add _ _

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
lemma Identical.sub {x₁ x₂ y₁ y₂ : PGame.{u}} (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) : x₁ - y₁ ≡ x₂ - y₂ :=
  hx.add hy.neg

theorem neg_add_le {x y : PGame} : -(x + y) ≤ -x + -y :=
  (x.neg_add y).le
#align pgame.neg_add_le SetTheory.PGame.neg_add_le

theorem add_comm_le {x y : PGame} : x + y ≤ y + x :=
  (x.add_comm y).le
#align pgame.add_comm_le SetTheory.PGame.add_comm_le

theorem add_comm_equiv {x y : PGame} : x + y ≈ y + x :=
  (x.add_comm y).equiv
#align pgame.add_comm_equiv SetTheory.PGame.add_comm_equiv

theorem add_assoc_equiv {x y z : PGame} : x + y + z ≈ x + (y + z) :=
  (x.add_assoc y z).equiv
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
decreasing_by all_goals pgame_wf_tac

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
    z ≤ z + 0 := (PGame.add_zero _).symm.le
    _ ≤ z + (x + -x) := (add_le_add_left (zero_le_add_right_neg x) _)
    _ ≤ z + x + -x := (PGame.add_assoc _ _ _).symm.le
    _ ≤ y + x + -x := (add_le_add_right w _)
    _ ≤ y + (x + -x) := (PGame.add_assoc _ _ _).le
    _ ≤ y + 0 := (add_le_add_left (add_right_neg_le_zero x) _)
    _ ≤ y := (PGame.add_zero _).le
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
      x ≤ 0 + x := (PGame.zero_add x).symm.le
      _ ≤ y - x + x := (add_le_add_right h _)
      _ ≤ y + (-x + x) := (PGame.add_assoc _ _ _).le
      _ ≤ y + 0 := (add_le_add_left (add_left_neg_le_zero x) _)
      _ ≤ y := (PGame.add_zero y).le
      ⟩
#align pgame.le_iff_sub_nonneg SetTheory.PGame.le_iff_sub_nonneg

theorem lf_iff_sub_zero_lf {x y : PGame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h => (zero_le_add_right_neg x).trans_lf (add_lf_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (PGame.zero_add x).symm.le
      _ ⧏ y - x + x := (add_lf_add_right h _)
      _ ≤ y + (-x + x) := (PGame.add_assoc _ _ _).le
      _ ≤ y + 0 := (add_le_add_left (add_left_neg_le_zero x) _)
      _ ≤ y := (PGame.add_zero y).le
      ⟩
#align pgame.lf_iff_sub_zero_lf SetTheory.PGame.lf_iff_sub_zero_lf

theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (zero_le_add_right_neg x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (PGame.zero_add x).symm.le
      _ < y - x + x := (add_lt_add_right h _)
      _ ≤ y + (-x + x) := (PGame.add_assoc _ _ _).le
      _ ≤ y + 0 := (add_le_add_left (add_left_neg_le_zero x) _)
      _ ≤ y := (PGame.add_zero y).le
      ⟩
#align pgame.lt_iff_sub_pos SetTheory.PGame.lt_iff_sub_pos

/-! ### Multiplication -/


/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, xR*y + x*yL - xR*yL}`. -/
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

@[simp]
theorem neg_mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inl SetTheory.PGame.neg_mk_mul_moveLeft_inl

@[simp]
theorem neg_mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inr SetTheory.PGame.neg_mk_mul_moveLeft_inr

@[simp]
theorem neg_mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inl SetTheory.PGame.neg_mk_mul_moveRight_inl

@[simp]
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

lemma LeftMovesMul.exists {x y : PGame} {p : (x * y).LeftMoves → Prop} :
    (∃ i, p i) ↔
      (∃ i j, p (toLeftMovesMul (.inl (i, j)))) ∨ (∃ i j, p (toLeftMovesMul (.inr (i, j)))) := by
  cases' x with xl xr xL xR
  cases' y with yl yr yL yR
  constructor
  · rintro ⟨(⟨i, j⟩ | ⟨i, j⟩), hi⟩
    exacts [.inl ⟨i, j, hi⟩, .inr ⟨i, j, hi⟩]
  · rintro (⟨i, j, h⟩ | ⟨i, j, h⟩)
    exacts [⟨_, h⟩, ⟨_, h⟩]

lemma RightMovesMul.exists {x y : PGame} {p : (x * y).RightMoves → Prop} :
    (∃ i, p i) ↔
      (∃ i j, p (toRightMovesMul (.inl (i, j)))) ∨ (∃ i j, p (toRightMovesMul (.inr (i, j)))) := by
  cases' x with xl xr xL xR
  cases' y with yl yr yL yR
  constructor
  · rintro ⟨(⟨i, j⟩ | ⟨i, j⟩), hi⟩
    exacts [.inl ⟨i, j, hi⟩, .inr ⟨i, j, hi⟩]
  · rintro (⟨i, j, h⟩ | ⟨i, j, h⟩)
    exacts [⟨_, h⟩, ⟨_, h⟩]

lemma memₗ_mul_iff : ∀ {x y₁ y₂ : PGame},
    x ∈ₗ y₁ * y₂ ↔
      (∃ i j, x ≡ y₁.moveLeft i * y₂ + y₁ * y₂.moveLeft j - y₁.moveLeft i * y₂.moveLeft j) ∨
      (∃ i j, x ≡ y₁.moveRight i * y₂ + y₁ * y₂.moveRight j - y₁.moveRight i * y₂.moveRight j)
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _ => LeftMovesMul.exists

lemma memᵣ_mul_iff : ∀ {x y₁ y₂ : PGame},
    x ∈ᵣ y₁ * y₂ ↔
      (∃ i j, x ≡ y₁.moveLeft i * y₂ + y₁ * y₂.moveRight j - y₁.moveLeft i * y₂.moveRight j) ∨
      (∃ i j, x ≡ y₁.moveRight i * y₂ + y₁ * y₂.moveLeft j - y₁.moveRight i * y₂.moveLeft j)
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _ => RightMovesMul.exists

/-- `x * y` and `y * x` have the same moves. -/
protected lemma mul_comm (x y : PGame) : x * y ≡ y * x :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine Identical.of_equiv ((Equiv.prodComm _ _).sumCongr (Equiv.prodComm _ _))
      ((Equiv.sumComm _ _).trans ((Equiv.prodComm _ _).sumCongr (Equiv.prodComm _ _))) ?_ ?_ <;>
    · rintro (⟨_, _⟩ | ⟨_, _⟩) <;>
      exact ((((PGame.mul_comm _ (mk _ _ _ _)).add (PGame.mul_comm (mk _ _ _ _) _)).trans
        (PGame.add_comm _ _)).sub (PGame.mul_comm _ _))
  termination_by (x, y)

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : PGame) : x * y ≈ y * x :=
  (x.mul_comm y).equiv
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
protected lemma mul_zero (x : PGame) : x * 0 ≡ 0 := identical_zero _

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : PGame) : x * 0 ≈ 0 :=
  x.mul_zero.equiv
#align pgame.mul_zero_equiv SetTheory.PGame.mul_zero_equiv

/-- `0 * x` has exactly the same moves as `0`. -/
protected lemma zero_mul (x : PGame) : 0 * x ≡ 0 := identical_zero _

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : PGame) : 0 * x ≈ 0 :=
  x.zero_mul.equiv
#align pgame.zero_mul_equiv SetTheory.PGame.zero_mul_equiv

/-- `x * -y` and `-(x * y)` have the same moves. -/
protected lemma mul_neg (x y : PGame) : x * -y = -(x * y) :=
  match x, y with
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ext rfl rfl ?_ ?_
    · rintro (⟨i, j⟩ | ⟨i, j⟩) _ ⟨rfl⟩
      · refine mul_moveLeft_inl.trans ?_
        dsimp
        rw [PGame.neg_sub', PGame.neg_add]
        congr
        exacts [PGame.mul_neg _ (mk _ _ _ _), PGame.mul_neg _ _, PGame.mul_neg _ _]
      · refine mul_moveLeft_inr.trans ?_
        dsimp
        rw [PGame.neg_sub', PGame.neg_add]
        congr
        exacts [PGame.mul_neg _ (mk _ _ _ _), PGame.mul_neg _ _, PGame.mul_neg _ _]
    · rintro (⟨i, j⟩ | ⟨i, j⟩) _ ⟨rfl⟩
      · refine mul_moveRight_inl.trans ?_
        dsimp
        rw [PGame.neg_sub', PGame.neg_add]
        congr
        exacts [PGame.mul_neg _ (mk _ _ _ _), PGame.mul_neg _ _, PGame.mul_neg _ _]
      · refine mul_moveRight_inr.trans ?_
        dsimp
        rw [PGame.neg_sub', PGame.neg_add]
        congr
        exacts [PGame.mul_neg _ (mk _ _ _ _), PGame.mul_neg _ _, PGame.mul_neg _ _]
  termination_by (x, y)

/-- `-x * y` and `-(x * y)` have the same moves. -/
protected lemma neg_mul (x y : PGame) : -x * y ≡ -(x * y) :=
  ((PGame.mul_comm _ _).trans (of_eq (PGame.mul_neg _ _))).trans (PGame.mul_comm _ _).neg

/-- `1 * x` has the same moves as `x`. -/
protected lemma one_mul : ∀ (x : PGame), 1 * x ≡ x
  | ⟨xl, xr, xL, xR⟩ => by
    refine Identical.of_equiv ((Equiv.sumEmpty _ _).trans (Equiv.punitProd _))
      ((Equiv.sumEmpty _ _).trans (Equiv.punitProd _)) ?_ ?_ <;>
    · rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩)
      exact ((((PGame.zero_mul (mk _ _ _ _)).add (PGame.one_mul _)).trans (PGame.zero_add _)).sub
        (PGame.zero_mul _)).trans (PGame.sub_zero _)

/-- `x * 1` has the same moves as `x`. -/
protected lemma mul_one (x : PGame) : x * 1 ≡ x := (x.mul_comm _).trans x.one_mul

/-- `x * 1` is equivalent to `x`. -/
theorem mul_one_equiv (x : PGame) : x * 1 ≈ x :=
  x.mul_one.equiv
#align pgame.mul_one_equiv SetTheory.PGame.mul_one_equiv

/-- `1 * x` is equivalent to `x`. -/
theorem one_mul_equiv (x : PGame) : 1 * x ≈ x :=
  x.one_mul.equiv
#align pgame.one_mul_equiv SetTheory.PGame.one_mul_equiv

lemma Identical.mul_right {x₁ x₂ y : PGame.{u}} : x₁ ≡ x₂ → x₁ * y ≡ x₂ * y :=
  match x₁, x₂, y with
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => by
    rintro ⟨⟨hL₁, hL₂⟩, ⟨hR₁, hR₂⟩⟩
    have h : mk x₁l x₁r x₁L x₁R ≡ mk x₂l x₂r x₂L x₂R := ⟨⟨hL₁, hL₂⟩, ⟨hR₁, hR₂⟩⟩
    refine Identical.ext (fun _ ↦ ?_) (fun _ ↦ ?_)
    · simp_rw [memₗ_mul_iff]; congr!
      · exact ⟨fun ⟨i, i', hi⟩ ↦ (hL₁ i).imp (fun j (hj : x₁L i ≡ x₂L j) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg)⟩),
          fun ⟨i, i', hi⟩ ↦ (hL₂ i).imp (fun j (hj : x₁L j ≡ x₂L i) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg).symm⟩)⟩
      · exact ⟨fun ⟨i, i', hi⟩ ↦ (hR₁ i).imp (fun j (hj : x₁R i ≡ x₂R j) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg)⟩),
          fun ⟨i, i', hi⟩ ↦ (hR₂ i).imp (fun j (hj : x₁R j ≡ x₂R i) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg).symm⟩)⟩
    · simp_rw [memᵣ_mul_iff]; congr!
      · exact ⟨fun ⟨i, i', hi⟩ ↦ (hL₁ i).imp (fun j (hj : x₁L i ≡ x₂L j) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg)⟩),
          fun ⟨i, i', hi⟩ ↦ (hL₂ i).imp (fun j (hj : x₁L j ≡ x₂L i) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg).symm⟩)⟩
      · exact ⟨fun ⟨i, i', hi⟩ ↦ (hR₁ i).imp (fun j (hj : x₁R i ≡ x₂R j) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg)⟩),
          fun ⟨i, i', hi⟩ ↦ (hR₂ i).imp (fun j (hj : x₁R j ≡ x₂R i) ↦ ⟨i', hi.trans
            ((hj.mul_right.add h.mul_right).add hj.mul_right.neg).symm⟩)⟩
  termination_by (x₁, x₂, y)
  decreasing_by all_goals pgame_wf_tac

lemma Identical.mul_left {x y₁ y₂} (hy : y₁ ≡ y₂) : x * y₁ ≡ x * y₂ :=
  (x.mul_comm y₁).trans (hy.mul_right.trans (y₂.mul_comm x))

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w * y` has the same moves as `x * z`. -/
lemma Identical.mul {x₁ x₂ y₁ y₂ : PGame.{u}} (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) : x₁ * y₁ ≡ x₂ * y₂ :=
  hx.mul_right.trans hy.mul_left

set_option linter.unusedVariables false in
lemma memₗ_mul_iff' : ∀ {x y₁ y₂ : PGame},
    x ∈ₗ y₁ * y₂ ↔
      (∃ z₁ ∈ₗ y₁, (∃ z₂ ∈ₗ y₂, (x ≡ z₁ * y₂ + y₁ * z₂ - z₁ * z₂))) ∨
      (∃ z₁ ∈ᵣ y₁, (∃ z₂ ∈ᵣ y₂, (x ≡ z₁ * y₂ + y₁ * z₂ - z₁ * z₂)))
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => memₗ_mul_iff.trans <| or_congr
    ⟨fun ⟨i, j, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, _, ⟨_, refl _⟩, hi⟩,
      fun ⟨_, ⟨i, hi⟩, _, ⟨j, hj⟩, h⟩ ↦ ⟨i, j, h.trans
        ((hi.mul_right.add hj.mul_left).sub (hi.mul hj))⟩⟩
    ⟨fun ⟨i, j, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, _, ⟨_, refl _⟩, hi⟩,
      fun ⟨_, ⟨i, hi⟩, _, ⟨j, hj⟩, h⟩ ↦ ⟨i, j, h.trans
        ((hi.mul_right.add hj.mul_left).sub (hi.mul hj))⟩⟩

set_option linter.unusedVariables false in
lemma memᵣ_mul_iff' : ∀ {x y₁ y₂ : PGame},
    x ∈ᵣ y₁ * y₂ ↔
      (∃ z₁ ∈ₗ y₁, (∃ z₂ ∈ᵣ y₂, (x ≡ z₁ * y₂ + y₁ * z₂ - z₁ * z₂))) ∨
      (∃ z₁ ∈ᵣ y₁, (∃ z₂ ∈ₗ y₂, (x ≡ z₁ * y₂ + y₁ * z₂ - z₁ * z₂)))
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => memᵣ_mul_iff.trans <| or_congr
    ⟨fun ⟨i, j, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, _, ⟨_, refl _⟩, hi⟩,
      fun ⟨_, ⟨i, hi⟩, _, ⟨j, hj⟩, h⟩ ↦ ⟨i, j, h.trans
        ((hi.mul_right.add hj.mul_left).sub (hi.mul hj))⟩⟩
    ⟨fun ⟨i, j, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, _, ⟨_, refl _⟩, hi⟩,
      fun ⟨_, ⟨i, hi⟩, _, ⟨j, hj⟩, h⟩ ↦ ⟨i, j, h.trans
        ((hi.mul_right.add hj.mul_left).sub (hi.mul hj))⟩⟩

/-! ### Inserting an option -/

/-- The pregame constructed by inserting `x'` as a new left option into x. -/
def insertLeft (x x' : PGame.{u}) : PGame :=
  match x with
  | mk xl xr xL xR => mk (xl ⊕ PUnit) xr (Sum.elim xL fun _ => x') xR

/-- A new left option cannot hurt Left. -/
lemma le_insertLeft (x x' : PGame) : x ≤ insertLeft x x' := by
  rw [le_def]
  constructor
  · intro i
    left
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [insertLeft, leftMoves_mk, moveLeft_mk, Sum.exists, Sum.elim_inl]
    left
    use i
  · intro j
    right
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [rightMoves_mk, moveRight_mk, insertLeft]
    use j

/-- Adding a gift horse left option does not change the value of `x`. A gift horse left option is
 a game `x'` with `x' ⧏ x`. It is called "gift horse" because it seems like Left has gotten the
 "gift" of a new option, but actually the value of the game did not change. -/
lemma insertLeft_equiv_of_lf {x x' : PGame} (h : x' ⧏ x) : insertLeft x x' ≈ x := by
  rw [equiv_def]
  constructor
  · rw [le_def]
    constructor
    · intro i
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertLeft, leftMoves_mk, moveLeft_mk] at i ⊢
      rcases i with i | _
      · simp only [Sum.elim_inl]
        left
        use i
      · simp only [Sum.elim_inr]
        rw [lf_iff_exists_le] at h
        simp only [leftMoves_mk, moveLeft_mk] at h
        exact h
    · intro j
      right
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertLeft, rightMoves_mk, moveRight_mk]
      use j
  · apply le_insertLeft

/-- The pregame constructed by inserting `x'` as a new right option into x. -/
def insertRight (x x' : PGame.{u}) : PGame :=
  match x with
  | mk xl xr xL xR => mk xl (xr ⊕ PUnit) xL (Sum.elim xR fun _ => x')

theorem neg_insertRight_neg (x x' : PGame.{u}) : (-x).insertRight (-x') = -x.insertLeft x' := by
  cases x
  cases x'
  dsimp [insertRight, insertLeft]
  congr! with (i | j)

theorem neg_insertLeft_neg (x x' : PGame.{u}) : (-x).insertLeft (-x') = -x.insertRight x' := by
  rw [← neg_eq_iff_eq_neg, ← neg_insertRight_neg, neg_neg, neg_neg]

/-- A new right option cannot hurt Right. -/
lemma insertRight_le (x x' : PGame) : insertRight x x' ≤ x := by
  rw [← neg_le_neg_iff, ← neg_insertLeft_neg]
  exact le_insertLeft _ _

/-- Adding a gift horse right option does not change the value of `x`. A gift horse right option is
 a game `x'` with `x ⧏ x'`. It is called "gift horse" because it seems like Right has gotten the
 "gift" of a new option, but actually the value of the game did not change. -/
lemma insertRight_equiv_of_lf {x x' : PGame} (h : x ⧏ x') : insertRight x x' ≈ x := by
  rw [← neg_equiv_neg_iff, ← neg_insertLeft_neg]
  exact insertLeft_equiv_of_lf (neg_lf_neg_iff.mpr h)

/-- Inserting on the left and right commutes. -/
theorem insertRight_insertLeft {x x' x'' : PGame} :
    insertRight (insertLeft x x') x'' = insertLeft (insertRight x x'') x' := by
  cases x; cases x'; cases x''
  dsimp [insertLeft, insertRight]

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

end SetTheory
