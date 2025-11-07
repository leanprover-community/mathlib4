/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "This module is now at `CombinatorialGames.Game.IGame` in the CGT repo <https://github.com/vihdzp/combinatorial-games>"
  (since := "2025-08-06")

/-!
# Combinatorial pregames

This is the first in a series of files developing the basic theory of combinatorial games,
following Conway's book "On Numbers and Games":

* this file defines _pregames_ and elementary operations on them (relabelling, option insertion)
* `Mathlib/SetTheory/PGame/Order.lean` defines an ordering on pregames
* `Mathlib/SetTheory/PGame/Algebra.lean` defines an `AddCommGroup` structure on pregames
* `Mathlib/SetTheory/Game/Basic.lean` defines games as the quotient of pregames by the
  equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`SetTheory.PGame` below) is axiomatised via an inductive type, whose sole constructor
takes two types (thought of as indexing the possible moves for the players Left and Right), and a
pair of functions out of these types to `SetTheory.PGame` (thought of as describing the resulting
game after making a move).

We may denote a game as $\{L | R\}$, where $L$ and $R$ stand for the collections of left and right
moves. This notation is not currently used in Mathlib.

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
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1977]
-/

namespace SetTheory

open Function Relation

/-! ### Pre-game moves -/

universe u

/-- The type of pre-games, before we have quotiented
  by equivalence (`PGame.setoid`). In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `PGame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → PGame) → (β → PGame) → PGame
compile_inductive% PGame

namespace PGame

/-- The indexing type for allowable moves by Left. -/
def LeftMoves : PGame → Type u
  | mk l _ _ _ => l

/-- The indexing type for allowable moves by Right. -/
def RightMoves : PGame → Type u
  | mk _ r _ _ => r

/-- The new game after Left makes an allowed move. -/
def moveLeft : ∀ g : PGame, LeftMoves g → PGame
  | mk _l _ L _ => L

/-- The new game after Right makes an allowed move. -/
def moveRight : ∀ g : PGame, RightMoves g → PGame
  | mk _ _r _ R => R

@[simp]
theorem leftMoves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).LeftMoves = xl :=
  rfl

@[simp]
theorem moveLeft_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).moveLeft = xL :=
  rfl

@[simp]
theorem rightMoves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).RightMoves = xr :=
  rfl

@[simp]
theorem moveRight_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).moveRight = xR :=
  rfl

lemma ext {x y : PGame} (hl : x.LeftMoves = y.LeftMoves) (hr : x.RightMoves = y.RightMoves)
    (hL : ∀ i j, i ≍ j → x.moveLeft i = y.moveLeft j)
    (hR : ∀ i j, i ≍ j → x.moveRight i = y.moveRight j) :
    x = y := by
  cases x
  cases y
  subst hl hr
  simp only [leftMoves_mk, rightMoves_mk, heq_eq_eq, forall_eq', mk.injEq, true_and] at *
  exact ⟨funext hL, funext hR⟩

-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
def ofLists (L R : List PGame.{u}) : PGame.{u} :=
  mk (ULift (Fin L.length)) (ULift (Fin R.length)) (fun i => L[i.down.1]) fun j ↦ R[j.down.1]

theorem leftMoves_ofLists (L R : List PGame) : (ofLists L R).LeftMoves = ULift (Fin L.length) :=
  rfl

theorem rightMoves_ofLists (L R : List PGame) : (ofLists L R).RightMoves = ULift (Fin R.length) :=
  rfl

/-- Converts a number into a left move for `ofLists`.

This is just an abbreviation for `Equiv.ulift.symm` -/
abbrev toOfListsLeftMoves {L R : List PGame} : Fin L.length ≃ (ofLists L R).LeftMoves :=
  Equiv.ulift.symm

/-- Converts a number into a right move for `ofLists`.

This is just an abbreviation for `Equiv.ulift.symm` -/
abbrev toOfListsRightMoves {L R : List PGame} : Fin R.length ≃ (ofLists L R).RightMoves :=
  Equiv.ulift.symm

@[simp]
theorem ofLists_moveLeft' {L R : List PGame} (i : (ofLists L R).LeftMoves) :
    (ofLists L R).moveLeft i = L[i.down.val] :=
  rfl

theorem ofLists_moveLeft {L R : List PGame} (i : Fin L.length) :
    (ofLists L R).moveLeft (ULift.up i) = L[i] :=
  rfl

@[simp]
theorem ofLists_moveRight' {L R : List PGame} (i : (ofLists L R).RightMoves) :
    (ofLists L R).moveRight i = R[i.down.val] :=
  rfl

theorem ofLists_moveRight {L R : List PGame} (i : Fin R.length) :
    (ofLists L R).moveRight (ULift.up i) = R[i] :=
  rfl

/-- A variant of `PGame.recOn` expressed in terms of `PGame.moveLeft` and `PGame.moveRight`.

Both this and `PGame.recOn` describe Conway induction on games. -/
@[elab_as_elim]
def moveRecOn {C : PGame → Sort*} (x : PGame)
    (IH : ∀ y : PGame, (∀ i, C (y.moveLeft i)) → (∀ j, C (y.moveRight j)) → C y) : C x :=
  x.recOn fun yl yr yL yR => IH (mk yl yr yL yR)

/-- `IsOption x y` means that `x` is either a left or right option for `y`. -/
@[mk_iff]
inductive IsOption : PGame → PGame → Prop
  | moveLeft {x : PGame} (i : x.LeftMoves) : IsOption (x.moveLeft i) x
  | moveRight {x : PGame} (i : x.RightMoves) : IsOption (x.moveRight i) x

theorem IsOption.mk_left {xl xr : Type u} (xL : xl → PGame) (xR : xr → PGame) (i : xl) :
    (xL i).IsOption (mk xl xr xL xR) :=
  @IsOption.moveLeft (mk _ _ _ _) i

theorem IsOption.mk_right {xl xr : Type u} (xL : xl → PGame) (xR : xr → PGame) (i : xr) :
    (xR i).IsOption (mk xl xr xL xR) :=
  @IsOption.moveRight (mk _ _ _ _) i

theorem wf_isOption : WellFounded IsOption :=
  ⟨fun x =>
    moveRecOn x fun x IHl IHr =>
      Acc.intro x fun y h => by
        induction h with
        | moveLeft i => exact IHl i
        | moveRight j => exact IHr j⟩

/-- `Subsequent x y` says that `x` can be obtained by playing some nonempty sequence of moves from
`y`. It is the transitive closure of `IsOption`. -/
def Subsequent : PGame → PGame → Prop :=
  TransGen IsOption

instance : IsTrans _ Subsequent :=
  inferInstanceAs <| IsTrans _ (TransGen _)

@[trans]
theorem Subsequent.trans {x y z} : Subsequent x y → Subsequent y z → Subsequent x z :=
  TransGen.trans

theorem wf_subsequent : WellFounded Subsequent :=
  wf_isOption.transGen

instance : WellFoundedRelation PGame :=
  ⟨_, wf_subsequent⟩

@[simp]
theorem Subsequent.moveLeft {x : PGame} (i : x.LeftMoves) : Subsequent (x.moveLeft i) x :=
  TransGen.single (IsOption.moveLeft i)

@[simp]
theorem Subsequent.moveRight {x : PGame} (j : x.RightMoves) : Subsequent (x.moveRight j) x :=
  TransGen.single (IsOption.moveRight j)

@[simp]
theorem Subsequent.mk_left {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i : xl) :
    Subsequent (xL i) (mk xl xr xL xR) :=
  @Subsequent.moveLeft (mk _ _ _ _) i

@[simp]
theorem Subsequent.mk_right {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j : xr) :
    Subsequent (xR j) (mk xl xr xL xR) :=
  @Subsequent.moveRight (mk _ _ _ _) j

/--
Discharges proof obligations of the form `⊢ Subsequent ..` arising in termination proofs
of definitions using well-founded recursion on `PGame`.
-/
macro "pgame_wf_tac" : tactic =>
  `(tactic| solve_by_elim (config := { maxDepth := 8 })
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subsequent.moveLeft, Subsequent.moveRight, Subsequent.mk_left, Subsequent.mk_right,
    Subsequent.trans])

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

/-! ### Basic pre-games -/


/-- The pre-game `Zero` is defined by `0 = { | }`. -/
instance : Zero PGame :=
  ⟨⟨PEmpty, PEmpty, PEmpty.elim, PEmpty.elim⟩⟩

@[simp]
theorem zero_leftMoves : LeftMoves 0 = PEmpty :=
  rfl

@[simp]
theorem zero_rightMoves : RightMoves 0 = PEmpty :=
  rfl

instance isEmpty_zero_leftMoves : IsEmpty (LeftMoves 0) :=
  PEmpty.instIsEmpty

instance isEmpty_zero_rightMoves : IsEmpty (RightMoves 0) :=
  PEmpty.instIsEmpty

instance : Inhabited PGame :=
  ⟨0⟩

/-- The pre-game `One` is defined by `1 = { 0 | }`. -/
instance instOnePGame : One PGame :=
  ⟨⟨PUnit, PEmpty, fun _ => 0, PEmpty.elim⟩⟩

@[simp]
theorem one_leftMoves : LeftMoves 1 = PUnit :=
  rfl

@[simp]
theorem one_moveLeft (x) : moveLeft 1 x = 0 :=
  rfl

@[simp]
theorem one_rightMoves : RightMoves 1 = PEmpty :=
  rfl

instance uniqueOneLeftMoves : Unique (LeftMoves 1) :=
  PUnit.instUnique

instance isEmpty_one_rightMoves : IsEmpty (RightMoves 1) :=
  PEmpty.instIsEmpty

/-! ### Identity -/

/-- Two pre-games are identical if their left and right sets are identical.
That is, `Identical x y` if every left move of `x` is identical to some left move of `y`,
every right move of `x` is identical to some right move of `y`, and vice versa. -/
def Identical : PGame.{u} → PGame.{u} → Prop
  | mk _ _ xL xR, mk _ _ yL yR =>
    Relator.BiTotal (fun i j ↦ Identical (xL i) (yL j)) ∧
      Relator.BiTotal (fun i j ↦ Identical (xR i) (yR j))

@[inherit_doc] scoped infix:50 " ≡ " => PGame.Identical

theorem identical_iff : ∀ {x y : PGame}, x ≡ y ↔
    Relator.BiTotal (x.moveLeft · ≡ y.moveLeft ·) ∧ Relator.BiTotal (x.moveRight · ≡ y.moveRight ·)
  | mk _ _ _ _, mk _ _ _ _ => Iff.rfl

@[refl, simp] protected theorem Identical.refl (x) : x ≡ x :=
  PGame.recOn x fun _ _ _ _ IHL IHR ↦ ⟨Relator.BiTotal.refl IHL, Relator.BiTotal.refl IHR⟩

protected theorem Identical.rfl {x} : x ≡ x := Identical.refl x

@[symm] protected theorem Identical.symm : ∀ {x y}, x ≡ y → y ≡ x
  | mk _ _ _ _, mk _ _ _ _, ⟨hL, hR⟩ => ⟨hL.symm fun _ _ h ↦ h.symm, hR.symm fun _ _ h ↦ h.symm⟩

theorem identical_comm {x y} : x ≡ y ↔ y ≡ x :=
  ⟨.symm, .symm⟩

@[trans] protected theorem Identical.trans : ∀ {x y z}, x ≡ y → y ≡ z → x ≡ z
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _, ⟨hL₁, hR₁⟩, ⟨hL₂, hR₂⟩ =>
    ⟨hL₁.trans (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) hL₂, hR₁.trans (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) hR₂⟩

/-- `x ∈ₗ y` if `x` is identical to some left move of `y`. -/
def memₗ (x y : PGame.{u}) : Prop := ∃ b, x ≡ y.moveLeft b

/-- `x ∈ᵣ y` if `x` is identical to some right move of `y`. -/
def memᵣ (x y : PGame.{u}) : Prop := ∃ b, x ≡ y.moveRight b

@[inherit_doc] scoped infix:50 " ∈ₗ " => PGame.memₗ
@[inherit_doc] scoped infix:50 " ∈ᵣ " => PGame.memᵣ
@[inherit_doc PGame.memₗ] binder_predicate x " ∈ₗ " y:term => `($x ∈ₗ $y)
@[inherit_doc PGame.memᵣ] binder_predicate x " ∈ᵣ " y:term => `($x ∈ᵣ $y)

theorem memₗ_def {x y : PGame} : x ∈ₗ y ↔ ∃ b, x ≡ y.moveLeft b := .rfl
theorem memᵣ_def {x y : PGame} : x ∈ᵣ y ↔ ∃ b, x ≡ y.moveRight b := .rfl
theorem moveLeft_memₗ (x : PGame) (b) : x.moveLeft b ∈ₗ x := ⟨_, .rfl⟩
theorem moveRight_memᵣ (x : PGame) (b) : x.moveRight b ∈ᵣ x := ⟨_, .rfl⟩

theorem identical_of_isEmpty (x y : PGame)
    [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves]
    [IsEmpty y.LeftMoves] [IsEmpty y.RightMoves] : x ≡ y :=
  identical_iff.2 (by simp [biTotal_empty])

/-- `Identical` as a `Setoid`. -/
def identicalSetoid : Setoid PGame :=
  ⟨Identical, Identical.refl, Identical.symm, Identical.trans⟩

instance : IsRefl PGame (· ≡ ·) := ⟨Identical.refl⟩
instance : IsSymm PGame (· ≡ ·) := ⟨fun _ _ ↦ Identical.symm⟩
instance : IsTrans PGame (· ≡ ·) := ⟨fun _ _ _ ↦ Identical.trans⟩
instance : IsEquiv PGame (· ≡ ·) := { }

/-- If `x` and `y` are identical, then a left move of `x` is identical to some left move of `y`. -/
lemma Identical.moveLeft : ∀ {x y}, x ≡ y →
    ∀ i, ∃ j, x.moveLeft i ≡ y.moveLeft j
  | mk _ _ _ _, mk _ _ _ _, ⟨hl, _⟩, i => hl.1 i

/-- If `x` and `y` are identical, then a right move of `x` is identical to some right move of `y`.
-/
lemma Identical.moveRight : ∀ {x y}, x ≡ y →
    ∀ i, ∃ j, x.moveRight i ≡ y.moveRight j
  | mk _ _ _ _, mk _ _ _ _, ⟨_, hr⟩, i => hr.1 i

theorem identical_of_eq {x y : PGame} (h : x = y) : x ≡ y := by subst h; rfl

/-- Uses `∈ₗ` and `∈ᵣ` instead of `≡`. -/
theorem identical_iff' : ∀ {x y : PGame}, x ≡ y ↔
    ((∀ i, x.moveLeft i ∈ₗ y) ∧ (∀ j, y.moveLeft j ∈ₗ x)) ∧
      ((∀ i, x.moveRight i ∈ᵣ y) ∧ (∀ j, y.moveRight j ∈ᵣ x))
  | mk xl xr xL xR, mk yl yr yL yR => by
    convert identical_iff <;>
    dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal] <;>
    congr! <;>
    exact exists_congr <| fun _ ↦ identical_comm

theorem memₗ.congr_right : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, w ∈ₗ x ↔ w ∈ₗ y)
  | mk _ _ _ _, mk _ _ _ _, ⟨⟨h₁, h₂⟩, _⟩, _w =>
    ⟨fun ⟨i, hi⟩ ↦ (h₁ i).imp (fun _ ↦ hi.trans),
      fun ⟨j, hj⟩ ↦ (h₂ j).imp (fun _ hi ↦ hj.trans hi.symm)⟩

theorem memᵣ.congr_right : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, w ∈ᵣ x ↔ w ∈ᵣ y)
  | mk _ _ _ _, mk _ _ _ _, ⟨_, ⟨h₁, h₂⟩⟩, _w =>
    ⟨fun ⟨i, hi⟩ ↦ (h₁ i).imp (fun _ ↦ hi.trans),
      fun ⟨j, hj⟩ ↦ (h₂ j).imp (fun _ hi ↦ hj.trans hi.symm)⟩

theorem memₗ.congr_left : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, x ∈ₗ w ↔ y ∈ₗ w)
  | _, _, h, mk _ _ _ _ => ⟨fun ⟨i, hi⟩ ↦ ⟨i, h.symm.trans hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, h.trans hi⟩⟩

theorem memᵣ.congr_left : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, x ∈ᵣ w ↔ y ∈ᵣ w)
  | _, _, h, mk _ _ _ _ => ⟨fun ⟨i, hi⟩ ↦ ⟨i, h.symm.trans hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, h.trans hi⟩⟩

lemma Identical.ext : ∀ {x y}, (∀ z, z ∈ₗ x ↔ z ∈ₗ y) → (∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) → x ≡ y
  | mk _ _ _ _, mk _ _ _ _, hl, hr => identical_iff'.mpr
    ⟨⟨fun i ↦ (hl _).mp ⟨i, refl _⟩, fun j ↦ (hl _).mpr ⟨j, refl _⟩⟩,
      ⟨fun i ↦ (hr _).mp ⟨i, refl _⟩, fun j ↦ (hr _).mpr ⟨j, refl _⟩⟩⟩

lemma Identical.ext_iff {x y} : x ≡ y ↔ (∀ z, z ∈ₗ x ↔ z ∈ₗ y) ∧ (∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) :=
  ⟨fun h ↦ ⟨@memₗ.congr_right _ _ h, @memᵣ.congr_right _ _ h⟩, fun h ↦ h.elim Identical.ext⟩

lemma Identical.congr_right {x y z} (h : x ≡ y) : z ≡ x ↔ z ≡ y :=
  ⟨fun hz ↦ hz.trans h, fun hz ↦ hz.trans h.symm⟩

lemma Identical.congr_left {x y z} (h : x ≡ y) : x ≡ z ↔ y ≡ z :=
  ⟨fun hz ↦ h.symm.trans hz, fun hz ↦ h.trans hz⟩

/-- Show `x ≡ y` by giving an explicit correspondence between the moves of `x` and `y`. -/
lemma Identical.of_fn {x y : PGame}
    (l : x.LeftMoves → y.LeftMoves) (il : y.LeftMoves → x.LeftMoves)
    (r : x.RightMoves → y.RightMoves) (ir : y.RightMoves → x.RightMoves)
    (hl : ∀ i, x.moveLeft i ≡ y.moveLeft (l i))
    (hil : ∀ i, x.moveLeft (il i) ≡ y.moveLeft i)
    (hr : ∀ i, x.moveRight i ≡ y.moveRight (r i))
    (hir : ∀ i, x.moveRight (ir i) ≡ y.moveRight i) : x ≡ y :=
  identical_iff.mpr
    ⟨⟨fun i ↦ ⟨l i, hl i⟩, fun i ↦ ⟨il i, hil i⟩⟩, ⟨fun i ↦ ⟨r i, hr i⟩, fun i ↦ ⟨ir i, hir i⟩⟩⟩

lemma Identical.of_equiv {x y : PGame}
    (l : x.LeftMoves ≃ y.LeftMoves) (r : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i, x.moveLeft i ≡ y.moveLeft (l i)) (hr : ∀ i, x.moveRight i ≡ y.moveRight (r i)) :
    x ≡ y :=
  .of_fn l l.symm r r.symm hl (by simpa using hl <| l.symm ·) hr (by simpa using hr <| r.symm ·)

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

@[inherit_doc]
scoped infixl:50 " ≡r " => PGame.Relabelling

namespace Relabelling

variable {x y : PGame.{u}}

/-- A constructor for relabellings swapping the equivalences. -/
def mk' (L : y.LeftMoves ≃ x.LeftMoves) (R : y.RightMoves ≃ x.RightMoves)
    (hL : ∀ i, x.moveLeft (L i) ≡r y.moveLeft i) (hR : ∀ j, x.moveRight (R j) ≡r y.moveRight j) :
    x ≡r y :=
  ⟨L.symm, R.symm, fun i => by simpa using hL (L.symm i), fun j => by simpa using hR (R.symm j)⟩

/-- The equivalence between left moves of `x` and `y` given by the relabelling. -/
def leftMovesEquiv : x ≡r y → x.LeftMoves ≃ y.LeftMoves
  | ⟨L,_, _,_⟩ => L

@[simp]
theorem mk_leftMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).leftMovesEquiv = L :=
  rfl

@[simp]
theorem mk'_leftMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).leftMovesEquiv = L.symm :=
  rfl

/-- The equivalence between right moves of `x` and `y` given by the relabelling. -/
def rightMovesEquiv : x ≡r y → x.RightMoves ≃ y.RightMoves
  | ⟨_, R, _, _⟩ => R

@[simp]
theorem mk_rightMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).rightMovesEquiv = R :=
  rfl

@[simp]
theorem mk'_rightMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).rightMovesEquiv = R.symm :=
  rfl

/-- A left move of `x` is a relabelling of a left move of `y`. -/
def moveLeft : ∀ (r : x ≡r y) (i : x.LeftMoves), x.moveLeft i ≡r y.moveLeft (r.leftMovesEquiv i)
  | ⟨_, _, hL, _⟩ => hL

/-- A left move of `y` is a relabelling of a left move of `x`. -/
def moveLeftSymm :
    ∀ (r : x ≡r y) (i : y.LeftMoves), x.moveLeft (r.leftMovesEquiv.symm i) ≡r y.moveLeft i
  | ⟨L, R, hL, hR⟩, i => by simpa using hL (L.symm i)

/-- A right move of `x` is a relabelling of a right move of `y`. -/
def moveRight :
    ∀ (r : x ≡r y) (i : x.RightMoves), x.moveRight i ≡r y.moveRight (r.rightMovesEquiv i)
  | ⟨_, _, _, hR⟩ => hR

/-- A right move of `y` is a relabelling of a right move of `x`. -/
def moveRightSymm :
    ∀ (r : x ≡r y) (i : y.RightMoves), x.moveRight (r.rightMovesEquiv.symm i) ≡r y.moveRight i
  | ⟨L, R, hL, hR⟩, i => by simpa using hR (R.symm i)

/-- The identity relabelling. -/
@[refl]
def refl (x : PGame) : x ≡r x :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ => refl _, fun _ => refl _⟩
termination_by x

instance (x : PGame) : Inhabited (x ≡r x) :=
  ⟨refl _⟩

/-- Flip a relabelling. -/
@[symm]
def symm : ∀ {x y : PGame}, x ≡r y → y ≡r x
  | _, _, ⟨L, R, hL, hR⟩ => mk' L R (fun i => (hL i).symm) fun j => (hR j).symm

/-- Transitivity of relabelling. -/
@[trans]
def trans : ∀ {x y z : PGame}, x ≡r y → y ≡r z → x ≡r z
  | _, _, _, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ j).trans (hR₂ _)⟩

/-- Any game without left or right moves is a relabelling of 0. -/
def isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equiv.equivPEmpty _, Equiv.equivOfIsEmpty _ _, isEmptyElim, isEmptyElim⟩

end Relabelling

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) : PGame :=
  ⟨xl', xr', x.moveLeft ∘ el, x.moveRight ∘ er⟩

@[simp]
theorem relabel_moveLeft' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : xl') : moveLeft (relabel el er) i = x.moveLeft (el i) :=
  rfl

theorem relabel_moveLeft {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : x.LeftMoves) : moveLeft (relabel el er) (el.symm i) = x.moveLeft i := by simp

@[simp]
theorem relabel_moveRight' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : xr') : moveRight (relabel el er) j = x.moveRight (er j) :=
  rfl

theorem relabel_moveRight {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : x.RightMoves) : moveRight (relabel el er) (er.symm j) = x.moveRight j := by simp

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabelRelabelling {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) :
    x ≡r relabel el er :=
  -- Porting note: needed to add `rfl`
  Relabelling.mk' el er (fun i => by simp; rfl) (fun j => by simp; rfl)

/-! ### Inserting an option -/

/-- The pregame constructed by inserting `x'` as a new left option into x. -/
def insertLeft (x x' : PGame.{u}) : PGame :=
  match x with
  | mk xl xr xL xR => mk (xl ⊕ PUnit) xr (Sum.elim xL fun _ => x') xR

/-- The pregame constructed by inserting `x'` as a new right option into x. -/
def insertRight (x x' : PGame.{u}) : PGame :=
  match x with
  | mk xl xr xL xR => mk xl (xr ⊕ PUnit) xL (Sum.elim xR fun _ => x')

/-- Inserting on the left and right commutes. -/
theorem insertRight_insertLeft {x x' x'' : PGame} :
    insertRight (insertLeft x x') x'' = insertLeft (insertRight x x'') x' := by
  cases x; cases x'; cases x''
  dsimp [insertLeft, insertRight]

end SetTheory.PGame
