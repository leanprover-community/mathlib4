/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Logic.Relation
import Mathlib.Logic.Small.Defs
import Mathlib.Order.GameAdd

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

We may denote a game as $\{L | R\}$, where $L$ and $R$ stand for the collections of left and right
moves. This notation is not currently used in Mathlib.

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
    (hL : ∀ i j, HEq i j → x.moveLeft i = y.moveLeft j)
    (hR : ∀ i j, HEq i j → x.moveRight i = y.moveRight j) :
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

/-! ### Pre-game order relations -/


/-- The less or equal relation on pre-games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`.
See `PGame.le_iff_sub_nonneg`. -/
instance le : LE PGame :=
  ⟨Sym2.GameAdd.fix wf_isOption fun x y le =>
      (∀ i, ¬le y (x.moveLeft i) (Sym2.GameAdd.snd_fst <| IsOption.moveLeft i)) ∧
        ∀ j, ¬le (y.moveRight j) x (Sym2.GameAdd.fst_snd <| IsOption.moveRight j)⟩

/-- The less or fuzzy relation on pre-games. `x ⧏ y` is defined as `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`.
See `PGame.lf_iff_sub_zero_lf`. -/
def LF (x y : PGame) : Prop :=
  ¬y ≤ x

@[inherit_doc]
scoped infixl:50 " ⧏ " => PGame.LF

@[simp]
protected theorem not_le {x y : PGame} : ¬x ≤ y ↔ y ⧏ x :=
  Iff.rfl

@[simp]
theorem not_lf {x y : PGame} : ¬x ⧏ y ↔ y ≤ x :=
  Classical.not_not

theorem _root_.LE.le.not_gf {x y : PGame} : x ≤ y → ¬y ⧏ x :=
  not_lf.2

theorem LF.not_ge {x y : PGame} : x ⧏ y → ¬y ≤ x :=
  id

/-- Definition of `x ≤ y` on pre-games, in terms of `⧏`.

The ordering here is chosen so that `And.left` refer to moves by Left, and `And.right` refer to
moves by Right. -/
theorem le_iff_forall_lf {x y : PGame} :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by
  unfold LE.le le
  simp only
  rw [Sym2.GameAdd.fix_eq]
  rfl

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ≤ mk yl yr yL yR ↔ (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
  le_iff_forall_lf

theorem le_of_forall_lf {x y : PGame} (h₁ : ∀ i, x.moveLeft i ⧏ y) (h₂ : ∀ j, x ⧏ y.moveRight j) :
    x ≤ y :=
  le_iff_forall_lf.2 ⟨h₁, h₂⟩

/-- Definition of `x ⧏ y` on pre-games, in terms of `≤`.

The ordering here is chosen so that `or.inl` refer to moves by Left, and `or.inr` refer to
moves by Right. -/
theorem lf_iff_exists_le {x y : PGame} :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [LF, le_iff_forall_lf, not_and_or]
  simp

/-- Definition of `x ⧏ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ⧏ mk yl yr yL yR ↔ (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
  lf_iff_exists_le

theorem le_or_gf (x y : PGame) : x ≤ y ∨ y ⧏ x := by
  rw [← PGame.not_le]
  apply em

theorem moveLeft_lf_of_le {x y : PGame} (h : x ≤ y) (i) : x.moveLeft i ⧏ y :=
  (le_iff_forall_lf.1 h).1 i

alias _root_.LE.le.moveLeft_lf := moveLeft_lf_of_le

theorem lf_moveRight_of_le {x y : PGame} (h : x ≤ y) (j) : x ⧏ y.moveRight j :=
  (le_iff_forall_lf.1 h).2 j

alias _root_.LE.le.lf_moveRight := lf_moveRight_of_le

theorem lf_of_moveRight_le {x y : PGame} {j} (h : x.moveRight j ≤ y) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨j, h⟩

theorem lf_of_le_moveLeft {x y : PGame} {i} (h : x ≤ y.moveLeft i) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨i, h⟩

theorem lf_of_le_mk {xl xr xL xR y} : mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
  moveLeft_lf_of_le

theorem lf_of_mk_le {x yl yr yL yR} : x ≤ mk yl yr yL yR → ∀ j, x ⧏ yR j :=
  lf_moveRight_of_le

theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → PGame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
  @lf_of_moveRight_le (mk _ _ _ _) y j

theorem lf_mk_of_le {x yl yr} {yL : yl → PGame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
  @lf_of_le_moveLeft x (mk _ _ _ _) i

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
      induction x with | mk _ _ _ _ IHl IHr => _
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

lemma Identical.le : ∀ {x y}, x ≡ y → x ≤ y
  | mk _ _ _ _, mk _ _ _ _, ⟨hL, hR⟩ => le_of_forall_lf
    (fun i ↦ let ⟨_, hj⟩ := hL.1 i; lf_of_le_moveLeft hj.le)
    (fun i ↦ let ⟨_, hj⟩ := hR.2 i; lf_of_moveRight_le hj.le)

lemma Identical.ge {x y} (h : x ≡ y) : y ≤ x := h.symm.le

theorem lt_iff_le_and_lf {x y : PGame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
  Iff.rfl

theorem lt_of_le_of_lf {x y : PGame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
  ⟨h₁, h₂⟩

theorem lf_of_lt {x y : PGame} (h : x < y) : x ⧏ y :=
  h.2

alias _root_.LT.lt.lf := lf_of_lt

theorem lf_irrefl (x : PGame) : ¬x ⧏ x :=
  le_rfl.not_gf

instance : IsIrrefl _ (· ⧏ ·) :=
  ⟨lf_irrefl⟩

protected theorem not_lt {x y : PGame} : ¬ x < y ↔ y ⧏ x ∨ y ≤ x := not_lt_iff_not_le_or_ge

@[trans]
theorem lf_of_le_of_lf {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₂ ⊢
  exact fun h₃ => h₂ (h₃.trans h₁)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): added instance
instance : Trans (· ≤ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_le_of_lf⟩

@[trans]
theorem lf_of_lf_of_le {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₁ ⊢
  exact fun h₃ => h₁ (h₂.trans h₃)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): added instance
instance : Trans (· ⧏ ·) (· ≤ ·) (· ⧏ ·) := ⟨lf_of_lf_of_le⟩

alias _root_.LE.le.trans_lf := lf_of_le_of_lf

alias LF.trans_le := lf_of_lf_of_le

@[trans]
theorem lf_of_lt_of_lf {x y z : PGame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
  h₁.le.trans_lf h₂

@[trans]
theorem lf_of_lf_of_lt {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
  h₁.trans_le h₂.le

alias _root_.LT.lt.trans_lf := lf_of_lt_of_lf

alias LF.trans_lt := lf_of_lf_of_lt

theorem moveLeft_lf {x : PGame} : ∀ i, x.moveLeft i ⧏ x :=
  le_rfl.moveLeft_lf

theorem lf_moveRight {x : PGame} : ∀ j, x ⧏ x.moveRight j :=
  le_rfl.lf_moveRight

theorem lf_mk {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i) : xL i ⧏ mk xl xr xL xR :=
  @moveLeft_lf (mk _ _ _ _) i

theorem mk_lf {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j) : mk xl xr xL xR ⧏ xR j :=
  @lf_moveRight (mk _ _ _ _) j

/-- This special case of `PGame.le_of_forall_lf` is useful when dealing with surreals, where `<` is
preferred over `⧏`. -/
theorem le_of_forall_lt {x y : PGame} (h₁ : ∀ i, x.moveLeft i < y) (h₂ : ∀ j, x < y.moveRight j) :
    x ≤ y :=
  le_of_forall_lf (fun i => (h₁ i).lf) fun i => (h₂ i).lf

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later.

Note that it's often more convenient to use `le_iff_forall_lf`, which only unfolds the definition by
one step. -/
theorem le_def {x y : PGame} :
    x ≤ y ↔
      (∀ i, (∃ i', x.moveLeft i ≤ y.moveLeft i') ∨ ∃ j, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j, (∃ i, x ≤ (y.moveRight j).moveLeft i) ∨ ∃ j', x.moveRight j' ≤ y.moveRight j := by
  rw [le_iff_forall_lf]
  conv =>
    lhs
    simp only [lf_iff_exists_le]

/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later.

Note that it's often more convenient to use `lf_iff_exists_le`, which only unfolds the definition by
one step. -/
theorem lf_def {x y : PGame} :
    x ⧏ y ↔
      (∃ i, (∀ i', x.moveLeft i' ⧏ y.moveLeft i) ∧ ∀ j, x ⧏ (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i ⧏ y) ∧ ∀ j', x.moveRight j ⧏ y.moveRight j' := by
  rw [lf_iff_exists_le]
  conv =>
    lhs
    simp only [le_iff_forall_lf]

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem zero_le_lf {x : PGame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.moveRight j := by
  rw [le_iff_forall_lf]
  simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem le_zero_lf {x : PGame} : x ≤ 0 ↔ ∀ i, x.moveLeft i ⧏ 0 := by
  rw [le_iff_forall_lf]
  simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem zero_lf_le {x : PGame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.moveLeft i := by
  rw [lf_iff_exists_le]
  simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem lf_zero_le {x : PGame} : x ⧏ 0 ↔ ∃ j, x.moveRight j ≤ 0 := by
  rw [lf_iff_exists_le]
  simp

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : PGame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_def]
  simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : PGame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_def]
  simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ⧏` two moves later. -/
theorem zero_lf {x : PGame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.moveLeft i).moveRight j := by
  rw [lf_def]
  simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `⧏ 0` two moves later. -/
theorem lf_zero {x : PGame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.moveRight j).moveLeft i ⧏ 0 := by
  rw [lf_def]
  simp

@[simp]
theorem zero_le_of_isEmpty_rightMoves (x : PGame) [IsEmpty x.RightMoves] : 0 ≤ x :=
  zero_le.2 isEmptyElim

@[simp]
theorem le_zero_of_isEmpty_leftMoves (x : PGame) [IsEmpty x.LeftMoves] : x ≤ 0 :=
  le_zero.2 isEmptyElim

/-- Given a game won by the right player when they play second, provide a response to any move by
left. -/
noncomputable def rightResponse {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).RightMoves :=
  Classical.choose <| (le_zero.1 h) i

/-- Show that the response for right provided by `rightResponse` preserves the right-player-wins
condition. -/
theorem rightResponse_spec {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (rightResponse h i) ≤ 0 :=
  Classical.choose_spec <| (le_zero.1 h) i

/-- Given a game won by the left player when they play second, provide a response to any move by
right. -/
noncomputable def leftResponse {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    (x.moveRight j).LeftMoves :=
  Classical.choose <| (zero_le.1 h) j

/-- Show that the response for left provided by `leftResponse` preserves the left-player-wins
condition. -/
theorem leftResponse_spec {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (leftResponse h j) :=
  Classical.choose_spec <| (zero_le.1 h) j

/-- A small family of pre-games is bounded above. -/
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddAbove (Set.range f) := by
  let x : PGame.{u} := ⟨Σ i, (f <| (equivShrink.{u} ι).symm i).LeftMoves, PEmpty,
    fun x ↦ moveLeft _ x.2, PEmpty.elim⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @moveLeft_lf x ⟨equivShrink ι i, j⟩

/-- A small set of pre-games is bounded above. -/
lemma bddAbove_of_small (s : Set PGame.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → PGame.{u})

/-- A small family of pre-games is bounded below. -/
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddBelow (Set.range f) := by
  let x : PGame.{u} := ⟨PEmpty, Σ i, (f <| (equivShrink.{u} ι).symm i).RightMoves, PEmpty.elim,
    fun x ↦ moveRight _ x.2⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @lf_moveRight x ⟨equivShrink ι i, j⟩

/-- A small set of pre-games is bounded below. -/
lemma bddBelow_of_small (s : Set PGame.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → PGame.{u})

/-- The equivalence relation on pre-games. Two pre-games `x`, `y` are equivalent if `x ≤ y` and
`y ≤ x`.

If `x ≈ 0`, then the second player can always win `x`. -/
def Equiv (x y : PGame) : Prop :=
  x ≤ y ∧ y ≤ x

-- Porting note: deleted the scoped notation due to notation overloading with the setoid
-- instance and this causes the PGame.equiv docstring to not show up on hover.

instance : IsEquiv _ PGame.Equiv where
  refl _ := ⟨le_rfl, le_rfl⟩
  trans := fun _ _ _ ⟨xy, yx⟩ ⟨yz, zy⟩ => ⟨xy.trans yz, zy.trans yx⟩
  symm _ _ := And.symm

-- Porting note: moved the setoid instance from Basic.lean to here

instance setoid : Setoid PGame :=
  ⟨Equiv, refl, symm, Trans.trans⟩

theorem equiv_def {x y : PGame} : x ≈ y ↔ x ≤ y ∧ y ≤ x := Iff.rfl

theorem Equiv.le {x y : PGame} (h : x ≈ y) : x ≤ y :=
  h.1

theorem Equiv.ge {x y : PGame} (h : x ≈ y) : y ≤ x :=
  h.2

@[refl, simp]
theorem equiv_rfl {x : PGame} : x ≈ x :=
  refl x

theorem equiv_refl (x : PGame) : x ≈ x :=
  refl x

@[symm]
protected theorem Equiv.symm {x y : PGame} : (x ≈ y) → (y ≈ x) :=
  symm

@[trans]
protected theorem Equiv.trans {x y z : PGame} : (x ≈ y) → (y ≈ z) → (x ≈ z) :=
  _root_.trans

protected theorem equiv_comm {x y : PGame} : (x ≈ y) ↔ (y ≈ x) :=
  comm

theorem equiv_of_eq {x y : PGame} (h : x = y) : x ≈ y := by subst h; rfl

lemma Identical.equiv {x y} (h : x ≡ y) : x ≈ y := ⟨h.le, h.ge⟩

@[trans]
theorem le_of_le_of_equiv {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  h₁.trans h₂.1

instance : Trans
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_le_of_equiv

@[trans]
theorem le_of_equiv_of_le {x y z : PGame} (h₁ : x ≈ y) : y ≤ z → x ≤ z :=
  h₁.1.trans

instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_equiv_of_le

theorem LF.not_equiv {x y : PGame} (h : x ⧏ y) : ¬(x ≈ y) := fun h' => h.not_ge h'.2

theorem LF.not_equiv' {x y : PGame} (h : x ⧏ y) : ¬(y ≈ x) := fun h' => h.not_ge h'.1

theorem LF.not_gt {x y : PGame} (h : x ⧏ y) : ¬y < x := fun h' => h.not_ge h'.le

theorem le_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
  hx.2.trans (h.trans hy.1)

theorem le_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
  ⟨le_congr_imp hx hy, le_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩

theorem le_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
  le_congr hx equiv_rfl

theorem le_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
  le_congr equiv_rfl hy

theorem lf_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
  PGame.not_le.symm.trans <| (not_congr (le_congr hy hx)).trans PGame.not_le

theorem lf_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
  (lf_congr hx hy).1

theorem lf_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
  lf_congr hx equiv_rfl

theorem lf_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
  lf_congr equiv_rfl hy

@[trans]
theorem lf_of_lf_of_equiv {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
  lf_congr_imp equiv_rfl h₂ h₁

instance : Trans (· ⧏ ·) (· ≈ ·) (· ⧏ ·) := ⟨lf_of_lf_of_equiv⟩

@[trans]
theorem lf_of_equiv_of_lf {x y z : PGame} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  lf_congr_imp (Equiv.symm h₁) equiv_rfl

instance : Trans (· ≈ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_equiv_of_lf⟩

@[trans]
theorem lt_of_lt_of_equiv {x y z : PGame} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1

instance : Trans
    ((· < ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_lt_of_equiv

@[trans]
theorem lt_of_equiv_of_lt {x y z : PGame} (h₁ : x ≈ y) : y < z → x < z :=
  h₁.1.trans_lt

instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_equiv_of_lt

theorem lt_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
  hx.2.trans_lt (h.trans_le hy.1)

theorem lt_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  ⟨lt_congr_imp hx hy, lt_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩

theorem lt_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
  lt_congr hx equiv_rfl

theorem lt_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
  lt_congr equiv_rfl hy

theorem lt_or_equiv_of_le {x y : PGame} (h : x ≤ y) : x < y ∨ (x ≈ y) :=
  and_or_left.mp ⟨h, (em <| y ≤ x).symm.imp_left PGame.not_le.1⟩

theorem lf_or_equiv_or_gf (x y : PGame) : x ⧏ y ∨ (x ≈ y) ∨ y ⧏ x := by
  by_cases h : x ⧏ y
  · exact Or.inl h
  · right
    cases' lt_or_equiv_of_le (PGame.not_lf.1 h) with h' h'
    · exact Or.inr h'.lf
    · exact Or.inl (Equiv.symm h')

theorem equiv_congr_left {y₁ y₂ : PGame} : (y₁ ≈ y₂) ↔ ∀ x₁, (x₁ ≈ y₁) ↔ (x₁ ≈ y₂) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans h' h, fun h' => Equiv.trans h' (Equiv.symm h)⟩,
   fun h => (h y₁).1 <| equiv_rfl⟩

theorem equiv_congr_right {x₁ x₂ : PGame} : (x₁ ≈ x₂) ↔ ∀ y₁, (x₁ ≈ y₁) ↔ (x₂ ≈ y₁) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans (Equiv.symm h) h', fun h' => Equiv.trans h h'⟩,
   fun h => (h x₂).2 <| equiv_rfl⟩

theorem Equiv.of_exists {x y : PGame}
    (hl₁ : ∀ i, ∃ j, x.moveLeft i ≈ y.moveLeft j) (hr₁ : ∀ i, ∃ j, x.moveRight i ≈ y.moveRight j)
    (hl₂ : ∀ j, ∃ i, x.moveLeft i ≈ y.moveLeft j) (hr₂ : ∀ j, ∃ i, x.moveRight i ≈ y.moveRight j) :
    x ≈ y := by
  constructor <;> refine le_def.2 ⟨?_, ?_⟩ <;> intro i
  · obtain ⟨j, hj⟩ := hl₁ i
    exact Or.inl ⟨j, Equiv.le hj⟩
  · obtain ⟨j, hj⟩ := hr₂ i
    exact Or.inr ⟨j, Equiv.le hj⟩
  · obtain ⟨j, hj⟩ := hl₂ i
    exact Or.inl ⟨j, Equiv.ge hj⟩
  · obtain ⟨j, hj⟩ := hr₁ i
    exact Or.inr ⟨j, Equiv.ge hj⟩

theorem Equiv.of_equiv {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j, x.moveRight j ≈ y.moveRight (R j)) : x ≈ y := by
  apply Equiv.of_exists <;> intro i
  exacts [⟨_, hl i⟩, ⟨_, hr i⟩,
    ⟨_, by simpa using hl (L.symm i)⟩, ⟨_, by simpa using hr (R.symm i)⟩]

@[deprecated (since := "2024-09-26")] alias equiv_of_mk_equiv := Equiv.of_equiv

/-- The fuzzy, confused, or incomparable relation on pre-games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy (x y : PGame) : Prop :=
  x ⧏ y ∧ y ⧏ x

@[inherit_doc]
scoped infixl:50 " ‖ " => PGame.Fuzzy

@[symm]
theorem Fuzzy.swap {x y : PGame} : x ‖ y → y ‖ x :=
  And.symm

instance : IsSymm _ (· ‖ ·) :=
  ⟨fun _ _ => Fuzzy.swap⟩

theorem Fuzzy.swap_iff {x y : PGame} : x ‖ y ↔ y ‖ x :=
  ⟨Fuzzy.swap, Fuzzy.swap⟩

theorem fuzzy_irrefl (x : PGame) : ¬x ‖ x := fun h => lf_irrefl x h.1

instance : IsIrrefl _ (· ‖ ·) :=
  ⟨fuzzy_irrefl⟩

theorem lf_iff_lt_or_fuzzy {x y : PGame} : x ⧏ y ↔ x < y ∨ x ‖ y := by
  simp only [lt_iff_le_and_lf, Fuzzy, ← PGame.not_le]
  tauto

theorem lf_of_fuzzy {x y : PGame} (h : x ‖ y) : x ⧏ y :=
  lf_iff_lt_or_fuzzy.2 (Or.inr h)

alias Fuzzy.lf := lf_of_fuzzy

theorem lt_or_fuzzy_of_lf {x y : PGame} : x ⧏ y → x < y ∨ x ‖ y :=
  lf_iff_lt_or_fuzzy.1

theorem Fuzzy.not_equiv {x y : PGame} (h : x ‖ y) : ¬(x ≈ y) := fun h' => h'.1.not_gf h.2

theorem Fuzzy.not_equiv' {x y : PGame} (h : x ‖ y) : ¬(y ≈ x) := fun h' => h'.2.not_gf h.2

theorem not_fuzzy_of_le {x y : PGame} (h : x ≤ y) : ¬x ‖ y := fun h' => h'.2.not_ge h

theorem not_fuzzy_of_ge {x y : PGame} (h : y ≤ x) : ¬x ‖ y := fun h' => h'.1.not_ge h

theorem Equiv.not_fuzzy {x y : PGame} (h : x ≈ y) : ¬x ‖ y :=
  not_fuzzy_of_le h.1

theorem Equiv.not_fuzzy' {x y : PGame} (h : x ≈ y) : ¬y ‖ x :=
  not_fuzzy_of_le h.2

theorem fuzzy_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ ↔ x₂ ‖ y₂ :=
  show _ ∧ _ ↔ _ ∧ _ by rw [lf_congr hx hy, lf_congr hy hx]

theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ → x₂ ‖ y₂ :=
  (fuzzy_congr hx hy).1

theorem fuzzy_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ‖ y ↔ x₂ ‖ y :=
  fuzzy_congr hx equiv_rfl

theorem fuzzy_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ‖ y₁ ↔ x ‖ y₂ :=
  fuzzy_congr equiv_rfl hy

@[trans]
theorem fuzzy_of_fuzzy_of_equiv {x y z : PGame} (h₁ : x ‖ y) (h₂ : y ≈ z) : x ‖ z :=
  (fuzzy_congr_right h₂).1 h₁

@[trans]
theorem fuzzy_of_equiv_of_fuzzy {x y z : PGame} (h₁ : x ≈ y) (h₂ : y ‖ z) : x ‖ z :=
  (fuzzy_congr_left h₁).2 h₂

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

theorem lt_or_equiv_or_gf (x y : PGame) : x < y ∨ (x ≈ y) ∨ y ⧏ x := by
  rw [lf_iff_lt_or_fuzzy, Fuzzy.swap_iff]
  exact lt_or_equiv_or_gt_or_fuzzy x y

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

theorem le {x y : PGame} (r : x ≡r y) : x ≤ y :=
  le_def.2
    ⟨fun i => Or.inl ⟨_, (r.moveLeft i).le⟩, fun j =>
      Or.inr ⟨_, (r.moveRightSymm j).le⟩⟩
termination_by x

theorem ge {x y : PGame} (r : x ≡r y) : y ≤ x :=
  r.symm.le

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.ge⟩

/-- Transitivity of relabelling. -/
@[trans]
def trans : ∀ {x y z : PGame}, x ≡r y → y ≡r z → x ≡r z
  | _, _, _, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ j).trans (hR₂ _)⟩

/-- Any game without left or right moves is a relabelling of 0. -/
def isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equiv.equivPEmpty _, Equiv.equivOfIsEmpty _ _, isEmptyElim, isEmptyElim⟩

end Relabelling

theorem Equiv.isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≈ 0 :=
  (Relabelling.isEmpty x).equiv

instance {x y : PGame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩

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

/-! ### Negation -/


/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : PGame → PGame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩

instance : Neg PGame :=
  ⟨neg⟩

@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (-xR ·) (-xL ·) :=
  rfl

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

theorem isOption_neg {x y : PGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  rw [isOption_iff, isOption_iff, or_comm]
  cases y
  apply or_congr <;>
    · apply exists_congr
      intro
      rw [neg_eq_iff_eq_neg]
      rfl

@[simp]
theorem isOption_neg_neg {x y : PGame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]

/-- Use `toLeftMovesNeg` to cast between these two types. -/
theorem leftMoves_neg : ∀ x : PGame, (-x).LeftMoves = x.RightMoves
  | ⟨_, _, _, _⟩ => rfl

/-- Use `toRightMovesNeg` to cast between these two types. -/
theorem rightMoves_neg : ∀ x : PGame, (-x).RightMoves = x.LeftMoves
  | ⟨_, _, _, _⟩ => rfl

/-- Turns a right move for `x` into a left move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesNeg {x : PGame} : x.RightMoves ≃ (-x).LeftMoves :=
  Equiv.cast (leftMoves_neg x).symm

/-- Turns a left move for `x` into a right move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesNeg {x : PGame} : x.LeftMoves ≃ (-x).RightMoves :=
  Equiv.cast (rightMoves_neg x).symm

@[simp]
theorem moveLeft_neg {x : PGame} (i) :
    (-x).moveLeft i = -x.moveRight (toLeftMovesNeg.symm i) := by
  cases x
  rfl

@[deprecated moveLeft_neg (since := "2024-10-30")]
alias moveLeft_neg' := moveLeft_neg

theorem moveLeft_neg_toLeftMovesNeg {x : PGame} (i) :
    (-x).moveLeft (toLeftMovesNeg i) = -x.moveRight i := by simp

@[simp]
theorem moveRight_neg {x : PGame} (i) :
    (-x).moveRight i = -x.moveLeft (toRightMovesNeg.symm i) := by
  cases x
  rfl

@[deprecated moveRight_neg (since := "2024-10-30")]
alias moveRight_neg' := moveRight_neg

theorem moveRight_neg_toRightMovesNeg {x : PGame} (i) :
    (-x).moveRight (toRightMovesNeg i) = -x.moveLeft i := by simp

@[deprecated moveRight_neg (since := "2024-10-30")]
theorem moveLeft_neg_symm {x : PGame} (i) :
    x.moveLeft (toRightMovesNeg.symm i) = -(-x).moveRight i := by simp

@[deprecated moveRight_neg (since := "2024-10-30")]
theorem moveLeft_neg_symm' {x : PGame} (i) :
    x.moveLeft i = -(-x).moveRight (toRightMovesNeg i) := by simp

@[deprecated moveLeft_neg (since := "2024-10-30")]
theorem moveRight_neg_symm {x : PGame} (i) :
    x.moveRight (toLeftMovesNeg.symm i) = -(-x).moveLeft i := by simp

@[deprecated moveLeft_neg (since := "2024-10-30")]
theorem moveRight_neg_symm' {x : PGame} (i) :
    x.moveRight i = -(-x).moveLeft (toLeftMovesNeg i) := by simp

@[simp]
theorem forall_leftMoves_neg {x : PGame} {p : (-x).LeftMoves → Prop} :
    (∀ i : (-x).LeftMoves, p i) ↔ (∀ i : x.RightMoves, p (toLeftMovesNeg i)) :=
  toLeftMovesNeg.forall_congr_right.symm

@[simp]
theorem exists_leftMoves_neg {x : PGame} {p : (-x).LeftMoves → Prop} :
    (∃ i : (-x).LeftMoves, p i) ↔ (∃ i : x.RightMoves, p (toLeftMovesNeg i)) :=
  toLeftMovesNeg.exists_congr_right.symm

@[simp]
theorem forall_rightMoves_neg {x : PGame} {p : (-x).RightMoves → Prop} :
    (∀ i : (-x).RightMoves, p i) ↔ (∀ i : x.LeftMoves, p (toRightMovesNeg i)) :=
  toRightMovesNeg.forall_congr_right.symm

@[simp]
theorem exists_rightMoves_neg {x : PGame} {p : (-x).RightMoves → Prop} :
    (∃ i : (-x).RightMoves, p i) ↔ (∃ i : x.LeftMoves, p (toRightMovesNeg i)) :=
  toRightMovesNeg.exists_congr_right.symm

theorem leftMoves_neg_cases {x : PGame} (k) {P : (-x).LeftMoves → Prop}
    (h : ∀ i, P <| toLeftMovesNeg i) :
    P k := by
  rw [← toLeftMovesNeg.apply_symm_apply k]
  exact h _

theorem rightMoves_neg_cases {x : PGame} (k) {P : (-x).RightMoves → Prop}
    (h : ∀ i, P <| toRightMovesNeg i) :
    P k := by
  rw [← toRightMovesNeg.apply_symm_apply k]
  exact h _

/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
lemma Identical.neg : ∀ {x₁ x₂ : PGame}, x₁ ≡ x₂ → -x₁ ≡ -x₂
  | mk _ _ _ _, mk _ _ _ _, ⟨⟨hL₁, hL₂⟩, ⟨hR₁, hR₂⟩⟩ =>
    ⟨⟨fun i ↦ (hR₁ i).imp (fun _ ↦ Identical.neg), fun j ↦ (hR₂ j).imp (fun _ ↦ Identical.neg)⟩,
      ⟨fun i ↦ (hL₁ i).imp (fun _ ↦ Identical.neg), fun j ↦ (hL₂ j).imp (fun _ ↦ Identical.neg)⟩⟩

/-- If `-x` has the same moves as `-y`, then `x` has the sames moves as `y`. -/
lemma Identical.of_neg : ∀ {x₁ x₂ : PGame}, -x₁ ≡ -x₂ → x₁ ≡ x₂
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R => by
    simpa using Identical.neg (x₁ := mk _ _ (-x₁R ·) (-x₁L ·)) (x₂ := mk _ _ (-x₂R ·) (-x₂L ·))

lemma memₗ_neg_iff : ∀ {x y : PGame},
    x ∈ₗ -y ↔ ∃ z ∈ᵣ y, x ≡ -z
  | mk _ _ _ _, mk _ _ _ _ =>
    ⟨fun ⟨_i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.neg⟩⟩

lemma memᵣ_neg_iff : ∀ {x y : PGame},
    x ∈ᵣ -y ↔ ∃ z ∈ₗ y, x ≡ -z
  | mk _ _ _ _, mk _ _ _ _ =>
    ⟨fun ⟨_i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.neg⟩⟩

/-- If `x` has the same moves as `y`, then `-x` has the same moves as `-y`. -/
def Relabelling.negCongr : ∀ {x y : PGame}, x ≡r y → -x ≡r -y
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun j => (hR j).negCongr, fun i => (hL i).negCongr⟩

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

@[simp]
theorem neg_lf_neg_iff {x y : PGame} : -y ⧏ -x ↔ x ⧏ y :=
  neg_le_lf_neg_iff.2

@[simp]
theorem neg_lt_neg_iff {x y : PGame} : -y < -x ↔ x < y := by
  rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]

@[simp]
theorem neg_identical_neg {x y : PGame} : -x ≡ -y ↔ x ≡ y :=
  ⟨Identical.of_neg, Identical.neg⟩

@[simp]
theorem neg_equiv_neg_iff {x y : PGame} : -x ≈ -y ↔ x ≈ y := by
  show Equiv (-x) (-y) ↔ Equiv x y
  rw [Equiv, Equiv, neg_le_neg_iff, neg_le_neg_iff, and_comm]

@[simp]
theorem neg_fuzzy_neg_iff {x y : PGame} : -x ‖ -y ↔ x ‖ y := by
  rw [Fuzzy, Fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and_comm]

theorem neg_le_iff {x y : PGame} : -y ≤ x ↔ -x ≤ y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]

theorem neg_lf_iff {x y : PGame} : -y ⧏ x ↔ -x ⧏ y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]

theorem neg_lt_iff {x y : PGame} : -y < x ↔ -x < y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]

theorem neg_equiv_iff {x y : PGame} : (-x ≈ y) ↔ (x ≈ -y) := by
  rw [← neg_neg y, neg_equiv_neg_iff, neg_neg]

theorem neg_fuzzy_iff {x y : PGame} : -x ‖ y ↔ x ‖ -y := by
  rw [← neg_neg y, neg_fuzzy_neg_iff, neg_neg]

theorem le_neg_iff {x y : PGame} : y ≤ -x ↔ x ≤ -y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]

theorem lf_neg_iff {x y : PGame} : y ⧏ -x ↔ x ⧏ -y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]

theorem lt_neg_iff {x y : PGame} : y < -x ↔ x < -y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]

@[simp]
theorem neg_le_zero_iff {x : PGame} : -x ≤ 0 ↔ 0 ≤ x := by rw [neg_le_iff, neg_zero]

@[simp]
theorem zero_le_neg_iff {x : PGame} : 0 ≤ -x ↔ x ≤ 0 := by rw [le_neg_iff, neg_zero]

@[simp]
theorem neg_lf_zero_iff {x : PGame} : -x ⧏ 0 ↔ 0 ⧏ x := by rw [neg_lf_iff, neg_zero]

@[simp]
theorem zero_lf_neg_iff {x : PGame} : 0 ⧏ -x ↔ x ⧏ 0 := by rw [lf_neg_iff, neg_zero]

@[simp]
theorem neg_lt_zero_iff {x : PGame} : -x < 0 ↔ 0 < x := by rw [neg_lt_iff, neg_zero]

@[simp]
theorem zero_lt_neg_iff {x : PGame} : 0 < -x ↔ x < 0 := by rw [lt_neg_iff, neg_zero]

@[simp]
theorem neg_equiv_zero_iff {x : PGame} : (-x ≈ 0) ↔ (x ≈ 0) := by rw [neg_equiv_iff, neg_zero]

@[simp]
theorem neg_fuzzy_zero_iff {x : PGame} : -x ‖ 0 ↔ x ‖ 0 := by rw [neg_fuzzy_iff, neg_zero]

@[simp]
theorem zero_equiv_neg_iff {x : PGame} : (0 ≈ -x) ↔ (0 ≈ x) := by rw [← neg_equiv_iff, neg_zero]

@[simp]
theorem zero_fuzzy_neg_iff {x : PGame} : 0 ‖ -x ↔ 0 ‖ x := by rw [← neg_fuzzy_iff, neg_zero]

/-! ### Addition and subtraction -/

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add PGame.{u} :=
  ⟨fun x y => by
    induction x generalizing y with | mk xl xr _ _ IHxl IHxr => _
    induction y with | mk yl yr yL yR IHyl IHyr => _
    have y := mk yl yr yL yR
    refine ⟨xl ⊕ yl, xr ⊕ yr, Sum.rec ?_ ?_, Sum.rec ?_ ?_⟩
    · exact fun i => IHxl i y
    · exact IHyl
    · exact fun i => IHxr i y
    · exact IHyr⟩

theorem mk_add_moveLeft {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft i =
      i.rec (xL · + mk yl yr yL yR) (mk xl xr xL xR + yL ·) :=
  rfl

theorem mk_add_moveRight {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight i =
      i.rec (xR · + mk yl yr yL yR) (mk xl xr xL xR + yR ·) :=
  rfl

/-- The pre-game `((0 + 1) + ⋯) + 1`.

Note that this is **not** the usual recursive definition `n = {0, 1, … | }`. For instance,
`2 = 0 + 1 + 1 = {0 + 0 + 1, 0 + 1 + 0 | }` does not contain any left option equivalent to `0`. For
an implementation of said definition, see `Ordinal.toPGame`. For the proof that these games are
equivalent, see `Ordinal.toPGame_natCast`. -/
instance : NatCast PGame :=
  ⟨Nat.unaryCast⟩

@[simp]
protected theorem nat_succ (n : ℕ) : ((n + 1 : ℕ) : PGame) = n + 1 :=
  rfl

instance isEmpty_leftMoves_add (x y : PGame.{u}) [IsEmpty x.LeftMoves] [IsEmpty y.LeftMoves] :
    IsEmpty (x + y).LeftMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'

instance isEmpty_rightMoves_add (x y : PGame.{u}) [IsEmpty x.RightMoves] [IsEmpty y.RightMoves] :
    IsEmpty (x + y).RightMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'

/-- `x + 0` has exactly the same moves as `x`. -/
def addZeroRelabelling : ∀ x : PGame.{u}, x + 0 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.sumEmpty xl PEmpty, Equiv.sumEmpty xr PEmpty, ?_, ?_⟩ <;> rintro (⟨i⟩ | ⟨⟨⟩⟩) <;>
      apply addZeroRelabelling
termination_by x => x

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : PGame.{u}) : x + 0 ≈ x :=
  (addZeroRelabelling x).equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zeroAddRelabelling : ∀ x : PGame.{u}, 0 + x ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.emptySum PEmpty xl, Equiv.emptySum PEmpty xr, ?_, ?_⟩ <;> rintro (⟨⟨⟩⟩ | ⟨i⟩) <;>
      apply zeroAddRelabelling

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : PGame.{u}) : 0 + x ≈ x :=
  (zeroAddRelabelling x).equiv

/-- Use `toLeftMovesAdd` to cast between these two types. -/
theorem leftMoves_add : ∀ x y : PGame.{u}, (x + y).LeftMoves = (x.LeftMoves ⊕ y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Use `toRightMovesAdd` to cast between these two types. -/
theorem rightMoves_add : ∀ x y : PGame.{u}, (x + y).RightMoves = (x.RightMoves ⊕ y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesAdd {x y : PGame} : x.LeftMoves ⊕ y.LeftMoves ≃ (x + y).LeftMoves :=
  Equiv.cast (leftMoves_add x y).symm

/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesAdd {x y : PGame} : x.RightMoves ⊕ y.RightMoves ≃ (x + y).RightMoves :=
  Equiv.cast (rightMoves_add x y).symm

@[simp]
theorem mk_add_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inl i) =
      (mk xl xr xL xR).moveLeft i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_moveLeft_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inl i)) = x.moveLeft i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inl i) =
      (mk xl xr xL xR).moveRight i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_moveRight_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inl i)) = x.moveRight i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveLeft i :=
  rfl

@[simp]
theorem add_moveLeft_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inr i)) = x + y.moveLeft i := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveRight i :=
  rfl

@[simp]
theorem add_moveRight_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inr i)) = x + y.moveRight i := by
  cases x
  cases y
  rfl

/-- Case on possible left moves of `x + y`. -/
theorem leftMoves_add_cases {x y : PGame} (k) {P : (x + y).LeftMoves → Prop}
    (hl : ∀ i, P <| toLeftMovesAdd (Sum.inl i)) (hr : ∀ i, P <| toLeftMovesAdd (Sum.inr i)) :
    P k := by
  rw [← toLeftMovesAdd.apply_symm_apply k]
  cases' toLeftMovesAdd.symm k with i i
  · exact hl i
  · exact hr i

/-- Case on possible right moves of `x + y`. -/
theorem rightMoves_add_cases {x y : PGame} (k) {P : (x + y).RightMoves → Prop}
    (hl : ∀ j, P <| toRightMovesAdd (Sum.inl j)) (hr : ∀ j, P <| toRightMovesAdd (Sum.inr j)) :
    P k := by
  rw [← toRightMovesAdd.apply_symm_apply k]
  cases' toRightMovesAdd.symm k with i i
  · exact hl i
  · exact hr i

instance isEmpty_nat_rightMoves : ∀ n : ℕ, IsEmpty (RightMoves n)
  | 0 => inferInstanceAs (IsEmpty PEmpty)
  | n + 1 => by
    haveI := isEmpty_nat_rightMoves n
    rw [PGame.nat_succ, rightMoves_add]
    infer_instance

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

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
protected lemma neg_add (x y : PGame) : -(x + y) = -x + -y :=
  match x, y with
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ext rfl rfl ?_ ?_ <;>
    · rintro (i | i) _ ⟨rfl⟩
      · exact PGame.neg_add _ _
      · simpa [Equiv.refl, mk_add_moveLeft, mk_add_moveRight] using PGame.neg_add _ _
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
      exact identical_of_isEmpty _ _

/-- Any game without left or right moves is identical to 0. -/
lemma identical_zero (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡ 0 :=
  x.identical_zero_iff.mpr ⟨by infer_instance, by infer_instance⟩

protected lemma add_eq_zero : ∀ {x y : PGame}, x + y ≡ 0 ↔ x ≡ 0 ∧ y ≡ 0
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [identical_zero_iff, leftMoves_add, rightMoves_add, isEmpty_sum]
    tauto

lemma Identical.add_right {x₁ x₂ y} : x₁ ≡ x₂ → x₁ + y ≡ x₂ + y :=
  match x₁, x₂, y with
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => by
    intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rintro (_ | _) <;> try exact ⟨.inr _, h.add_right⟩
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

lemma memₗ_add_iff {x y₁ y₂ : PGame} :
    x ∈ₗ y₁ + y₂ ↔ (∃ z ∈ₗ y₁, x ≡ z + y₂) ∨ (∃ z ∈ₗ y₂, x ≡ y₁ + z) := by
  cases' y₁ with y₁l y₁r y₁L y₁R
  cases' y₂ with y₂l y₂r y₂L y₂R
  constructor
  · rintro ⟨(i | i), hi⟩
    exacts [.inl ⟨y₁L i, moveLeft_memₗ _ _, hi⟩, .inr ⟨y₂L i, moveLeft_memₗ _ _, hi⟩]
  · rintro (⟨_, ⟨i, hi⟩, h⟩ | ⟨_, ⟨i, hi⟩, h⟩)
    exacts [⟨.inl i, h.trans hi.add_right⟩, ⟨.inr i, h.trans hi.add_left⟩]

lemma memᵣ_add_iff {x y₁ y₂ : PGame} :
    x ∈ᵣ y₁ + y₂ ↔ (∃ z ∈ᵣ y₁, x ≡ z + y₂) ∨ (∃ z ∈ᵣ y₂, x ≡ y₁ + z) := by
  cases' y₁ with y₁l y₁r y₁L y₁R
  cases' y₂ with y₂l y₂r y₂L y₂R
  constructor
  · rintro ⟨(i | i), hi⟩
    exacts [.inl ⟨y₁R i, moveRight_memᵣ _ _, hi⟩, .inr ⟨y₂R i, moveRight_memᵣ _ _, hi⟩]
  · rintro (⟨_, ⟨i, hi⟩, h⟩ | ⟨_, ⟨i, hi⟩, h⟩)
    exacts [⟨.inl i, h.trans hi.add_right⟩, ⟨.inr i, h.trans hi.add_left⟩]

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

instance : Sub PGame :=
  ⟨fun x y => x + -y⟩

@[simp]
theorem sub_zero_eq_add_zero (x : PGame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by rw [neg_zero]

protected lemma sub_zero (x : PGame) : x - 0 ≡ x :=
  _root_.trans (of_eq x.sub_zero_eq_add_zero) x.add_zero

/-- This lemma is named to match `neg_sub'`. -/
protected lemma neg_sub' (x y : PGame) : -(x - y) = -x - -y := PGame.neg_add _ _

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
lemma Identical.sub {x₁ x₂ y₁ y₂ : PGame.{u}} (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) : x₁ - y₁ ≡ x₂ - y₂ :=
  hx.add hy.neg

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def Relabelling.subCongr {w x y z : PGame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def negAddRelabelling : ∀ x y : PGame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.refl _, Equiv.refl _, ?_, ?_⟩
    all_goals
      exact fun j =>
        Sum.casesOn j (fun j => negAddRelabelling _ _) fun j =>
          negAddRelabelling ⟨xl, xr, xL, xR⟩ _
termination_by x y => (x, y)

theorem neg_add_le {x y : PGame} : -(x + y) ≤ -x + -y :=
  (negAddRelabelling x y).le

/-- `x + y` has exactly the same moves as `y + x`. -/
def addCommRelabelling : ∀ x y : PGame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;> rintro (_ | _) <;>
      · dsimp
        apply addCommRelabelling
termination_by x y => (x, y)

theorem add_comm_le {x y : PGame} : x + y ≤ y + x :=
  (addCommRelabelling x y).le

theorem add_comm_equiv {x y : PGame} : x + y ≈ y + x :=
  (addCommRelabelling x y).equiv

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

theorem add_assoc_equiv {x y z : PGame} : x + y + z ≈ x + (y + z) :=
  (addAssocRelabelling x y z).equiv

theorem neg_add_cancel_le_zero : ∀ x : PGame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ =>
    le_zero.2 fun i => by
      cases' i with i i
      · -- If Left played in -x, Right responds with the same move in x.
        refine ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), ?_⟩
        convert @neg_add_cancel_le_zero (xR i)
        apply add_moveRight_inr
      · -- If Left in x, Right responds with the same move in -x.
        dsimp
        refine ⟨@toRightMovesAdd ⟨_, _, _, _⟩ _ (Sum.inl i), ?_⟩
        convert @neg_add_cancel_le_zero (xL i)
        apply add_moveRight_inl

theorem zero_le_neg_add_cancel (x : PGame) : 0 ≤ -x + x := by
  rw [← neg_le_neg_iff, neg_zero]
  exact neg_add_le.trans (neg_add_cancel_le_zero _)

theorem neg_add_cancel_equiv (x : PGame) : -x + x ≈ 0 :=
  ⟨neg_add_cancel_le_zero x, zero_le_neg_add_cancel x⟩

theorem add_neg_cancel_le_zero (x : PGame) : x + -x ≤ 0 :=
  add_comm_le.trans (neg_add_cancel_le_zero x)

theorem zero_le_add_neg_cancel (x : PGame) : 0 ≤ x + -x :=
  (zero_le_neg_add_cancel x).trans add_comm_le

theorem add_neg_cancel_equiv (x : PGame) : x + -x ≈ 0 :=
  ⟨add_neg_cancel_le_zero x, zero_le_add_neg_cancel x⟩

theorem sub_self_equiv : ∀ (x : PGame), x - x ≈ 0 :=
  add_neg_cancel_equiv

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

instance addRightMono : AddRightMono PGame :=
  ⟨fun _ _ _ => add_le_add_right'⟩

instance addLeftMono : AddLeftMono PGame :=
  ⟨fun x _ _ h => (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩

theorem add_lf_add_right {y z : PGame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
  suffices z + x ≤ y + x → z ≤ y by
    rw [← PGame.not_le] at h ⊢
    exact mt this h
  fun w =>
  calc
    z ≤ z + 0 := (addZeroRelabelling _).symm.le
    _ ≤ z + (x + -x) := add_le_add_left (zero_le_add_neg_cancel x) _
    _ ≤ z + x + -x := (addAssocRelabelling _ _ _).symm.le
    _ ≤ y + x + -x := add_le_add_right w _
    _ ≤ y + (x + -x) := (addAssocRelabelling _ _ _).le
    _ ≤ y + 0 := add_le_add_left (add_neg_cancel_le_zero x) _
    _ ≤ y := (addZeroRelabelling _).le

theorem add_lf_add_left {y z : PGame} (h : y ⧏ z) (x) : x + y ⧏ x + z := by
  rw [lf_congr add_comm_equiv add_comm_equiv]
  apply add_lf_add_right h

instance addRightStrictMono : AddRightStrictMono PGame :=
  ⟨fun x _ _ h => ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩⟩

instance addLeftStrictMono : AddLeftStrictMono PGame :=
  ⟨fun x _ _ h => ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩⟩

theorem add_lf_add_of_lf_of_le {w x y z : PGame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
  lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)

theorem add_lf_add_of_le_of_lf {w x y z : PGame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
  lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)

theorem add_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
  ⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
    (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩

theorem add_congr_left {x y z : PGame} (h : x ≈ y) : x + z ≈ y + z :=
  add_congr h equiv_rfl

theorem add_congr_right {x y z : PGame} : (y ≈ z) → (x + y ≈ x + z) :=
  add_congr equiv_rfl

theorem sub_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
  add_congr h₁ (neg_equiv_neg_iff.2 h₂)

theorem sub_congr_left {x y z : PGame} (h : x ≈ y) : x - z ≈ y - z :=
  sub_congr h equiv_rfl

theorem sub_congr_right {x y z : PGame} : (y ≈ z) → (x - y ≈ x - z) :=
  sub_congr equiv_rfl

theorem le_iff_sub_nonneg {x y : PGame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => (zero_le_add_neg_cancel x).trans (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ≤ y - x + x := add_le_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

theorem lf_iff_sub_zero_lf {x y : PGame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h => (zero_le_add_neg_cancel x).trans_lf (add_lf_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ⧏ y - x + x := add_lf_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (zero_le_add_neg_cancel x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ < y - x + x := add_lt_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

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

/-! ### Removing an option -/

/-- The PGame constructed by removing `'x` as a left option from `x`. -/
def removeLeft (x : PGame.{u}) (i : x.LeftMoves) : PGame :=
  match x with
  | mk _ xr xL xR => mk { x // x ≠ i } xr (xL ·.val) xR

/-- One less left option will not empower Left. -/
theorem removeLeft_le (x : PGame) (i : x.LeftMoves) : x.removeLeft i ≤ x := by
  rw [le_def]
  constructor
  · intro i
    left
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [moveLeft_mk]
    constructor
    rfl
  · intro j
    right
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [moveRight_mk]
    use j
    rfl

/-- The PGame constructed by removing `'x` as a right option from `x`. -/
def removeRight (x : PGame.{u}) (i : x.RightMoves) : PGame :=
  match x with
  | mk xl _ xL xR => mk xl { x // x ≠ i } xL (xR ·.val)

theorem neg_removeRight_neg (x : PGame.{u}) (i : x.RightMoves) :
    (-x).removeLeft (toLeftMovesNeg i) = -x.removeRight i := by
  cases x
  dsimp [insertRight, insertLeft]
  congr! with (i | j)

/-- One less right option will not empower Right. -/
theorem removeRight_le (x : PGame) (i : x.RightMoves) : x ≤ x.removeRight i := by
  rw [← neg_le_neg_iff, ← neg_removeRight_neg]
  simp only [removeLeft_le]

/-! ### Special pre-games -/


/-- The pre-game `star`, which is fuzzy with zero. -/
def star : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => 0⟩

@[simp]
theorem star_leftMoves : star.LeftMoves = PUnit :=
  rfl

@[simp]
theorem star_rightMoves : star.RightMoves = PUnit :=
  rfl

@[simp]
theorem star_moveLeft (x) : star.moveLeft x = 0 :=
  rfl

@[simp]
theorem star_moveRight (x) : star.moveRight x = 0 :=
  rfl

instance uniqueStarLeftMoves : Unique star.LeftMoves :=
  PUnit.instUnique

instance uniqueStarRightMoves : Unique star.RightMoves :=
  PUnit.instUnique

theorem zero_lf_star : 0 ⧏ star := by
  rw [zero_lf]
  use default
  rintro ⟨⟩

theorem star_lf_zero : star ⧏ 0 := by
  rw [lf_zero]
  use default
  rintro ⟨⟩

theorem star_fuzzy_zero : star ‖ 0 :=
  ⟨star_lf_zero, zero_lf_star⟩

@[simp]
theorem neg_star : -star = star := by simp [star]

@[simp]
protected theorem zero_lt_one : (0 : PGame) < 1 :=
  lt_of_le_of_lf (zero_le_of_isEmpty_rightMoves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)

/-- The pre-game `up` -/
def up : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => star⟩

@[simp]
theorem up_leftMoves : up.LeftMoves = PUnit :=
  rfl

@[simp]
theorem up_rightMoves : up.RightMoves = PUnit :=
  rfl

@[simp]
theorem up_moveLeft (x) : up.moveLeft x = 0 :=
  rfl

@[simp]
theorem up_moveRight (x) : up.moveRight x = star :=
  rfl

@[simp]
theorem up_neg : 0 < up := by
  rw [lt_iff_le_and_lf, zero_lf]
  simp [zero_le_lf, zero_lf_star]

theorem star_fuzzy_up : star ‖ up := by
  unfold Fuzzy
  simp only [← PGame.not_le]
  simp [le_iff_forall_lf]

/-- The pre-game `down` -/
def down : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => star, fun _ => 0⟩

@[simp]
theorem down_leftMoves : down.LeftMoves = PUnit :=
  rfl

@[simp]
theorem down_rightMoves : down.RightMoves = PUnit :=
  rfl

@[simp]
theorem down_moveLeft (x) : down.moveLeft x = star :=
  rfl

@[simp]
theorem down_moveRight (x) : down.moveRight x = 0 :=
  rfl

@[simp]
theorem down_neg : down < 0 := by
  rw [lt_iff_le_and_lf, lf_zero]
  simp [le_zero_lf, star_lf_zero]

@[simp]
theorem neg_down : -down = up := by simp [up, down]

@[simp]
theorem neg_up : -up = down := by simp [up, down]

theorem star_fuzzy_down : star ‖ down := by
  rw [← neg_fuzzy_neg_iff, neg_down, neg_star]
  exact star_fuzzy_up

instance : ZeroLEOneClass PGame :=
  ⟨PGame.zero_lt_one.le⟩

@[simp]
theorem zero_lf_one : (0 : PGame) ⧏ 1 :=
  PGame.zero_lt_one.lf

end PGame

end SetTheory

set_option linter.style.longFile 2300
