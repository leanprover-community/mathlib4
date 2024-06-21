/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Violeta Hernández Palacios, Junyan Xu, Theodore Hwa
-/
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Logic.Hydra
import Mathlib.SetTheory.Game.Ordinal

#align_import set_theory.surreal.basic from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `Numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties

Surreal numbers inherit the relations `≤` and `<` from games (`Surreal.instLE` and
`Surreal.instLT`), and these relations satisfy the axioms of a partial order.

## Algebraic operations

We show that the surreals form a linear ordered commutative ring.

One can also map all the ordinals into the surreals!

### Todo

- Define the field structure on the surreals.

-/


universe u

namespace SetTheory

open scoped PGame

namespace PGame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def Numeric : PGame → Prop
  | ⟨_, _, L, R⟩ => (∀ i j, L i < R j) ∧ (∀ i, Numeric (L i)) ∧ ∀ j, Numeric (R j)
#align pgame.numeric SetTheory.PGame.Numeric

theorem numeric_def {x : PGame} :
    Numeric x ↔
      (∀ i j, x.moveLeft i < x.moveRight j) ∧
        (∀ i, Numeric (x.moveLeft i)) ∧ ∀ j, Numeric (x.moveRight j) := by
  cases x; rfl
#align pgame.numeric_def SetTheory.PGame.numeric_def

namespace Numeric

theorem mk {x : PGame} (h₁ : ∀ i j, x.moveLeft i < x.moveRight j) (h₂ : ∀ i, Numeric (x.moveLeft i))
    (h₃ : ∀ j, Numeric (x.moveRight j)) : Numeric x :=
  numeric_def.2 ⟨h₁, h₂, h₃⟩
#align pgame.numeric.mk SetTheory.PGame.Numeric.mk

theorem left_lt_right {x : PGame} (o : Numeric x) (i : x.LeftMoves) (j : x.RightMoves) :
    x.moveLeft i < x.moveRight j := by cases x; exact o.1 i j
#align pgame.numeric.left_lt_right SetTheory.PGame.Numeric.left_lt_right

theorem moveLeft {x : PGame} (o : Numeric x) (i : x.LeftMoves) : Numeric (x.moveLeft i) := by
  cases x; exact o.2.1 i
#align pgame.numeric.move_left SetTheory.PGame.Numeric.moveLeft

theorem moveRight {x : PGame} (o : Numeric x) (j : x.RightMoves) : Numeric (x.moveRight j) := by
  cases x; exact o.2.2 j
#align pgame.numeric.move_right SetTheory.PGame.Numeric.moveRight

end Numeric

@[elab_as_elim]
theorem numeric_rec {C : PGame → Prop}
    (H : ∀ (l r) (L : l → PGame) (R : r → PGame), (∀ i j, L i < R j) →
      (∀ i, Numeric (L i)) → (∀ i, Numeric (R i)) → (∀ i, C (L i)) → (∀ i, C (R i)) →
      C ⟨l, r, L, R⟩) :
    ∀ x, Numeric x → C x
  | ⟨_, _, _, _⟩, ⟨h, hl, hr⟩ =>
    H _ _ _ _ h hl hr (fun i => numeric_rec H _ (hl i)) fun i => numeric_rec H _ (hr i)
#align pgame.numeric_rec SetTheory.PGame.numeric_rec

theorem Relabelling.numeric_imp {x y : PGame} (r : x ≡r y) (ox : Numeric x) : Numeric y := by
  induction' x using PGame.moveRecOn with x IHl IHr generalizing y
  apply Numeric.mk (fun i j => ?_) (fun i => ?_) fun j => ?_
  · rw [← lt_congr (r.moveLeftSymm i).equiv (r.moveRightSymm j).equiv]
    apply ox.left_lt_right
  · exact IHl _ (r.moveLeftSymm i) (ox.moveLeft _)
  · exact IHr _ (r.moveRightSymm j) (ox.moveRight _)
#align pgame.relabelling.numeric_imp SetTheory.PGame.Relabelling.numeric_imp

/-- Relabellings preserve being numeric. -/
theorem Relabelling.numeric_congr {x y : PGame} (r : x ≡r y) : Numeric x ↔ Numeric y :=
  ⟨r.numeric_imp, r.symm.numeric_imp⟩
#align pgame.relabelling.numeric_congr SetTheory.PGame.Relabelling.numeric_congr

theorem lf_asymm {x y : PGame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y → ¬y ⧏ x := by
  refine numeric_rec (C := fun x => ∀ z (_oz : Numeric z), x ⧏ z → ¬z ⧏ x)
    (fun xl xr xL xR hx _oxl _oxr IHxl IHxr => ?_) x ox y oy
  refine numeric_rec fun yl yr yL yR hy oyl oyr _IHyl _IHyr => ?_
  rw [mk_lf_mk, mk_lf_mk]; rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩)
  · exact IHxl _ _ (oyl _) (h₁.moveLeft_lf _) (h₂.moveLeft_lf _)
  · exact (le_trans h₂ h₁).not_gf (lf_of_lt (hy _ _))
  · exact (le_trans h₁ h₂).not_gf (lf_of_lt (hx _ _))
  · exact IHxr _ _ (oyr _) (h₁.lf_moveRight _) (h₂.lf_moveRight _)
#align pgame.lf_asymm SetTheory.PGame.lf_asymm

theorem le_of_lf {x y : PGame} (h : x ⧏ y) (ox : Numeric x) (oy : Numeric y) : x ≤ y :=
  not_lf.1 (lf_asymm ox oy h)
#align pgame.le_of_lf SetTheory.PGame.le_of_lf

alias LF.le := le_of_lf
#align pgame.lf.le SetTheory.PGame.LF.le

theorem lt_of_lf {x y : PGame} (h : x ⧏ y) (ox : Numeric x) (oy : Numeric y) : x < y :=
  (lt_or_fuzzy_of_lf h).resolve_right (not_fuzzy_of_le (h.le ox oy))
#align pgame.lt_of_lf SetTheory.PGame.lt_of_lf

alias LF.lt := lt_of_lf
#align pgame.lf.lt SetTheory.PGame.LF.lt

theorem lf_iff_lt {x y : PGame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y ↔ x < y :=
  ⟨fun h => h.lt ox oy, lf_of_lt⟩
#align pgame.lf_iff_lt SetTheory.PGame.lf_iff_lt

/-- Definition of `x ≤ y` on numeric pre-games, in terms of `<` -/
theorem le_iff_forall_lt {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x ≤ y ↔ (∀ i, x.moveLeft i < y) ∧ ∀ j, x < y.moveRight j := by
  refine le_iff_forall_lf.trans (and_congr ?_ ?_) <;>
      refine forall_congr' fun i => lf_iff_lt ?_ ?_ <;>
    apply_rules [Numeric.moveLeft, Numeric.moveRight]
#align pgame.le_iff_forall_lt SetTheory.PGame.le_iff_forall_lt

/-- Definition of `x < y` on numeric pre-games, in terms of `≤` -/
theorem lt_iff_exists_le {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [← lf_iff_lt ox oy, lf_iff_exists_le]
#align pgame.lt_iff_exists_le SetTheory.PGame.lt_iff_exists_le

theorem lt_of_exists_le {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    ((∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y) → x < y :=
  (lt_iff_exists_le ox oy).2
#align pgame.lt_of_exists_le SetTheory.PGame.lt_of_exists_le

/-- The definition of `x < y` on numeric pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔
      (∃ i, (∀ i', x.moveLeft i' < y.moveLeft i) ∧ ∀ j, x < (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i < y) ∧ ∀ j', x.moveRight j < y.moveRight j' := by
  rw [← lf_iff_lt ox oy, lf_def]
  refine or_congr ?_ ?_ <;> refine exists_congr fun x_1 => ?_ <;> refine and_congr ?_ ?_ <;>
      refine forall_congr' fun i => lf_iff_lt ?_ ?_ <;>
    apply_rules [Numeric.moveLeft, Numeric.moveRight]
#align pgame.lt_def SetTheory.PGame.lt_def

theorem not_fuzzy {x y : PGame} (ox : Numeric x) (oy : Numeric y) : ¬Fuzzy x y :=
  fun h => not_lf.2 ((lf_of_fuzzy h).le ox oy) h.2
#align pgame.not_fuzzy SetTheory.PGame.not_fuzzy

theorem lt_or_equiv_or_gt {x y : PGame} (ox : Numeric x) (oy : Numeric y) :
    x < y ∨ (x ≈ y) ∨ y < x :=
  ((lf_or_equiv_or_gf x y).imp fun h => h.lt ox oy) <| Or.imp_right fun h => h.lt oy ox
#align pgame.lt_or_equiv_or_gt SetTheory.PGame.lt_or_equiv_or_gt

theorem numeric_of_isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : Numeric x :=
  Numeric.mk isEmptyElim isEmptyElim isEmptyElim
#align pgame.numeric_of_is_empty SetTheory.PGame.numeric_of_isEmpty

theorem numeric_of_isEmpty_leftMoves (x : PGame) [IsEmpty x.LeftMoves] :
    (∀ j, Numeric (x.moveRight j)) → Numeric x :=
  Numeric.mk isEmptyElim isEmptyElim
#align pgame.numeric_of_is_empty_left_moves SetTheory.PGame.numeric_of_isEmpty_leftMoves

theorem numeric_of_isEmpty_rightMoves (x : PGame) [IsEmpty x.RightMoves]
    (H : ∀ i, Numeric (x.moveLeft i)) : Numeric x :=
  Numeric.mk (fun _ => isEmptyElim) H isEmptyElim
#align pgame.numeric_of_is_empty_right_moves SetTheory.PGame.numeric_of_isEmpty_rightMoves

theorem numeric_zero : Numeric 0 :=
  numeric_of_isEmpty 0
#align pgame.numeric_zero SetTheory.PGame.numeric_zero

theorem numeric_one : Numeric 1 :=
  numeric_of_isEmpty_rightMoves 1 fun _ => numeric_zero
#align pgame.numeric_one SetTheory.PGame.numeric_one

theorem Numeric.neg : ∀ {x : PGame} (_ : Numeric x), Numeric (-x)
  | ⟨_, _, _, _⟩, o =>
    ⟨fun j i => neg_lt_neg_iff.2 (o.1 i j), fun j => (o.2.2 j).neg, fun i => (o.2.1 i).neg⟩
#align pgame.numeric.neg SetTheory.PGame.Numeric.neg

namespace Numeric

theorem moveLeft_lt {x : PGame} (o : Numeric x) (i) : x.moveLeft i < x :=
  (moveLeft_lf i).lt (o.moveLeft i) o
#align pgame.numeric.move_left_lt SetTheory.PGame.Numeric.moveLeft_lt

theorem moveLeft_le {x : PGame} (o : Numeric x) (i) : x.moveLeft i ≤ x :=
  (o.moveLeft_lt i).le
#align pgame.numeric.move_left_le SetTheory.PGame.Numeric.moveLeft_le

theorem lt_moveRight {x : PGame} (o : Numeric x) (j) : x < x.moveRight j :=
  (lf_moveRight j).lt o (o.moveRight j)
#align pgame.numeric.lt_move_right SetTheory.PGame.Numeric.lt_moveRight

theorem le_moveRight {x : PGame} (o : Numeric x) (j) : x ≤ x.moveRight j :=
  (o.lt_moveRight j).le
#align pgame.numeric.le_move_right SetTheory.PGame.Numeric.le_moveRight

theorem add : ∀ {x y : PGame} (_ : Numeric x) (_ : Numeric y), Numeric (x + y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ox, oy =>
    ⟨by
      rintro (ix | iy) (jx | jy)
      · exact add_lt_add_right (ox.1 ix jx) _
      · exact (add_lf_add_of_lf_of_le (lf_mk _ _ ix) (oy.le_moveRight jy)).lt
          ((ox.moveLeft ix).add oy) (ox.add (oy.moveRight jy))
      · exact (add_lf_add_of_lf_of_le (mk_lf _ _ jx) (oy.moveLeft_le iy)).lt
          (ox.add (oy.moveLeft iy)) ((ox.moveRight jx).add oy)
      · exact add_lt_add_left (oy.1 iy jy) ⟨xl, xr, xL, xR⟩, by
      constructor
      · rintro (ix | iy)
        · exact (ox.moveLeft ix).add oy
        · exact ox.add (oy.moveLeft iy)
      · rintro (jx | jy)
        · apply (ox.moveRight jx).add oy
        · apply ox.add (oy.moveRight jy)⟩
termination_by x y => (x, y) -- Porting note: Added `termination_by`
#align pgame.numeric.add SetTheory.PGame.Numeric.add

theorem sub {x y : PGame} (ox : Numeric x) (oy : Numeric y) : Numeric (x - y) :=
  ox.add oy.neg
#align pgame.numeric.sub SetTheory.PGame.Numeric.sub

end Numeric

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : ∀ n : ℕ, Numeric n
  | 0 => numeric_zero
  | n + 1 => (numeric_nat n).add numeric_one
#align pgame.numeric_nat SetTheory.PGame.numeric_nat

/-- Ordinal games are numeric. -/
theorem numeric_toPGame (o : Ordinal) : o.toPGame.Numeric := by
  induction' o using Ordinal.induction with o IH
  apply numeric_of_isEmpty_rightMoves
  simpa using fun i => IH _ (Ordinal.toLeftMovesToPGame_symm_lt i)
#align pgame.numeric_to_pgame SetTheory.PGame.numeric_toPGame

end PGame

end SetTheory

open SetTheory PGame

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotient (inferInstanceAs <| Setoid (Subtype Numeric))
#align surreal Surreal

namespace Surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : PGame) (h : x.Numeric) : Surreal :=
  ⟦⟨x, h⟩⟧
#align surreal.mk Surreal.mk

instance : Zero Surreal :=
  ⟨mk 0 numeric_zero⟩

instance : One Surreal :=
  ⟨mk 1 numeric_one⟩

instance : Inhabited Surreal :=
  ⟨0⟩

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, Numeric x → α)
    (H : ∀ {x y} (hx : Numeric x) (hy : Numeric y), x.Equiv y → f x hx = f y hy) : Surreal → α :=
  Quotient.lift (fun x : { x // Numeric x } => f x.1 x.2) fun x y => H x.2 y.2
#align surreal.lift Surreal.lift

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, Numeric x → Numeric y → α)
    (H :
      ∀ {x₁ y₁ x₂ y₂} (ox₁ : Numeric x₁) (oy₁ : Numeric y₁) (ox₂ : Numeric x₂) (oy₂ : Numeric y₂),
        x₁.Equiv x₂ → y₁.Equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) :
    Surreal → Surreal → α :=
  lift (fun x ox => lift (fun y oy => f x y ox oy) fun _ _ => H _ _ _ _ equiv_rfl)
    fun _ _ h => funext <| Quotient.ind fun _ => H _ _ _ _ h equiv_rfl
#align surreal.lift₂ Surreal.lift₂

instance instLE : LE Surreal :=
  ⟨lift₂ (fun x y _ _ => x ≤ y) fun _ _ _ _ hx hy => propext (le_congr hx hy)⟩
#align surreal.has_le Surreal.instLE

@[simp]
lemma mk_le_mk {x y : PGame.{u}} {hx hy} : mk x hx ≤ mk y hy ↔ x ≤ y := Iff.rfl

instance instLT : LT Surreal :=
  ⟨lift₂ (fun x y _ _ => x < y) fun _ _ _ _ hx hy => propext (lt_congr hx hy)⟩
#align surreal.has_lt Surreal.instLT

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Surreal :=
  ⟨Surreal.lift₂ (fun (x y : PGame) ox oy => ⟦⟨x + y, ox.add oy⟩⟧) fun _ _ _ _ hx hy =>
      Quotient.sound (add_congr hx hy)⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Surreal :=
  ⟨Surreal.lift (fun x ox => ⟦⟨-x, ox.neg⟩⟧) fun _ _ a => Quotient.sound (neg_equiv_neg_iff.2 a)⟩

instance orderedAddCommGroup : OrderedAddCommGroup Surreal where
  add := (· + ·)
  add_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound add_assoc_equiv
  zero := 0
  zero_add := by rintro ⟨a⟩; exact Quotient.sound (zero_add_equiv a)
  add_zero := by rintro ⟨a⟩; exact Quotient.sound (add_zero_equiv a)
  neg := Neg.neg
  add_left_neg := by rintro ⟨a⟩; exact Quotient.sound (add_left_neg_equiv a)
  add_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound add_comm_equiv
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_, ox⟩ ⟨_, oy⟩; apply @lt_iff_le_not_le PGame
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact @add_le_add_left PGame _ _ _ _ _ hx _
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  { Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩
      exact or_iff_not_imp_left.2 fun h => (PGame.not_le.1 h).le oy ox
    decidableLE := Classical.decRel _ }

instance : AddMonoidWithOne Surreal :=
  AddMonoidWithOne.unary

/-- Casts a `Surreal` number into a `Game`. -/
def toGame : Surreal →+o Game where
  toFun := lift (fun x _ => ⟦x⟧) fun _ _ => Quot.sound
  map_zero' := rfl
  map_add' := by rintro ⟨_, _⟩ ⟨_, _⟩; rfl
  monotone' := by rintro ⟨_, _⟩ ⟨_, _⟩; exact id
#align surreal.to_game Surreal.toGame

theorem zero_toGame : toGame 0 = 0 :=
  rfl
#align surreal.zero_to_game Surreal.zero_toGame

@[simp]
theorem one_toGame : toGame 1 = 1 :=
  rfl
#align surreal.one_to_game Surreal.one_toGame

@[simp]
theorem nat_toGame : ∀ n : ℕ, toGame n = n :=
  map_natCast' _ one_toGame
#align surreal.nat_to_game Surreal.nat_toGame

#noalign upper_bound_numeric
#noalign lower_bound_numeric

/-- A small family of surreals is bounded above. -/
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    BddAbove (Set.range f) := by
  induction' f using Quotient.induction_on_pi with f
  let g : ι → PGame.{u} := Subtype.val ∘ f
  have hg (i) : (g i).Numeric := Subtype.prop _
  conv in (⟦f _⟧) =>
    change mk (g i) (hg i)
  clear_value g
  clear f
  let x : PGame.{u} := ⟨Σ i, (g <| (equivShrink.{u} ι).symm i).LeftMoves, PEmpty,
    fun x ↦ moveLeft _ x.2, PEmpty.elim⟩
  refine ⟨mk x (.mk (by simp [x]) (fun _ ↦ (hg _).moveLeft _) (by simp [x])),
    Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [mk_le_mk, ← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @moveLeft_lf x ⟨equivShrink ι i, j⟩

/-- A small set of surreals is bounded above. -/
lemma bddAbove_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → Surreal.{u})
#align surreal.bdd_above_of_small Surreal.bddAbove_of_small

/-- A small family of surreals is bounded below. -/
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    BddBelow (Set.range f) := by
  induction' f using Quotient.induction_on_pi with f
  let g : ι → PGame.{u} := Subtype.val ∘ f
  have hg (i) : (g i).Numeric := Subtype.prop _
  conv in (⟦f _⟧) =>
    change mk (g i) (hg i)
  clear_value g
  clear f
  let x : PGame.{u} := ⟨PEmpty, Σ i, (g <| (equivShrink.{u} ι).symm i).RightMoves,
    PEmpty.elim, fun x ↦ moveRight _ x.2⟩
  refine ⟨mk x (.mk (by simp [x]) (by simp [x]) (fun _ ↦ (hg _).moveRight _) ),
    Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [mk_le_mk, ← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @lf_moveRight x ⟨equivShrink ι i, j⟩

/-- A small set of surreals is bounded below. -/
lemma bddBelow_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → Surreal.{u})
#align surreal.bdd_below_of_small Surreal.bddBelow_of_small

end Surreal

/-!
### Surreal multiplication

This section carries out the main inductive argument that proves the following three main theorems:
* P1: being numeric is closed under multiplication,
* P2: multiplying a numeric pregame by equivalent numeric pregames results in equivalent pregames,
* P3: the product of two positive numeric pregames is positive (`mul_pos`).

This is Theorem 8 in [Conway2001], or Theorem 3.8 in [SchleicherStoll]. P1 allows us to define
multiplication as an operation on numeric pregames, P2 says that this is well-defined as an
operation on the quotient by `PGame.Equiv`, namely the surreal numbers, and P3 is an axiom that
needs to be satisfied for the surreals to be a `OrderedRing`.

We follow the proof in [schleicher_stoll], except that we use the well-foundedness of
the hydra relation `CutExpand` on `Multiset PGame` instead of the argument based
on a depth function in the paper.

In the argument, P3 is stated with four variables `x₁`, `x₂`, `y₁`, `y₂` satisfying `x₁ < x₂` and
`y₁ < y₂`, and says that `x₁ * y₂ + x₂ * x₁ < x₁ * y₁ + x₂ * y₂`, which is equivalent to
`0 < x₂ - x₁ → 0 < y₂ - y₁ → 0 < (x₂ - x₁) * (y₂ - y₁)`, i.e.
`@mul_pos PGame _ (x₂ - x₁) (y₂ - y₁)`. It has to be stated in this form and not in terms of
`mul_pos` because we need to show show P1, P2 and (a specialized form of) P3 simultaneously, and
for example `P1 x y` will be deduced from P3 with variables taking values simpler than `x` or `y`
(among other induction hypotheses), but if you subtract two pregames simpler than `x` or `y`,
the result may no longer be simpler.

The specialized version of P3 is called P4, which takes only three arguments `x₁`, `x₂`, `y` and
requires that `y₂ = y` or `-y` and that `y₁` is a left option of `y₂`. After P1, P2 and P4 are
shown, a further inductive argument (this time using the `GameAdd` relation) proves P3 in full.

Our proof features a clear separation into components/submodules:
* calculation (e.g. ...),
* specialize induction hypothesis to a form easier to apply
  (that direct takes in `IsOption` arguments),
* application of specialized indution hypothesis,
* symmetry verification,
* verification of `CutExpand` relations,
* `Numeric`ity of options (filled in at the last moment ).
and we utilize symmetry (permutation and negation of arguments) to minimize calculation.

  strategy: extract specialized versions of the induction hypothesis that easier to apply
  (example: `ih1`, ...),
  show they are invariant under certain symmetries (permutation and negation of variables),
  and that the induction hypothesis indeed implies the specialized versions.
  (Actually the induction hypotheses themselves already have those symmetries ..? No, not usually
  the negation symmetries).

  add the numeric hypothesis only at the last moment ..

## References

* [Conway, *On numbers and games*][Conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][SchleicherStoll]

-/

open SetTheory
open Game
open PGame
open WellFounded

namespace SetTheory.PGame.Numeric

lemma isOption {x' x} (h : IsOption x' x) (hx : Numeric x) : Numeric x' := by
  cases h
  apply hx.moveLeft
  apply hx.moveRight

end SetTheory.PGame.Numeric

namespace Surreal.Multiplication

def P1 (x₁ x₂ x₃ y₁ y₂ y₃ : PGame) :=
  ⟦x₁ * y₁⟧ + ⟦x₂ * y₂⟧ - ⟦x₁ * y₂⟧ < ⟦x₃ * y₁⟧ + ⟦x₂ * y₃⟧ - (⟦x₃ * y₃⟧: Game)

/-- The proposition P2, without numeric assumptions. -/
def P2 (x₁ x₂ y : PGame) := x₁ ≈ x₂ → ⟦x₁ * y⟧ = (⟦x₂ * y⟧: Game)

/-- The proposition P3, without the `x₁ < x₂` and `y₁ < y₂` assumptions. -/
def P3 (x₁ x₂ y₁ y₂ : PGame) := ⟦x₁ * y₂⟧ + ⟦x₂ * y₁⟧ < ⟦x₁ * y₁⟧ + (⟦x₂ * y₂⟧: Game)

/-- The proposition P4, without numeric assumptions. In the references, the second part of the
  conjunction is stated as `∀ j, P3 x₁ x₂ y (y.moveRight j)`, which is equivalent to our statement
  by `P3_comm` and `P3_neg`. We choose to state everything in terms of left options for uniform
  treatment. -/
def P4 (x₁ x₂ y : PGame) :=
    x₁ < x₂ → (∀ i, P3 x₁ x₂ (y.moveLeft i) y) ∧ ∀ j, P3 x₁ x₂ ((-y).moveLeft j) (-y)

/-- The conjunction of P2 and P4. -/
def P24 (x₁ x₂ y : PGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' : PGame.{u}}

/-! #### Symmetry properties of P1, P2, P3, and P4 -/

lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by
  rw [P3, P3, add_comm]
  congr! 2 <;> rw [quot_mul_comm]

lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3] at h₁ h₂
  rw [P3, ← add_lt_add_iff_left (⟦x₂ * y₁⟧ + ⟦x₂ * y₂⟧)]
  convert add_lt_add h₁ h₂ using 1 <;> abel

lemma P3_neg : P3 x₁ x₂ y₁ y₂ ↔ P3 (-x₂) (-x₁) y₁ y₂ := by
  simp only [P3, quot_neg_mul]
  rw [← _root_.neg_lt_neg_iff]
  abel_nf

lemma P2_negx : P2 x₁ x₂ y ↔ P2 (-x₂) (-x₁) y := by
  rw [P2, P2]
  constructor
  · rw [quot_neg_mul, quot_neg_mul, eq_comm, neg_inj, neg_equiv_neg_iff, PGame.equiv_comm]
    exact fun a a_1 ↦ a a_1
  · rw [PGame.equiv_comm, neg_equiv_neg_iff, quot_neg_mul, quot_neg_mul, neg_inj]
    tauto

lemma P2_negy : P2 x₁ x₂ y ↔ P2 x₁ x₂ (-y) := by
  rw [P2, P2]
  rw [quot_mul_neg, quot_mul_neg, neg_inj]

lemma P4_negx : P4 x₁ x₂ y ↔ P4 (-x₂) (-x₁) y := by
  rw [P4, P4, PGame.neg_lt_neg_iff]
  simp [← P3_neg]

lemma P4_negy : P4 x₁ x₂ y ↔ P4 x₁ x₂ (-y) := by
  rw [P4, P4, neg_neg, and_comm]

lemma P24_negx : P24 x₁ x₂ y ↔ P24 (-x₂) (-x₁) y := by rw [P24, P24, P2_negx, P4_negx]
lemma P24_negy : P24 x₁ x₂ y ↔ P24 x₁ x₂ (-y) := by rw [P24, P24, P2_negy, P4_negy]


/-! #### Explicit calculations necessary for the main proof -/

lemma mul_option_lt_iff_P1 {i j k l} :
    (⟦mul_option x y i k⟧: Game) < -⟦mul_option x (-y) j l⟧ ↔
    P1 (x.moveLeft i) x (x.moveLeft j) y (y.moveLeft k) (-(-y).moveLeft l) := by
  dsimp [mul_option, P1]
  convert Iff.rfl using 2
  simp only [neg_sub', neg_add, quot_mul_neg, neg_neg]

lemma mul_option_lt_mul_iff_P3 {i j} :
    ⟦mul_option x y i j⟧ < (⟦x * y⟧: Game) ↔ P3 (x.moveLeft i) x (y.moveLeft j) y := by
  dsimp [mul_option]
  exact sub_lt_iff_lt_add'

lemma P1_of_eq (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 ⟦x₁ * y₁⟧ using 1 <;> abel

lemma P1_of_lt (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, sub_lt_sub_iff, ← add_lt_add_iff_left ⟦x₃ * y₂⟧]
  convert add_lt_add h₁ h₂ using 1 <;> abel

/-- The type of lists of arguments for P1, P2, and P4. -/
inductive Args : Type (u+1)
| P1 (x y : PGame.{u}) : Args
| P24 (x₁ x₂ y : PGame.{u}) : Args


/-- The multiset associated to a list of arguments. -/
def Args.toMultiset : Args → Multiset PGame
| (Args.P1 x y) => {x, y}
| (Args.P24 x₁ x₂ y) => {x₁, x₂, y}


/-- A list of arguments is numeric if all the arguments are. -/
def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, SetTheory.PGame.Numeric x


open Relation

/-- The relation specifying when a list of (pregame) arguments is considered simpler than another:
  `args_rel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by
  repeatedly removing a pregame from `a₂` and adding back one or two options of the pregame.  -/
def args_rel := InvImage (TransGen $ CutExpand IsOption) Args.toMultiset

/-- `args_rel` is well-founded. -/
--theorem args_rel_wf : well_founded args_rel := inv_image.wf _ wf_is_option.cut_expand.trans_gen
theorem args_rel_wf : WellFounded args_rel := InvImage.wf _ wf_isOption.cutExpand.transGen


/-- The statement that we will be shown by induction using the well-founded relation `args_rel`. -/
def P124 : Args → Prop
| (Args.P1 x y) => Numeric (x * y)
| (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y


/-- The property that all arguments are numeric is leftward-closed under `args_rel`. -/
lemma args_rel.numeric_closed {a' a} : args_rel a' a → a.Numeric → a'.Numeric := by
  exact TransGen.closed2 $ @cutExpand_closed _ IsOption ⟨wf_isOption.isIrrefl.1⟩ _ Numeric.isOption

/-- A specialized induction hypothesis used to prove P1. -/
def ih1 (x y: PGame) : Prop :=
    ∀ ⦃x₁ x₂ y'⦄, IsOption x₁ x → IsOption x₂ x → (y' = y ∨ IsOption y' y) → P24 x₁ x₂ y'

/-! #### Symmetry properties of `ih1` -/

lemma ih1_negx : ih1 x y → ih1 (-x) y :=
  fun h x₁ x₂ y' h₁ h₂ hy => by
    rw [isOption_neg] at h₁ h₂
    exact P24_negx.2 (h h₂ h₁ hy)

lemma ih1_negy : ih1 x y → ih1 x (-y) :=
  fun h x₁ x₂ y' => by
    rw [← neg_eq_iff_eq_neg, isOption_neg, P24_negy]
    apply h

/-! #### Specialize `ih` to obtain specialized induction hypotheses for P1 -/

variable (ih : ∀ a, args_rel a (Args.P1 x y) → P124 a)

lemma ihnx (h : IsOption x' x) : (x' * y).Numeric :=
  ih (Args.P1 x' y) $ TransGen.single $ cutExpand_pair_left h

lemma ihny (h : IsOption y' y) : (x * y').Numeric :=
  ih (Args.P1 x y') $ TransGen.single $ cutExpand_pair_right h

lemma ihnxy (hx : IsOption x' x) (hy : IsOption y' y) : (x' * y').Numeric :=
  ih (Args.P1 x' y') $ TransGen.tail (TransGen.single $ cutExpand_pair_right hy) $
    cutExpand_pair_left hx

lemma ih1xy : ih1 x y := by
  rintro x₁ x₂ y' h₁ h₂ (rfl|hy) <;> apply ih (Args.P24 _ _ _)
  swap
  refine TransGen.tail ?_ (cutExpand_pair_right hy)
  all_goals { exact TransGen.single (cutExpand_double_left h₁ h₂) }

lemma ih1yx : ih1 y x :=
  ih1xy $ by
    simp_rw [args_rel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih ⊢
    exact ih

lemma P3_of_ih (hy : Numeric y) (ihyx : ih1 y x) (i k l) :
    P3 (x.moveLeft i) x (y.moveLeft k) (-(-y).moveLeft l) :=
  P3_comm.2 $ ((ihyx (IsOption.moveLeft k) (isOption_neg.1 $ IsOption.moveLeft l) (Or.inl rfl)).2
    (by rw [← moveRight_neg_symm]; apply hy.left_lt_right)).1 i

lemma P24_of_ih (ihxy : ih1 x y) (i j) : P24 (x.moveLeft i) (x.moveLeft j) y :=
  ihxy (IsOption.moveLeft i) (IsOption.moveLeft j) (Or.inl rfl)

variable (hx : Numeric x) (hy : Numeric y)

section

variable (ihxy : ih1 x y) (ihyx : ih1 y x)

lemma mul_option_lt_of_lt (i j k l) (h : x.moveLeft i < x.moveLeft j) :
    (⟦mul_option x y i k⟧: Game) < -⟦mul_option x (-y) j l⟧ :=
  mul_option_lt_iff_P1.2 $ P1_of_lt (P3_of_ih hy ihyx j k l) $ ((P24_of_ih ihxy i j).2 h).1 k

lemma mul_option_lt (i j k l) : (⟦mul_option x y i k⟧: Game) < -⟦mul_option x (-y) j l⟧ := by
  obtain (h|h|h) := lt_or_equiv_or_gt (hx.moveLeft i) (hx.moveLeft j)
  { exact mul_option_lt_of_lt hy ihxy ihyx i j k l h }
  { have ml := @IsOption.moveLeft
    exact mul_option_lt_iff_P1.2 (P1_of_eq h (P24_of_ih ihxy i j).1
      (ihxy (ml i) (ml j) $ Or.inr $ isOption_neg.1 $ ml l).1 $ P3_of_ih hy ihyx i k l) }
  { rw [mul_option_neg_neg, lt_neg]
    exact mul_option_lt_of_lt hy.neg (ih1_negy ihxy) (ih1_negx ihyx) j i l _ h }

end

/-- P1 follows from the induction hypothesis. -/
theorem P1_of_ih : (x * y).Numeric := by
  have ihxy := ih1xy ih
  have ihyx := ih1yx ih
  have ihxyn := ih1_negx (ih1_negy ihxy)
  have ihyxn := ih1_negx (ih1_negy ihyx)
  refine numeric_def.mpr ⟨?_, ?_, ?_⟩

  · simp_rw [lt_iff_game_lt]
    intro i
    rw [rightMoves_mul_iff]
    constructor
    · intros j l
      revert i
      rw [leftMoves_mul_iff (GT.gt _)]
      constructor
      · intros i k
        apply mul_option_lt hx hy ihxy ihyx
      · simp only [← mul_option_symm (-y)]
        rw [mul_option_neg_neg x]
        have := mul_option_lt hy.neg hx.neg ihyxn ihxyn
        simp [gt_iff_lt]
        intros i j_1
        exact this j_1 l i (toLeftMovesNeg (toRightMovesNeg j))
    · intros j l
      revert i
      rw [leftMoves_mul_iff (GT.gt _)]
      constructor
      · simp only [← mul_option_symm y]
        have := mul_option_lt hy hx ihyx ihxy
        simp [gt_iff_lt]
        intros i j_1
        exact this j_1 l i j
      · rw [mul_option_neg_neg y]
        have := mul_option_lt hx.neg hy.neg ihxyn ihyxn
        simp [gt_iff_lt]
        intros i j_1
        exact this i j j_1 (toLeftMovesNeg (toRightMovesNeg l))
  all_goals (
    cases x
    cases y
    rintro (⟨i,j⟩|⟨i,j⟩)
  )
  rw [mk_mul_moveLeft_inl]
  pick_goal 2
  rw [mk_mul_moveLeft_inr]
  pick_goal 3
  rw [mk_mul_moveRight_inl]
  pick_goal 4
  rw [mk_mul_moveRight_inr]
  all_goals (
    apply Numeric.sub
    apply Numeric.add
    apply ihnx ih
    pick_goal 2
    apply ihny ih
    pick_goal 3
    apply ihnxy ih
  )
  all_goals { solve_by_elim [IsOption.mk_left, IsOption.mk_right] }


/-- A specialized induction hypothesis used to prove P2 and P4. -/
def ih24 (x₁ x₂ y: PGame) : Prop :=
  ∀ ⦃z⦄, (IsOption z x₁ → P24 z x₂ y) ∧ (IsOption z x₂ → P24 x₁ z y) ∧ (IsOption z y → P24 x₁ x₂ z)

/-- A specialized induction hypothesis used to prove P4. -/
def ih4 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z w⦄, IsOption w y → (IsOption z x₁ → P2 z x₂ w) ∧ (IsOption z x₂ → P2 x₁ z w)

/-! #### Specialize `ih'` to obtain specialized induction hypotheses for P2 and P4 -/

variable (ih' : ∀ a, args_rel a (Args.P24 x₁ x₂ y) → P124 a)

lemma ih₁₂ : ih24 x₁ x₂ y := by
  rw [ih24]
  refine (fun z => ⟨?_, ?_, ?_⟩) <;> (
    refine fun h => ih' (Args.P24 _ _ _) (TransGen.single ?_)
  )
  · exact (cutExpand_add_right {y}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_right h)


lemma ih₂₁ : ih24 x₂ x₁ y := ih₁₂ (by
  simp_rw [args_rel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih' ⊢
  suffices {x₁, y, x₂} = {x₂, y, x₁} by rwa [← this]
  dsimp [← Multiset.singleton_add] at ih' ⊢
  abel
)

lemma ih4_of_ih : ih4 x₁ x₂ y := by
  refine (fun z w h => ⟨?_, ?_⟩) <;> (
    intro h'
    apply (
      ih' (Args.P24 _ _ _)
      (TransGen.tail (TransGen.single _) (
        (cutExpand_add_left {x₁}).2  (cutExpand_pair_right h)
      )
      )
    ).1
    try exact (cutExpand_add_right {w}).2 $ cutExpand_pair_left h'
    try exact (cutExpand_add_right {w}).2 $ cutExpand_pair_right h'
  )

lemma numeric_of_ih : (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by
  constructor <;> (
    refine ih' (Args.P1 _ _) (TransGen.single ?_)
  )
  exact (cutExpand_add_right {y}).2 $ (cutExpand_add_left {x₁}).2 cutExpand_zero
  exact (cutExpand_add_right {x₂, y}).2 cutExpand_zero


/-- Symmetry properties of `ih24`. -/
lemma ih24_neg : ih24 x₁ x₂ y → ih24 (-x₂) (-x₁) y ∧ ih24 x₁ x₂ (-y) := by
  simp_rw [ih24, ← P24_negy, isOption_neg]
  refine (fun h => ⟨fun z => ⟨?_, ?_, ?_⟩,
      fun z => ⟨(@h z).1, (@h z).2.1, P24_negy.2 ∘ (@h $ -z).2.2⟩⟩) <;> (
        rw [P24_negx]
        simp only [neg_neg]
        try exact (@h $ -z).2.1
        try exact (@h $ -z).1
        try exact (@h z).2.2
      )

/-- Symmetry properties of `ih4`. -/
lemma ih4_neg : ih4 x₁ x₂ y → ih4 (-x₂) (-x₁) y ∧ ih4 x₁ x₂ (-y) := by
  simp_rw [ih4, isOption_neg]
  refine (fun h => ⟨fun z w h' => ?_, fun z w h' => ?_⟩)
  · specialize @h (-z) w h'
    rw [P2_negx]
    rw (config := {occs := .pos [2]}) [P2_negx]
    simp [neg_neg]
    tauto
  · specialize @h z (-w) h'
    rw [P2_negy]
    rw (config := {occs := .pos [2]}) [P2_negy]
    tauto

lemma mul_option_lt_mul_of_equiv (hn : x₁.Numeric) (h : ih24 x₁ x₂ y) (he : x₁ ≈ x₂) (i j) :
    ⟦mul_option x₁ y i j⟧ < (⟦x₂ * y⟧: Game) := by
  convert sub_lt_iff_lt_add'.2 ((((@h _).1 $ IsOption.moveLeft i).2 _).1 j) using 1
  { rw [← ((@h _).2.2 $ IsOption.moveLeft j).1 he]
    rfl
  }
  { rw [← lt_congr_right he]
    apply hn.moveLeft_lt
  }


/-- P2 follows from specialized induction hypotheses ("one half" of the equality). -/
theorem mul_right_le_of_equiv (h₁ : x₁.Numeric) (h₂ : x₂.Numeric)
    (h₁₂ : ih24 x₁ x₂ y) (h₂₁ : ih24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by
  apply PGame.le_of_forall_lt
  · have he' := neg_equiv_neg_iff.2 he
    simp_rw [lt_iff_game_lt]
    rw [leftMoves_mul_iff (GT.gt _)]
    constructor
    · exact fun i j => mul_option_lt_mul_of_equiv h₁ h₁₂ he i j
    · rw [← quot_neg_mul_neg]
      exact mul_option_lt_mul_of_equiv h₁.neg (ih24_neg $ (ih24_neg h₂₁).1).2 he'
  · have he' := neg_equiv_neg_iff.2 he
    simp_rw [lt_iff_game_lt]
    rw [rightMoves_mul_iff]
    constructor <;> (
      intros
      rw [lt_neg]
    )
    · rw [← quot_mul_neg]
      symm at he
      apply mul_option_lt_mul_of_equiv h₂ (ih24_neg h₂₁).2 he
    · rw [← quot_neg_mul]
      symm at he'
      apply mul_option_lt_mul_of_equiv h₂.neg (ih24_neg h₁₂).1 he'


/-- The statement that all left options of `x * y` of the first kind are less than itself. -/
def mul_options_lt_mul (x y: PGame) : Prop := ∀ ⦃i j⦄, ⟦mul_option x y i j⟧ < (⟦x * y⟧: Game)

/-- That the left options of `x * y` are less than itself and the right options are greater, which
  is part of the condition that `x * y` is numeric, is equivalent to the conjunction of various
  `mul_options_lt_mul` statements for `x`, `y` and their negations. We only show the forward
  direction. -/
lemma mul_options_lt_mul_of_numeric (hn : (x * y).Numeric) :
    (mul_options_lt_mul x y ∧ mul_options_lt_mul (-x) (-y)) ∧
    (mul_options_lt_mul x (-y) ∧ mul_options_lt_mul (-x) y) := by
  constructor
  · have h := hn.moveLeft_lt
    simp_rw [lt_iff_game_lt] at h
    convert (leftMoves_mul_iff (GT.gt _)).1 h
    rw [← quot_neg_mul_neg]
    rfl
  · have h := hn.lt_moveRight
    simp_rw [lt_iff_game_lt, rightMoves_mul_iff] at h
    refine h.imp ?_ ?_ <;> (
      refine forall₂_imp (fun a b => ?_)
      rw [lt_neg]
      try rw [quot_mul_neg]
      try rw [quot_neg_mul]
      exact id
    )

/-- A condition just enough to deduce P3, which will always be used with `x'` being a left
  option of `x₂`. When `y₁` is a left option of `y₂`, it can be deduced from induction hypotheses
  `ih24 x₁ x₂ y₂`, `ih4 x₁ x₂ y₂`, and `(x₂ * y₂).numeric` for P124 (`P3_cond_of_ih`); when `y₁` is
  not necessarily an option of `y₂`, it follows from the induction hypothesis for P3 (with `x₂`
  replaced by a left option `x'`) after the `main` theorem (P124) is established, and is used to
  prove P3 in full (`P3_of_lt_of_lt`). -/
def ih3 (x₁ x' x₂ y₁ y₂: PGame) : Prop :=
    P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

lemma ih3_of_ih (h24 : ih24 x₁ x₂ y) (h4 : ih4 x₁ x₂ y) (hl : mul_options_lt_mul x₂ y)
    (i j) : ih3 x₁ (x₂.moveLeft i) x₂ (y.moveLeft j) y :=
  let ml := @IsOption.moveLeft
  let h24 := (@h24 _).2.1 $ ml i
  ⟨(h4 $ ml j).2 $ ml i, h24.1, mul_option_lt_mul_iff_P3.1 $ @hl i j, fun l => (h24.2 l).1 _⟩

lemma P3_of_le_left {y₁ y₂} (i) (h : ih3 x₁ (x₂.moveLeft i) x₂ y₁ y₂)
  (hl : x₁ ≤ x₂.moveLeft i) : P3 x₁ x₂ y₁ y₂ := by
  obtain (hl|he) := lt_or_equiv_of_le hl
  · exact (h.2.2.2 hl).trans h.2.2.1
  · rw [P3, h.1 he, h.2.1 he]
    exact h.2.2.1

/-- P3 follows from `ih3` (so P4 (with `y₁` a left option of `y₂`) follows from the induction
  hypothesis). -/
theorem P3_of_lt {y₁ y₂} (h : ∀ i, ih3 x₁ (x₂.moveLeft i) x₂ y₁ y₂)
    (hs : ∀ i, ih3 (-x₂) ((-x₁).moveLeft i) (-x₁) y₁ y₂) (hl : x₁ < x₂) : P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i,hi⟩|⟨i,hi⟩) := lf_iff_exists_le.1 (lf_of_lt hl)
  · exact P3_of_le_left i (h i) hi
  · exact P3_neg.2 $
      P3_of_le_left _ (hs _) $ by {
        rw [moveLeft_neg]
        exact neg_le_neg (le_iff_game_le.1 hi) }

/-- The main chunk of Theorem 8 in [conway2001] / Theorem 3.8 in [schleicher_stoll]. -/
theorem main (a : Args) : a.Numeric → P124 a := by
  apply args_rel_wf.induction a
  intros a ih ha
  replace ih : ∀ a', args_rel a' a → P124 a' := fun a' hr => ih a' hr (hr.numeric_closed ha)
  cases a
  · /- P1 -/
    case _ x y =>
    simp [P124]
    simp [Args.Numeric, Args.toMultiset] at ha
    exact P1_of_ih ih (ha.1) (ha.2)
  · case _ x₁ x₂ y =>
    have h₁₂ := ih₁₂ ih
    have h₂₁ := ih₂₁ ih
    have h4 := ih4_of_ih ih
    obtain ⟨h₁₂x, h₁₂y⟩ := ih24_neg h₁₂
    obtain ⟨h4x, h4y⟩ := ih4_neg h4
    simp [P124, P24]
    constructor
    · /- P2 -/
      intro he
      simp [Args.Numeric, Args.toMultiset] at ha
      apply Quot.sound
      constructor
      · exact mul_right_le_of_equiv ha.1 ha.2.1 h₁₂ h₂₁ he
      · symm at he
        exact mul_right_le_of_equiv ha.2.1 ha.1 h₂₁ h₁₂ he
    · /- P4 -/
      intro hl
      obtain ⟨hn₁, hn₂⟩ := numeric_of_ih ih
      obtain ⟨⟨h₁, -⟩, h₂, -⟩ := mul_options_lt_mul_of_numeric hn₂
      obtain ⟨⟨-, h₃⟩, -, h₄⟩ := mul_options_lt_mul_of_numeric hn₁
      constructor <;> (
        intro
        refine P3_of_lt ?_ ?_ hl <;> (
          intro
          apply ih3_of_ih <;> try assumption

        )
      )
      exact (ih24_neg h₁₂y).1
      exact (ih4_neg h4y).1


end Surreal.Multiplication

namespace SetTheory.PGame
open Surreal.Multiplication

variable {x x₁ x₂ y y₁ y₂ : PGame.{u}}
  (hx : x.Numeric) (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric)
  (hy : y.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)

theorem Numeric.mul : Numeric (x * y) := main (Args.P1 x y) $ by
  simp [Args.Numeric, Args.toMultiset]
  tauto

theorem P24 : P24 x₁ x₂ y := main (Args.P24 x₁ x₂ y) $ by
  simp [Args.Numeric, Args.toMultiset]
  tauto

theorem Equiv.mul_congr_left (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  equiv_iff_game_eq.2 $ (P24 hx₁ hx₂ hy).1 he

theorem Equiv.mul_congr_right (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ :=
  PGame.Equiv.trans (mul_comm_equiv _ _) $
    PGame.Equiv.trans (mul_congr_left hy₁ hy₂ hx he) $ mul_comm_equiv _ _

theorem Equiv.mul_congr (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  PGame.Equiv.trans (mul_congr_left hx₁ hx₂ hy₁ hx) (mul_congr_right hx₂ hy₁ hy₂ hy)

open Prod.GameAdd

/-- One additional inductive argument that supplies the last missing part of Theorem 8. -/
theorem P3_of_lt_of_lt (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ := by
  revert x₁ x₂
  rw [← Prod.forall']
  intro t
  induction t using (wf_isOption.prod_gameAdd wf_isOption).induction with
  | _ t ih =>
    let ⟨x₁, x₂⟩ := t
    simp
    intro hx₁ hx₂ hx
    refine P3_of_lt ?_ ?_ hx <;> (
      intro i
    )
    · have hi := hx₂.moveLeft i
      exact ⟨(P24 hx₁ hi hy₁).1, (P24 hx₁ hi hy₂).1,
        P3_comm.2 $ ((P24 hy₁ hy₂ hx₂).2 hy).1 _,
        ih _ (snd $ IsOption.moveLeft i) hx₁ hi⟩
    · have hi := hx₁.neg.moveLeft i
      exact ⟨(P24 hx₂.neg hi hy₁).1, (P24 hx₂.neg hi hy₂).1,
        P3_comm.2 $ ((P24 hy₁ hy₂ hx₁).2 hy).2 _,
        by {
          rw [moveLeft_neg', ← P3_neg, neg_lt_neg_iff]
          exact ih _ (fst $ IsOption.moveRight _) (hx₁.moveRight _) hx₂ }⟩

theorem Numeric.mul_pos (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) : 0 < x₁ * x₂ := by
  rw [lt_iff_game_lt]
  have := P3_of_lt_of_lt numeric_zero hx₁ numeric_zero hx₂ hp₁ hp₂
  rw [P3] at this
  simp at this
  exact this
end SetTheory.PGame

namespace Surreal

open SetTheory.PGame.Equiv

noncomputable instance : LinearOrderedCommRing Surreal :=
{ Surreal.orderedAddCommGroup with
  mul := Surreal.lift₂ (fun x y ox oy => ⟦⟨x * y, ox.mul oy⟩⟧)
    (fun ox₁ oy₁ ox₂ oy₂ hx hy => Quotient.sound $ mul_congr ox₁ ox₂ oy₁ oy₂ hx hy)
  mul_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_assoc_equiv _ _ _)
  one := mk 1 numeric_one
  one_mul := by rintro ⟨_⟩; exact Quotient.sound (one_mul_equiv _)
  mul_one := by rintro ⟨_⟩; exact Quotient.sound (mul_one_equiv _)
  left_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (left_distrib_equiv _ _ _)
  right_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (right_distrib_equiv _ _ _)
  mul_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_comm_equiv _ _)
  le := lift₂ (fun x y _ _ => x ≤ y) (fun _ _ _ _ hx hy => propext $ le_congr hx hy)
  lt := lift₂ (fun x y _ _ => x < y) (fun _ _ _ _ hx hy => propext $ lt_congr hx hy)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_⟩ ⟨_⟩; exact lt_iff_le_not_le
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact @add_le_add_left PGame _ _ _ _ _ hx _
  zero_le_one := PGame.zero_lt_one.le
  zero_mul := by rintro ⟨_⟩; exact Quotient.sound (zero_mul_equiv _)
  mul_zero := by rintro ⟨_⟩; exact Quotient.sound (mul_zero_equiv _)
  exists_pair_ne := ⟨0, 1, ne_of_lt PGame.zero_lt_one⟩
  le_total := by rintro ⟨x⟩ ⟨y⟩; exact (le_or_gf x.1 y.1).imp id (fun h => h.le y.2 x.2)
  mul_pos := by rintro ⟨x⟩ ⟨y⟩; exact x.2.mul_pos y.2
  decidableLE := Classical.decRel _
}

end Surreal

open Surreal

namespace Ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal where
  toFun o := mk _ (numeric_toPGame o)
  inj' a b h := toPGame_equiv_iff.1 (by apply Quotient.exact h) -- Porting note: Added `by apply`
  map_rel_iff' := @toPGame_le_iff
#align ordinal.to_surreal Ordinal.toSurreal

end Ordinal
