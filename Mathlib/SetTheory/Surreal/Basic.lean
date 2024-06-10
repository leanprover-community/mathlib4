/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathlib.Algebra.Order.Hom.Monoid
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

We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers

The proof that multiplication lifts to surreal numbers is surprisingly difficult and is currently
missing in the library. A sample proof can be found in Theorem 3.8 in the second reference below.
The difficulty lies in the length of the proof and the number of theorems that need to proven
simultaneously. This will make for a fun and challenging project.

The branch `surreal_mul` contains some progress on this proof.

### Todo

- Define the field structure on the surreals.

## References

* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
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

open Surreal

namespace Ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal where
  toFun o := mk _ (numeric_toPGame o)
  inj' a b h := toPGame_equiv_iff.1 (by apply Quotient.exact h) -- Porting note: Added `by apply`
  map_rel_iff' := @toPGame_le_iff
#align ordinal.to_surreal Ordinal.toSurreal

end Ordinal
