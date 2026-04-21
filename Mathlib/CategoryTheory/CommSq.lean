/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Commutative squares

This file provides an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `CommSq top left right bottom` is the predicate that this
square is commutative.

The structure `CommSq` is extended in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`
as `IsPullback` and `IsPushout` in order to define pullback and pushout squares.

## Future work

Refactor `LiftStruct` from `Arrow.lean` and lifting properties using `CommSq.lean`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- The proposition that a square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
is a commuting square.
-/
@[to_dual self (reorder := W Z, X Y, f i, g h)]
structure CommSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop where
  /-- The square commutes. -/
  w : f ≫ h = g ≫ i := by cat_disch

attribute [simp] CommSq.mk

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option linter.translateOverwrite false in
@[to_dual existing w]
lemma w' (self : CommSq f g h i) : g ≫ i = f ≫ h := self.w.symm

set_option linter.translateOverwrite false in
/-- `CommSq.mk'` is the dual of `CommSq.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
lemma mk' (w : g ≫ i = f ≫ h := by cat_disch) : CommSq f g h i :=
  ⟨w.symm⟩

attribute [reassoc] CommSq.w

@[to_dual self]
theorem flip (p : CommSq f g h i) : CommSq g f i h :=
  ⟨p.w.symm⟩

theorem of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.hom h.left h.right g.hom :=
  ⟨h.w.symm⟩

/-- The commutative square in the opposite category associated to a commutative square. -/
@[to_dual self]
theorem op (p : CommSq f g h i) : CommSq i.op h.op g.op f.op :=
  ⟨by simp only [← op_comp, p.w]⟩

/-- The commutative square associated to a commutative square in the opposite category. -/
@[to_dual self]
theorem unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    CommSq i.unop h.unop g.unop f.unop :=
  ⟨by simp only [← unop_comp, p.w]⟩

@[to_dual none]
theorem vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i) :
    CommSq i g.inv h.inv f :=
  ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

@[to_dual none]
theorem horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom) :
    CommSq f.inv h g i.inv :=
  flip (vert_inv (flip p))

/-- The horizontal composition of two commutative squares as below is a commutative square.
```
  W ---f---> X ---f'--> X'
  |          |          |
  g          h          h'
  |          |          |
  v          v          v
  Y ---i---> Z ---i'--> Z'

```
-/
@[to_dual self (reorder := W Z', X Z, X' Y, f i', f' i, g h', hsq₁ hsq₂)]
lemma horiz_comp {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z}
    {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq f' h h' i') :
    CommSq (f ≫ f') g h' (i ≫ i') :=
  ⟨by rw [← Category.assoc, Category.assoc, ← hsq₁.w, hsq₂.w, Category.assoc]⟩

/-- The vertical composition of two commutative squares as below is a commutative square.
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z
  |          |
  g'         h'
  |          |
  v          v
  Y'---i'--> Z'

```
-/
@[to_dual self (reorder := W Z', Y Z, Y' X, g h', g' h, f i', hsq₁ hsq₂)]
lemma vert_comp {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
    {h' : Z ⟶ Z'} {i : Y ⟶ Z} {i' : Y' ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq i g' h' i') :
    CommSq f (g ≫ g') (h ≫ h') i' :=
  flip (horiz_comp (flip hsq₁) (flip hsq₂))


section

variable {W X Y : C}

@[to_dual none]
theorem eq_of_mono {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i i) : f = g :=
  (cancel_mono i).1 sq.w

@[to_dual none]
theorem eq_of_epi {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i) : h = i :=
  (cancel_epi f).1 sq.w

end

end CommSq

namespace Functor

variable {D : Type*} [Category* D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

@[to_dual self]
theorem map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.map i) :=
  ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩

end Functor

@[to_dual self]
alias CommSq.map := Functor.map_commSq

namespace CommSq


variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

/-- Now we consider a square:
```
  A ---f---> X
  |          |
  i          p
  |          |
  v          v
  B ---g---> Y
```

The datum of a lift in a commutative square, i.e. an up-right-diagonal
morphism which makes both triangles commute. -/
@[ext, to_dual self]
structure LiftStruct (sq : CommSq f i p g) where
  /-- The lift. -/
  l : B ⟶ X
  /-- The upper left triangle commutes. -/
  fac_left : i ≫ l = f := by cat_disch
  /-- The lower right triangle commutes. -/
  fac_right : l ≫ p = g := by cat_disch

attribute [to_dual self] LiftStruct.ext
set_option linter.translateOverwrite false in
attribute [to_dual existing fac_left] LiftStruct.fac_right
attribute [to_dual self (reorder := A Y, B X, f g, i p, fac_left fac_right)] LiftStruct.mk

namespace LiftStruct

/-- A `LiftStruct` for a commutative square gives a `LiftStruct` for the
corresponding square in the opposite category. -/
@[simps, to_dual self]
def op {sq : CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.op where
  l := l.l.op
  fac_left := by rw [← op_comp, l.fac_right]
  fac_right := by rw [← op_comp, l.fac_left]

/-- A `LiftStruct` for a commutative square in the opposite category
gives a `LiftStruct` for the corresponding square in the original category. -/
@[simps, to_dual self]
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
    (l : LiftStruct sq) : LiftStruct sq.unop where
  l := l.l.unop
  fac_left := by rw [← unop_comp, l.fac_right]
  fac_right := by rw [← unop_comp, l.fac_left]

/-- Equivalences of `LiftStruct` for a square and the corresponding square
in the opposite category. -/
@[simps, to_dual self]
def opEquiv (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.op where
  toFun := op
  invFun := unop
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equivalences of `LiftStruct` for a square in the opposite category and
the corresponding square in the original category. -/
@[simps, to_dual self]
def unopEquiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.unop where
  toFun := unop
  invFun := op
  left_inv := by cat_disch
  right_inv := by cat_disch

end LiftStruct

@[to_dual]
instance subsingleton_liftStruct_of_epi (sq : CommSq f i p g) [Epi i] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_epi i]
    simp only [LiftStruct.fac_left]⟩

variable (sq : CommSq f i p g)

/-- The assertion that a square has a `LiftStruct`. -/
@[to_dual self]
class HasLift : Prop where
  /-- Square has a `LiftStruct`. -/
  exists_lift : Nonempty sq.LiftStruct

namespace HasLift

variable {sq} in
@[to_dual self]
theorem mk' (l : sq.LiftStruct) : HasLift sq :=
  ⟨Nonempty.intro l⟩

@[to_dual self]
theorem iff : HasLift sq ↔ Nonempty sq.LiftStruct := by
  constructor
  exacts [fun h => h.exists_lift, fun h => mk h]

@[to_dual self]
theorem iff_op : HasLift sq ↔ HasLift sq.op := by
  rw [iff, iff]
  exact Nonempty.congr (LiftStruct.opEquiv sq).toFun (LiftStruct.opEquiv sq).invFun

@[to_dual self]
theorem iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : HasLift sq ↔ HasLift sq.unop := by
  rw [iff, iff]
  exact Nonempty.congr (LiftStruct.unopEquiv sq).toFun (LiftStruct.unopEquiv sq).invFun

end HasLift

/-- A choice of a diagonal morphism that is part of a `LiftStruct` when
the square has a lift. -/
@[to_dual self]
noncomputable def lift [hsq : HasLift sq] : B ⟶ X :=
  hsq.exists_lift.some.l

@[to_dual (attr := reassoc (attr := simp)) fac_right]
theorem fac_left [hsq : HasLift sq] : i ≫ sq.lift = f :=
  hsq.exists_lift.some.fac_left

end CommSq

end CategoryTheory
