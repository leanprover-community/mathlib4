/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathlib.CategoryTheory.Comma.Arrow

#align_import category_theory.comm_sq from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# Commutative squares

This file provide an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `CommSq top left right bottom` is the predicate that this
square is commutative.

The structure `CommSq` is extended in `CategoryTheory/Shapes/Limits/CommSq.lean`
as `IsPullback` and `IsPushout` in order to define pullback and pushout squares.

## Future work

Refactor `LiftStruct` from `Arrow.lean` and lifting properties using `CommSq.lean`.

-/


namespace CategoryTheory

variable {C : Type*} [Category C]

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
structure CommSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop where
  /-- The square commutes. -/
  w : f ≫ h = g ≫ i
#align category_theory.comm_sq CategoryTheory.CommSq

attribute [reassoc] CommSq.w

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem flip (p : CommSq f g h i) : CommSq g f i h :=
  ⟨p.w.symm⟩
#align category_theory.comm_sq.flip CategoryTheory.CommSq.flip

theorem of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.hom h.left h.right g.hom :=
  ⟨h.w.symm⟩
#align category_theory.comm_sq.of_arrow CategoryTheory.CommSq.of_arrow

/-- The commutative square in the opposite category associated to a commutative square. -/
theorem op (p : CommSq f g h i) : CommSq i.op h.op g.op f.op :=
  ⟨by simp only [← op_comp, p.w]⟩
#align category_theory.comm_sq.op CategoryTheory.CommSq.op

/-- The commutative square associated to a commutative square in the opposite category. -/
theorem unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    CommSq i.unop h.unop g.unop f.unop :=
  ⟨by simp only [← unop_comp, p.w]⟩
#align category_theory.comm_sq.unop CategoryTheory.CommSq.unop

theorem vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i) :
    CommSq i g.inv h.inv f :=
  ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

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
lemma vert_comp {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
    {h' : Z ⟶ Z'} {i : Y ⟶ Z} {i' : Y' ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq i g' h' i') :
    CommSq f (g ≫ g') (h ≫ h') i' :=
  flip (horiz_comp (flip hsq₁) (flip hsq₂))

end CommSq

namespace Functor

variable {D : Type*} [Category D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.map i) :=
  ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩
#align category_theory.functor.map_comm_sq CategoryTheory.Functor.map_commSq

end Functor

alias CommSq.map := Functor.map_commSq
#align category_theory.comm_sq.map CategoryTheory.CommSq.map

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
-- porting note (#5171): removed @[nolint has_nonempty_instance]
@[ext]
structure LiftStruct (sq : CommSq f i p g) where
  /-- The lift. -/
  l : B ⟶ X
  /-- The upper left triangle commutes. -/
  fac_left : i ≫ l = f
  /-- The lower right triangle commutes. -/
  fac_right: l ≫ p = g
#align category_theory.comm_sq.lift_struct CategoryTheory.CommSq.LiftStruct

namespace LiftStruct

/-- A `LiftStruct` for a commutative square gives a `LiftStruct` for the
corresponding square in the opposite category. -/
@[simps]
def op {sq : CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.op where
  l := l.l.op
  fac_left := by rw [← op_comp, l.fac_right]
  fac_right := by rw [← op_comp, l.fac_left]
#align category_theory.comm_sq.lift_struct.op CategoryTheory.CommSq.LiftStruct.op

/-- A `LiftStruct` for a commutative square in the opposite category
gives a `LiftStruct` for the corresponding square in the original category. -/
@[simps]
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
    (l : LiftStruct sq) : LiftStruct sq.unop where
  l := l.l.unop
  fac_left := by rw [← unop_comp, l.fac_right]
  fac_right := by rw [← unop_comp, l.fac_left]
#align category_theory.comm_sq.lift_struct.unop CategoryTheory.CommSq.LiftStruct.unop

/-- Equivalences of `LiftStruct` for a square and the corresponding square
in the opposite category. -/
@[simps]
def opEquiv (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.op where
  toFun := op
  invFun := unop
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.comm_sq.lift_struct.op_equiv CategoryTheory.CommSq.LiftStruct.opEquiv

/-- Equivalences of `LiftStruct` for a square in the oppositive category and
the corresponding square in the original category. -/
def unopEquiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.unop where
  toFun := unop
  invFun := op
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.comm_sq.lift_struct.unop_equiv CategoryTheory.CommSq.LiftStruct.unopEquiv

end LiftStruct

instance subsingleton_liftStruct_of_epi (sq : CommSq f i p g) [Epi i] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_epi i]
    simp only [LiftStruct.fac_left]⟩
#align category_theory.comm_sq.subsingleton_lift_struct_of_epi CategoryTheory.CommSq.subsingleton_liftStruct_of_epi

instance subsingleton_liftStruct_of_mono (sq : CommSq f i p g) [Mono p] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_mono p]
    simp only [LiftStruct.fac_right]⟩
#align category_theory.comm_sq.subsingleton_lift_struct_of_mono CategoryTheory.CommSq.subsingleton_liftStruct_of_mono

variable (sq : CommSq f i p g)


/-- The assertion that a square has a `LiftStruct`. -/
class HasLift : Prop where
  /-- Square has a `LiftStruct`. -/
  exists_lift : Nonempty sq.LiftStruct
#align category_theory.comm_sq.has_lift CategoryTheory.CommSq.HasLift

namespace HasLift

variable {sq}

theorem mk' (l : sq.LiftStruct) : HasLift sq :=
  ⟨Nonempty.intro l⟩
#align category_theory.comm_sq.has_lift.mk' CategoryTheory.CommSq.HasLift.mk'

variable (sq)

theorem iff : HasLift sq ↔ Nonempty sq.LiftStruct := by
  constructor
  exacts [fun h => h.exists_lift, fun h => mk h]
#align category_theory.comm_sq.has_lift.iff CategoryTheory.CommSq.HasLift.iff

theorem iff_op : HasLift sq ↔ HasLift sq.op := by
  rw [iff, iff]
  exact Nonempty.congr (LiftStruct.opEquiv sq).toFun (LiftStruct.opEquiv sq).invFun
#align category_theory.comm_sq.has_lift.iff_op CategoryTheory.CommSq.HasLift.iff_op

theorem iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : HasLift sq ↔ HasLift sq.unop := by
  rw [iff, iff]
  exact Nonempty.congr (LiftStruct.unopEquiv sq).toFun (LiftStruct.unopEquiv sq).invFun
#align category_theory.comm_sq.has_lift.iff_unop CategoryTheory.CommSq.HasLift.iff_unop

end HasLift

/-- A choice of a diagonal morphism that is part of a `LiftStruct` when
the square has a lift. -/
noncomputable def lift [hsq : HasLift sq] : B ⟶ X :=
  hsq.exists_lift.some.l
#align category_theory.comm_sq.lift CategoryTheory.CommSq.lift

@[reassoc (attr := simp)]
theorem fac_left [hsq : HasLift sq] : i ≫ sq.lift = f :=
  hsq.exists_lift.some.fac_left
#align category_theory.comm_sq.fac_left CategoryTheory.CommSq.fac_left

@[reassoc (attr := simp)]
theorem fac_right [hsq : HasLift sq] : sq.lift ≫ p = g :=
  hsq.exists_lift.some.fac_right
#align category_theory.comm_sq.fac_right CategoryTheory.CommSq.fac_right

end CommSq

end CategoryTheory
