/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou

! This file was ported from Lean 3 source module category_theory.comm_sq
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Arrow

/-!
# Commutative squares

This file provide an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `comm_sq top left right bottom` is the predicate that this
square is commutative.

The structure `comm_sq` is extended in `category_theory/shapes/limits/comm_sq.lean`
as `is_pullback` and `is_pushout` in order to define pullback and pushout squares.

## Future work

Refactor `lift_struct` from `arrow.lean` and lifting properties using `comm_sq.lean`.

-/


namespace CategoryTheory

variable {C : Type _} [Category C]

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
  w : f ≫ h = g ≫ i
#align category_theory.comm_sq CategoryTheory.CommSq

attribute [reassoc.1] comm_sq.w

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem flip (p : CommSq f g h i) : CommSq g f i h :=
  ⟨p.w.symm⟩
#align category_theory.comm_sq.flip CategoryTheory.CommSq.flip

theorem of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.Hom h.left h.right g.Hom :=
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

end CommSq

namespace Functor

variable {D : Type _} [Category D]

variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.map i) :=
  ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩
#align category_theory.functor.map_comm_sq CategoryTheory.Functor.map_commSq

end Functor

alias functor.map_comm_sq ← comm_sq.map
#align category_theory.comm_sq.map CategoryTheory.CommSq.map

namespace CommSq

variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

/-- The datum of a lift in a commutative square, i.e. a up-right-diagonal
morphism which makes both triangles commute. -/
@[ext, nolint has_nonempty_instance]
structure LiftStruct (sq : CommSq f i p g) where
  l : B ⟶ X
  fac_left' : i ≫ l = f
  fac_right' : l ≫ p = g
#align category_theory.comm_sq.lift_struct CategoryTheory.CommSq.LiftStruct

namespace LiftStruct

restate_axiom fac_left'

restate_axiom fac_right'

/-- A `lift_struct` for a commutative square gives a `lift_struct` for the
corresponding square in the opposite category. -/
@[simps]
def op {sq : CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.op
    where
  l := l.l.op
  fac_left' := by rw [← op_comp, l.fac_right]
  fac_right' := by rw [← op_comp, l.fac_left]
#align category_theory.comm_sq.lift_struct.op CategoryTheory.CommSq.LiftStruct.op

/-- A `lift_struct` for a commutative square in the opposite category
gives a `lift_struct` for the corresponding square in the original category. -/
@[simps]
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
    (l : LiftStruct sq) : LiftStruct sq.unop
    where
  l := l.l.unop
  fac_left' := by rw [← unop_comp, l.fac_right]
  fac_right' := by rw [← unop_comp, l.fac_left]
#align category_theory.comm_sq.lift_struct.unop CategoryTheory.CommSq.LiftStruct.unop

/-- Equivalences of `lift_struct` for a square and the corresponding square
in the opposite category. -/
@[simps]
def opEquiv (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.op
    where
  toFun := op
  invFun := unop
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.comm_sq.lift_struct.op_equiv CategoryTheory.CommSq.LiftStruct.opEquiv

/-- Equivalences of `lift_struct` for a square in the oppositive category and
the corresponding square in the original category. -/
def unopEquiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.unop
    where
  toFun := unop
  invFun := op
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.comm_sq.lift_struct.unop_equiv CategoryTheory.CommSq.LiftStruct.unopEquiv

end LiftStruct

instance subsingleton_liftStruct_of_epi (sq : CommSq f i p g) [Epi i] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    simp only [← cancel_epi i, lift_struct.fac_left]⟩
#align category_theory.comm_sq.subsingleton_lift_struct_of_epi CategoryTheory.CommSq.subsingleton_liftStruct_of_epi

instance subsingleton_liftStruct_of_mono (sq : CommSq f i p g) [Mono p] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    simp only [← cancel_mono p, lift_struct.fac_right]⟩
#align category_theory.comm_sq.subsingleton_lift_struct_of_mono CategoryTheory.CommSq.subsingleton_liftStruct_of_mono

variable (sq : CommSq f i p g)

/-- The assertion that a square has a `lift_struct`. -/
class HasLift : Prop where
  exists_lift : Nonempty sq.LiftStruct
#align category_theory.comm_sq.has_lift CategoryTheory.CommSq.HasLift

namespace HasLift

variable {sq}

theorem mk' (l : sq.LiftStruct) : HasLift sq :=
  ⟨Nonempty.intro l⟩
#align category_theory.comm_sq.has_lift.mk' CategoryTheory.CommSq.HasLift.mk'

variable (sq)

theorem iff : HasLift sq ↔ Nonempty sq.LiftStruct :=
  by
  constructor
  exacts[fun h => h.exists_lift, fun h => mk h]
#align category_theory.comm_sq.has_lift.iff CategoryTheory.CommSq.HasLift.iff

theorem iff_op : HasLift sq ↔ HasLift sq.op :=
  by
  rw [Iff, Iff]
  exact Nonempty.congr (lift_struct.op_equiv sq).toFun (lift_struct.op_equiv sq).invFun
#align category_theory.comm_sq.has_lift.iff_op CategoryTheory.CommSq.HasLift.iff_op

theorem iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : HasLift sq ↔ HasLift sq.unop :=
  by
  rw [Iff, Iff]
  exact Nonempty.congr (lift_struct.unop_equiv sq).toFun (lift_struct.unop_equiv sq).invFun
#align category_theory.comm_sq.has_lift.iff_unop CategoryTheory.CommSq.HasLift.iff_unop

end HasLift

/-- A choice of a diagonal morphism that is part of a `lift_struct` when
the square has a lift. -/
noncomputable def lift [hsq : HasLift sq] : B ⟶ X :=
  hsq.exists_lift.some.l
#align category_theory.comm_sq.lift CategoryTheory.CommSq.lift

@[simp, reassoc.1]
theorem fac_left [hsq : HasLift sq] : i ≫ sq.lift = f :=
  hsq.exists_lift.some.fac_left
#align category_theory.comm_sq.fac_left CategoryTheory.CommSq.fac_left

@[simp, reassoc.1]
theorem fac_right [hsq : HasLift sq] : sq.lift ≫ p = g :=
  hsq.exists_lift.some.fac_right
#align category_theory.comm_sq.fac_right CategoryTheory.CommSq.fac_right

end CommSq

end CategoryTheory

