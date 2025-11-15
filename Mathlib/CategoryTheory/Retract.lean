/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.EpiMono

/-!
# Retracts

Defines retracts of objects and morphisms.

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- An object `X` is a retract of `Y` if there are morphisms `i : X ⟶ Y` and `r : Y ⟶ X` such
that `i ≫ r = 𝟙 X`. -/
structure Retract (X Y : C) where
  /-- the split monomorphism -/
  i : X ⟶ Y
  /-- the split epimorphism -/
  r : Y ⟶ X
  retract : i ≫ r = 𝟙 X := by cat_disch

namespace Retract

attribute [reassoc (attr := simp)] retract

variable {X Y : C} (h : Retract X Y)

open Opposite

/-- Retracts are preserved when passing to the opposite category. -/
@[simps]
def op : Retract (op X) (op Y) where
  i := h.r.op
  r := h.i.op
  retract := by simp [← op_comp, h.retract]

/-- If `X` is a retract of `Y`, then `F.obj X` is a retract of `F.obj Y`. -/
@[simps]
def map (F : C ⥤ D) : Retract (F.obj X) (F.obj Y) where
  i := F.map h.i
  r := F.map h.r
  retract := by rw [← F.map_comp h.i h.r, h.retract, F.map_id]

/-- a retract determines a split epimorphism. -/
@[simps] def splitEpi : SplitEpi h.r where
  section_ := h.i

/-- a retract determines a split monomorphism. -/
@[simps] def splitMono : SplitMono h.i where
  retraction := h.r

instance : IsSplitEpi h.r := ⟨⟨h.splitEpi⟩⟩

instance : IsSplitMono h.i := ⟨⟨h.splitMono⟩⟩

variable (X) in
/-- Any object is a retract of itself. -/
@[simps]
def refl : Retract X X where
  i := 𝟙 X
  r := 𝟙 X

/-- A retract of a retract is a retract. -/
@[simps]
def trans {Z : C} (h' : Retract Y Z) : Retract X Z where
  i := h.i ≫ h'.i
  r := h'.r ≫ h.r

/-- If `e : X ≅ Y`, then `X` is a retract of `Y`. -/
def ofIso (e : X ≅ Y) : Retract X Y where
  i := e.hom
  r := e.inv

end Retract

/--
```
  X -------> Z -------> X
  |          |          |
  f          g          f
  |          |          |
  v          v          v
  Y -------> W -------> Y

```
A morphism `f : X ⟶ Y` is a retract of `g : Z ⟶ W` if there are morphisms `i : f ⟶ g`
and `r : g ⟶ f` in the arrow category such that `i ≫ r = 𝟙 f`. -/
abbrev RetractArrow {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) := Retract (Arrow.mk f) (Arrow.mk g)

namespace RetractArrow

variable {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)

@[reassoc]
lemma i_w : h.i.left ≫ g = f ≫ h.i.right := h.i.w

@[reassoc]
lemma r_w : h.r.left ≫ f = g ≫ h.r.right := h.r.w

/-- The top of a retract diagram of morphisms determines a retract of objects. -/
@[simps!]
def left : Retract X Z := h.map Arrow.leftFunc

/-- The bottom of a retract diagram of morphisms determines a retract of objects. -/
@[simps!]
def right : Retract Y W := h.map Arrow.rightFunc

@[reassoc (attr := simp)]
lemma retract_left : h.i.left ≫ h.r.left = 𝟙 X := h.left.retract

@[reassoc (attr := simp)]
lemma retract_right : h.i.right ≫ h.r.right = 𝟙 Y := h.right.retract

instance : IsSplitEpi h.r.left := ⟨⟨h.left.splitEpi⟩⟩

instance : IsSplitEpi h.r.right := ⟨⟨h.right.splitEpi⟩⟩

instance : IsSplitMono h.i.left := ⟨⟨h.left.splitMono⟩⟩

instance : IsSplitMono h.i.right := ⟨⟨h.right.splitMono⟩⟩

/-- If a morphism `f` is a retract of `g`,
then `F.map f` is a retract of `F.map g` for any functor `F`. -/
@[simps!]
def map (F : C ⥤ D) : RetractArrow (F.map f) (F.map g) :=
  Retract.map h F.mapArrow

/-- If a morphism `f` is a retract of `g`, then `f.op` is a retract of `g.op`. -/
@[simps]
def op : RetractArrow f.op g.op where
  i.left := h.r.right.op
  i.right := h.r.left.op
  i.w := by simp [← op_comp]
  r.left := h.i.right.op
  r.right := h.i.left.op
  r.w := by simp [← op_comp]
  retract := by ext <;> simp [← op_comp]

/-- If a morphism `f` in the opposite category is a retract of `g`,
then `f.unop` is a retract of `g.unop`. -/
@[simps]
def unop {X Y Z W : Cᵒᵖ} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
 : RetractArrow f.unop g.unop where
  i.left := h.r.right.unop
  i.right := h.r.left.unop
  i.w := by simp [← unop_comp]
  r.left := h.i.right.unop
  r.right := h.i.left.unop
  r.w := by simp [← unop_comp]
  retract := by ext <;> simp [← unop_comp]

end RetractArrow

namespace Iso

/-- If `X` is isomorphic to `Y`, then `X` is a retract of `Y`. -/
@[simps]
def retract {X Y : C} (e : X ≅ Y) : Retract X Y where
  i := e.hom
  r := e.inv

end Iso

end CategoryTheory
