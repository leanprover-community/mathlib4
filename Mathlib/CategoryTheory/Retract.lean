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
  /-- `i : X ⟶ Y` -/
  i : X ⟶ Y
  /-- `r : Y ⟶ X` -/
  r : Y ⟶ X
  /-- `i ≫ r = 𝟙 X` -/
  retract : i ≫ r = 𝟙 X

namespace Retract

attribute [reassoc (attr := simp)] retract

variable {X Y : C} (h : Retract X Y)

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

@[simp, reassoc]
lemma retract_left : h.i.left ≫ h.r.left = 𝟙 X := Arrow.hom.congr_left h.retract

@[simp, reassoc]
lemma retract_right : h.i.right ≫ h.r.right = 𝟙 Y := Arrow.hom.congr_right h.retract

@[reassoc]
lemma fac : h.i.left ≫ g ≫ h.r.right = f := by simp

/-- The top of a retract diagram of morphisms determines a retract of objects. -/
@[simps]
def left : Retract X Z where
  i := h.i.left
  r := h.r.left
  retract := h.retract_left

/-- The bottom of a retract diagram of morphisms determines a retract of objects. -/
@[simps]
def right : Retract Y W where
  i := h.i.right
  r := h.r.right
  retract := h.retract_right

/-- The bottom of a retract diagram determines a split epimorphism. -/
@[simps] def splitEpiLeft : SplitEpi h.r.left where
  section_ := h.i.left

/-- The top of a retract diagram determines a split epimorphism. -/
@[simps] def splitEpiRight : SplitEpi h.r.right where
  section_ := h.i.right

/-- The bottom of a retract diagram determines a split monomorphism. -/
@[simps] def splitMonoLeft : SplitMono h.i.left where
  retraction := h.r.left

/-- The top of a retract diagram determines a split monomorphism. -/
@[simps] def splitMonoRight : SplitMono h.i.right where
  retraction := h.r.right

instance : IsSplitEpi h.r.left := ⟨⟨h.splitEpiLeft⟩⟩

instance : IsSplitEpi h.r.right := ⟨⟨h.splitEpiRight⟩⟩

instance : IsSplitMono h.i.left := ⟨⟨h.splitMonoLeft⟩⟩

instance : IsSplitMono h.i.right := ⟨⟨h.splitMonoRight⟩⟩

end RetractArrow

end CategoryTheory
