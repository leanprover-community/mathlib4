/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.EpiMono

/-!
# Retracts

Defines retracts of objects and morphisms.

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

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

/-- the bottom of a retract diagram determines a split epimorphism. -/
@[simps] def splitEpiLeft : SplitEpi h.r.left where
  section_ := h.i.left

/-- the top of a retract diagram determines a split epimorphism. -/
@[simps] def splitEpiRight : SplitEpi h.r.right where
  section_ := h.i.right

/-- the bottom of a retract diagram determines a split monomorphism. -/
@[simps] def splitMonoLeft : SplitMono h.i.left where
  retraction := h.r.left

/-- the top of a retract diagram determines a split monomorphism. -/
@[simps] def splitMonoRight : SplitMono h.i.right where
  retraction := h.r.right

instance : IsSplitEpi h.r.left := ⟨⟨h.splitEpi_left⟩⟩

instance : IsSplitEpi h.r.right := ⟨⟨h.splitEpi_right⟩⟩

instance : IsSplitMono h.i.left := ⟨⟨h.splitMono_left⟩⟩

instance : IsSplitMono h.i.right := ⟨⟨h.splitMono_right⟩⟩

end RetractArrow

namespace MorphismProperty

/-- A class of morphisms is stable under retracts if a retract of such a morphism still
lies in the class. -/
class IsStableUnderRetracts (P : MorphismProperty C) : Prop where
  of_retract {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f

lemma of_retract {P : MorphismProperty C} [P.IsStableUnderRetracts]
    {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f :=
  IsStableUnderRetracts.of_retract h hg

instance IsStableUnderRetracts.monomorphisms : (monomorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ f g} h (hg : Mono g) := ⟨fun α β w ↦ by
    rw [← cancel_mono h.i.left, ← cancel_mono g, Category.assoc, Category.assoc,
      h.i_w, reassoc_of% w]⟩

instance IsStableUnderRetracts.epimorphisms : (epimorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ f g} h (hg : Epi g) := ⟨fun α β w ↦ by
    rw [← cancel_epi h.r.right, ← cancel_epi g, ← Category.assoc, ← Category.assoc, ← h.r_w,
      Category.assoc, Category.assoc, w]⟩

instance IsStableUnderRetracts.isomorphisms : (isomorphisms C).IsStableUnderRetracts where
  of_retract {X Y Z W f g} h (_ : IsIso _) := by
    refine ⟨h.i.right ≫ inv g ≫ h.r.left, ?_, ?_⟩
    · rw [← h.i_w_assoc, IsIso.hom_inv_id_assoc, h.retract_left]
    · rw [Category.assoc, Category.assoc, h.r_w, IsIso.inv_hom_id_assoc, h.retract_right]

end MorphismProperty

end CategoryTheory
