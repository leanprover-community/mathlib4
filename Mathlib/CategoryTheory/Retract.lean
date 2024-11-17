/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Retracts

Defines retracts of objects and morphisms.

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An object `X` is a retract of `Y` if there are morphisms `i : X ⟶ Y` and `r : Y ⟶ X` such
that `i ≫ r = 𝟙 X`. -/
class Retract (X Y : C) where
  /-- `i : X ⟶ Y` -/
  i : X ⟶ Y
  /-- `r : Y ⟶ X` -/
  r : Y ⟶ X
  /-- `i ≫ r = 𝟙 X` -/
  retract : i ≫ r = 𝟙 X

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

lemma leftSqComm : h.i.left ≫ g = f ≫ h.i.right := h.i.w

lemma rightSqComm : h.r.left ≫ f = g ≫ h.r.right := h.r.w

@[simp]
lemma topCompId : h.i.left ≫ h.r.left = 𝟙 X := Arrow.hom.congr_left h.retract

@[simp]
lemma bottomCompId : h.i.right ≫ h.r.right = 𝟙 Y := Arrow.hom.congr_right h.retract

@[simp]
lemma topCompBottom : h.i.left ≫ g ≫ h.r.right = f := by
  rw [← Category.assoc, leftSqComm, Category.assoc, bottomCompId, Category.comp_id]

end RetractArrow

namespace MorphismProperty

/-- A class of morphisms is stable under retracts if the retract of a morphism still
lies in the class. -/
class IsStableUnderRetracts (P : MorphismProperty C) : Prop where
  of_Retract {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f

lemma of_Retract {P : MorphismProperty C} [P.IsStableUnderRetracts]
    {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f :=
  IsStableUnderRetracts.of_Retract h hg

instance IsStableUnderRetracts.monomorphisms :
    (monomorphisms C).IsStableUnderRetracts := by
  refine ⟨fun {X Y} _ _ f g H p ↦ ⟨fun α β ω ↦ ?_⟩⟩
  have := ω =≫ H.i.right
  rw [Category.assoc, Category.assoc, ← RetractArrow.leftSqComm, ← Category.assoc,
    ← Category.assoc] at this
  have ω' := p.right_cancellation (α ≫ H.i.left) (β ≫ H.i.left) this =≫ H.r.left
  aesop

end MorphismProperty

end CategoryTheory
