/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Logic.Small.Basic

/-!
# Smallness of a property of objects

In this file, given `P : ObjectProperty C`, we define
`ObjectProperty.Small.{w} P` as an abbreviation for `Small.{w} (Subtype P)`.

-/

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- A property of objects is small relative to a universe `w`
if the corresponding subtype is. -/
protected abbrev Small (P : ObjectProperty C) : Prop := _root_.Small.{w} (Subtype P)

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    Small.{w} P.FullSubcategory :=
  small_of_surjective (f := fun (x : Subtype P) ↦ ⟨x.1, x.2⟩) (fun x ↦ ⟨⟨x.1, x.2⟩, rfl⟩)

lemma Small.of_le {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P ≤ Q) :
    ObjectProperty.Small.{w} P :=
  small_of_injective (Subtype.map_injective h Function.injective_id)

end CategoryTheory.ObjectProperty
