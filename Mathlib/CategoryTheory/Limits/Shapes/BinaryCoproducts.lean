/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of preserved binary coproducts
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

/-- If a functor preserves a binary coproduct and the target has zero morphisms, the image of the
first summand is a retract of the image of the coproduct. -/
noncomputable def Functor.retractCoprod
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) (X Y : C) [HasBinaryCoproduct X Y] [HasBinaryCoproduct (F.obj X) (F.obj Y)]
    [PreservesColimit (pair X Y) F] : Retract (F.obj X) (F.obj (X ⨿ Y)) where
  i := F.map (coprod.inl : X ⟶ X ⨿ Y)
  r := CategoryTheory.inv (coprodComparison F X Y) ≫ coprod.desc (𝟙 (F.obj X)) 0
  retract := by rw [map_inl_inv_coprodComparison_assoc, coprod.inl_desc]

end CategoryTheory
