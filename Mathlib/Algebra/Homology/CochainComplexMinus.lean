/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# C^-

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C]

protected def minus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyLE n

instance [HasZeroMorphisms C] : (CochainComplex.minus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyLE_of_iso e n⟩

abbrev Minus [HasZeroMorphisms C] :=
  (CochainComplex.minus C).FullSubcategory

namespace Minus

section

variable [HasZeroMorphisms C]

def ι : Minus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance : (ι C).Full := ObjectProperty.full_ι _
instance : (ι C).Faithful := ObjectProperty.faithful_ι _

variable {C} in
def quasiIso [CategoryWithHomology C] : MorphismProperty (Minus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

end

variable [Preadditive C]

noncomputable instance : HasShift (Minus C) ℤ :=
  (fullyFaithfulι C).hasShift
    (fun (n : ℤ) => ObjectProperty.lift _
    (Minus.ι C ⋙ CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) (by
      rintro ⟨K, k, hk⟩
      exact ⟨k - n, K.isStrictlyLE_shift k n _ (by omega)⟩))
    (fun n => ObjectProperty.liftCompιIso _ _ _)

instance : (ι C).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

end Minus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

def mapCochainComplexMinus : CochainComplex.Minus C ⥤ CochainComplex.Minus D :=
  ObjectProperty.lift _ (CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Minus.ι]
    infer_instance)

def mapCochainComplexMinusCompι :
    F.mapCochainComplexMinus ⋙ CochainComplex.Minus.ι D ≅
      CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory
