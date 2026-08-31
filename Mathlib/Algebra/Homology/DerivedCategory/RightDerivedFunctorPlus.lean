/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# The right derived functor on the bounded below derived category

If `F : C ⥤ D` is an additive functor between abelian categories,
where `C` has enough injectives, we define the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
between the corresponding bounded below derived categories.

TODO(@joelriou): show that this functor is triangulated and refactor
the definition of `Functor.rightDerived`

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The right derived functor `DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has enough injectives. -/
noncomputable def rightDerivedFunctorPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)

/-- The natural transformation that is part of the data of the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has enough injectives. It is defined here as a derived functor of
`F.mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D`,
postcomposed with `DerivedCategory.Plus.Qh`.
(See `Functor.rightDerivedFunctorPlusUnit` for the similar result regarding
`F.mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D`.) -/
@[no_expose]
noncomputable def rightDerivedFunctorPlusUnith :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)

instance :
    F.rightDerivedFunctorPlus.IsRightDerivedFunctor
      F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) := by
  dsimp only [rightDerivedFunctorPlus, rightDerivedFunctorPlusUnith]
  infer_instance

instance : F.rightDerivedFunctorPlus.CommShift ℤ := sorry

instance : F.rightDerivedFunctorPlus.IsTriangulated := sorry

instance : NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ := sorry

/-- A natural transformation that is part of the data of the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has enough injectives. While the right derived functor was defined using
bounded below homotopy categories, this natural transformation allows to say
that it is also the derived functor of the functor
`F.mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D`,
postcomposed with `DerivedCategory.Plus.Q`. -/
@[no_expose, simps! -isSimp app]
noncomputable def rightDerivedFunctorPlusUnit :
    F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
    DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus :=
  whiskerLeft _ (DerivedCategory.Plus.quotientCompQhIso D).inv ≫
    (associator _ _ _).inv ≫ whiskerRight F.quotientCompMapHomotopyCategoryPlusIso.inv _ ≫
    (associator _ _ _).hom ≫
    whiskerLeft (HomotopyCategory.Plus.quotient C) F.rightDerivedFunctorPlusUnith ≫
    (associator _ _ _).inv ≫ whiskerRight (DerivedCategory.Plus.quotientCompQhIso C).hom _

instance : NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ := by
  dsimp [rightDerivedFunctorPlusUnit]
  infer_instance

instance (K : CochainComplex.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj K)) := by
  simp only [F.rightDerivedFunctorPlusUnit_app]
  infer_instance

lemma derives_mapCochainComplexPlus_comp_Q :
    (CochainComplex.Plus.localizerMorphism C).Derives
      (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
  sorry

instance : F.rightDerivedFunctorPlus.IsRightDerivedFunctor
    F.rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso C) :=
  F.derives_mapCochainComplexPlus_comp_Q.isRightDerivedFunctor_of_isIso _
    (by dsimp; infer_instance)

example (X : HomotopyCategory.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X)) := by
  infer_instance

example (K : CochainComplex.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj K))) := by
  infer_instance

end Functor

end CategoryTheory
