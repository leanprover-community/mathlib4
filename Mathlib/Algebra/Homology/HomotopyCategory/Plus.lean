/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Shift.SingleFunctorsLift

/-!
# The triangulated subcategory K^+

-/

open CategoryTheory Category Limits Triangulated ZeroObject Pretriangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {D : Type _} [Category D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  (A : Type _) [Category A] [Abelian A]

namespace HomotopyCategory

def plus : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K ↦ ∃ (n : ℤ), CochainComplex.IsStrictlyGE K.1 n

instance : (plus C).IsTriangulated where
  exists_zero := by
    refine ⟨⟨0⟩, ?_, ⟨0, ?_⟩⟩
    · change IsZero ((quotient _ _).obj 0)
      rw [IsZero.iff_id_eq_zero, ← (quotient _ _).map_id, id_zero, Functor.map_zero]
    · dsimp
      infer_instance
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro ⟨X : CochainComplex C ℤ⟩ ⟨k, _ : X.IsStrictlyGE k⟩
        refine ⟨k - n, ?_⟩
        erw [Quotient.functor_obj_shift]
        exact X.isStrictlyGE_shift k n (k - n) (by omega) }
  ext₂' T hT := by
    rintro ⟨n₁, _⟩ ⟨n₃, _⟩
    obtain ⟨f : T.obj₃.as ⟶ T.obj₁.as⟦(1 : ℤ)⟧, hf⟩ := (quotient _ _ ).map_surjective
      (T.mor₃ ≫ ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app T.obj₁.as)
    let T₁ := T.rotate.rotate
    have hT₁ : T₁ ∈ distTriang _ := rot_of_distTriang _ (rot_of_distTriang _ hT)
    let T₂ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
      (CochainComplex.mappingCone.triangle f)
    have hT₂ : T₂ ∈ distTriang _ := by exact ⟨_, _, f, ⟨Iso.refl _⟩⟩
    have e := isoTriangleOfIso₁₂ T₁ T₂ hT₁ hT₂ (Iso.refl _)
      (((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).symm.app T.obj₁.as)
      (by dsimp [T₁, T₂]; rw [id_comp, hf])
    refine ⟨(quotient C (ComplexShape.up ℤ)).obj ((shiftFunctor (CochainComplex C ℤ) (-1)).obj
      (CochainComplex.mappingCone f)), ?_, ⟨?_⟩⟩
    · let n₀ : ℤ := min n₁ n₃ - 1
      have := min_le_left n₁ n₃
      have := min_le_right n₁ n₃
      have : (CochainComplex.mappingCone f).IsStrictlyGE n₀ := by
        rw [CochainComplex.isStrictlyGE_iff]
        intro i hi
        simp only [CochainComplex.mappingCone.isZero_X_iff]
        constructor
        · exact CochainComplex.isZero_of_isStrictlyGE T.obj₃.as n₃ (i + 1) (by omega)
        · exact CochainComplex.isZero_of_isStrictlyGE T.obj₁.as n₁ (i + 1) (by omega)
      exact ⟨_,
        (CochainComplex.mappingCone f).isStrictlyGE_shift n₀ (-1) (n₀ + 1) (by omega)⟩
    · exact (shiftEquiv _ (1 : ℤ)).unitIso.app T.obj₂ ≪≫
        (shiftFunctor _ (-1)).mapIso (Triangle.π₃.mapIso e) ≪≫
        ((quotient _ _).commShiftIso (-1)).symm.app (CochainComplex.mappingCone f)

abbrev Plus := (plus C).FullSubcategory

namespace Plus

abbrev ι : Plus C ⥤ HomotopyCategory C (ComplexShape.up ℤ) := (plus C).ι

def fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

def quasiIso : MorphismProperty (Plus A) := (HomotopyCategory.quasiIso A _).inverseImage (ι A)

instance : (quasiIso A).IsMultiplicative := by
  dsimp only [quasiIso]
  infer_instance

instance : (quasiIso A).IsCompatibleWithShift ℤ where
  condition a := by
    ext X Y f
    refine Iff.trans ?_ (MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ((ι A).map f) a)
    exact (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n => (plus C).lift (singleFunctor C n) (fun X => by
      refine ⟨n, ?_⟩
      change ((CochainComplex.singleFunctor C n).obj X).IsStrictlyGE n
      infer_instance))
    (fun n => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n := by
  apply SingleFunctors.liftFunctorCompIso

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end Plus

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C}
variable (F : C ⥤ D) [F.Additive]

def mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D :=
  (HomotopyCategory.plus D).lift
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ)) (by
      rintro ⟨X, ⟨n, _⟩⟩
      refine ⟨n, ?_⟩
      dsimp [HomotopyCategory.Plus.ι, HomotopyCategory.quotient, Quotient.functor]
      infer_instance)

noncomputable instance : (F.mapHomotopyCategoryPlus).CommShift ℤ := by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

instance : (F.mapHomotopyCategoryPlus).IsTriangulated := by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

noncomputable instance [Full F] [Faithful F] : Full F.mapHomotopyCategoryPlus where
  map_surjective f := ⟨(F.mapHomotopyCategory _).preimage f,
    (F.mapHomotopyCategory _).map_preimage f⟩

noncomputable instance [Full F] [Faithful F] : Faithful F.mapHomotopyCategoryPlus where
  map_injective h := (F.mapHomotopyCategory _).map_injective h

def mapHomotopyCategoryPlusCompIso {E : Type*} [Category E] [Preadditive E] [HasZeroObject E]
    [HasBinaryBiproducts E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    H.mapHomotopyCategoryPlus ≅ F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)))

end Functor

end CategoryTheory
