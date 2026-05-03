/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift

/-!
# The triangulated subcategory of bounded below cochain complexes up to homotopy

-/

@[expose] public section

open CategoryTheory Category Limits Triangulated ZeroObject Pretriangulated
  HomotopicalAlgebra

variable (C : Type*) [Category* C] [Preadditive C]
  (A : Type*) [Category* A] [Abelian A]

namespace CochainComplex

open HomologicalComplex

variable {C} [HasBinaryBiproducts C]

lemma plus_cylinder (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (cylinder K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  dsimp [cylinder]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj ↦ ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (.up ℤ) i).mapBiprod _ _)
    simpa using K.isZero_of_isStrictlyGE n i
  · simp only [ComplexShape.up_Rel] at hj
    exact K.isZero_of_isStrictlyGE n _ (by lia)

lemma plus_pathObject (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (pathObject K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine pathObject.isZero_X _ _ (K.isZero_of_isStrictlyGE n i)
    (fun j hj ↦ ?_)
  simp only [ComplexShape.up_Rel] at hj
  exact K.isZero_of_isStrictlyGE n j

lemma isStrictlyGE_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n₁ n₂ n : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (hn₁ : n < n₁ := by lia)
    (hn₂ : n ≤ n₂ := by lia) :
    (mappingCone f).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  simp at hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _, L.isZero_of_isStrictlyGE n₂ _⟩

noncomputable abbrev Plus.precylinder (K : Plus C) : Precylinder K :=
  K.obj.precylinder.toFullSubcategory (K.obj.plus_cylinder K.property)

noncomputable abbrev Plus.prepathObject (K : Plus C) : PrepathObject K :=
  K.obj.prepathObject.toFullSubcategory (K.obj.plus_pathObject K.property)

end CochainComplex

namespace HomotopyCategory

def plus : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K ↦ ∃ (n : ℤ), CochainComplex.IsStrictlyGE K.1 n

@[simp]
lemma plus_functor_obj_iff (K : CochainComplex C ℤ) :
    plus C ((quotient _ _).obj K) ↔ ∃ (n : ℤ), CochainComplex.IsStrictlyGE K n :=
  Iff.rfl

instance [HasZeroObject C] : (plus C).ContainsZero where
  exists_zero := by
    refine ⟨(HomotopyCategory.quotient _ _).obj 0,
      Functor.map_isZero _ (isZero_zero _), ?_⟩
    simp only [plus_functor_obj_iff]
    exact ⟨0, inferInstance⟩

instance : (plus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [plus_functor_obj_iff] at hK
        obtain ⟨q, _⟩ := hK
        refine ⟨q - n, ?_⟩
        have : (((HomotopyCategory.quotient _ _).obj K)⟦n⟧).as =
          ((HomotopyCategory.quotient _ _).obj (K⟦n⟧)).as := by
          congr 1; apply Quotient.functor_obj_shift
        rw [this]
        exact K.isStrictlyGE_shift q n (q - n) (by lia) }

instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (plus C).IsTriangulatedClosed₃ where
  ext₃' T hT := by
    rintro ⟨n₁, _⟩ ⟨n₂, _⟩
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · dsimp
      simp only [plus_functor_obj_iff]
      exact ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _
        (by simp) (by simp)⟩
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp [hf]

instance [HasZeroObject C] [HasBinaryBiproducts C] : (plus C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

abbrev Plus := (plus C).FullSubcategory

namespace Plus

abbrev ι : Plus C ⥤ HomotopyCategory C (ComplexShape.up ℤ) := (plus C).ι

abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

def quasiIso : MorphismProperty (Plus A) := (HomotopyCategory.quasiIso A _).inverseImage (ι A)
  deriving MorphismProperty.IsMultiplicative

lemma quasiIso_iff {K L : Plus A} (f : K ⟶ L) :
    quasiIso A f ↔ (HomotopyCategory.quasiIso A _) f.hom := Iff.rfl

instance : (quasiIso A).IsCompatibleWithShift ℤ where
  condition a := by
    ext X Y f
    simp only [quasiIso_iff, ← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso A (.up ℤ)) f.hom a]
    exact (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

instance : (quasiIso A).RespectsIso := by
  dsimp only [quasiIso]
  infer_instance

@[simps!]
def quotient : CochainComplex.Plus C ⥤ Plus C :=
  ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ)) (by
      rintro ⟨K, n, hn⟩
      exact ⟨n, hn⟩)

variable {C} in
lemma quotient_obj_surjective : Function.Surjective (quotient C).obj :=
  fun K ↦ ⟨⟨K.obj.as, K.property⟩, rfl⟩

instance : (quotient C).EssSurj where
  mem_essImage K := ⟨⟨K.obj.as, K.property⟩, ⟨Iso.refl _⟩⟩

instance : (quotient C).Full := by dsimp [quotient]; infer_instance

open HomologicalComplex in
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (quotient C).IsLocalization
      ((homotopyEquivalences C (.up ℤ)).inverseImage (CochainComplex.Plus.ι C)) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      simpa [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι C),
        ← isIso_quotient_map_iff_homotopyEquivalences] using hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    replace hf := homotopyOfEq f₀ f₁ ((HomotopyCategory.Plus.ι _).congr_map hf)
    exact ⟨K.precylinder, Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
      { h := cylinder.desc _ _ hf }, ⟨cylinder.homotopyEquiv _ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩⟩)

def quotientCompι :
  quotient C ⋙ ι C ≅
    CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ) := by
  apply ObjectProperty.liftCompιIso

variable [HasZeroObject C] [HasBinaryBiproducts C]
noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n => (plus C).lift (singleFunctor C n) (fun X => by
      refine ⟨n, ?_⟩
      change ((CochainComplex.singleFunctor C n).obj X).IsStrictlyGE n
      infer_instance))
    (fun n => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n :=
  Iso.refl _

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end Plus

end HomotopyCategory
