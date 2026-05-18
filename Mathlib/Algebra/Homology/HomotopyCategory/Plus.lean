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

In this file, we introduce the triangulated full subcategory `HomotopyCategory.Plus C`
of `HomotopyCategory C (.up ℤ)` consisting of bounded below cochain complexes.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Pretriangulated HomotopicalAlgebra

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

/-- The pre-cylinder object attached to `K : Plus C`. -/
noncomputable abbrev Plus.precylinder (K : Plus C) : Precylinder K :=
  K.obj.precylinder.toFullSubcategory (K.obj.plus_cylinder K.property)

/-- The pre-path object attached to `K : Plus C`. -/
noncomputable abbrev Plus.prepathObject (K : Plus C) : PrepathObject K :=
  K.obj.prepathObject.toFullSubcategory (K.obj.plus_pathObject K.property)

end CochainComplex

namespace HomotopyCategory

/-- The property of objects in `HomotopyCategory C (.up ℤ)` whose
underlying cochain complex is bounded below. (Note: this property of
objects is not closed under isomorphisms.) -/
def plus : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (CochainComplex.plus C).strictMap (quotient _ _)

variable {C} in
@[simp]
lemma plus_quotient_obj_iff (K : CochainComplex C ℤ) :
    plus C ((quotient _ _).obj K) ↔ CochainComplex.plus C K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  simp only [plus, ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

instance [HasZeroObject C] : (plus C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [plus_quotient_obj_iff]
      exact ⟨0, inferInstance⟩⟩

instance : (plus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [plus_quotient_obj_iff] at hK
        obtain ⟨q, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff, shift_quotient_obj,
          plus_quotient_obj_iff]
        exact ⟨q - n, K.isStrictlyGE_shift q n (q - n) (by lia)⟩ }

set_option backward.isDefEq.respectTransparency false in
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (plus C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨n₁, _⟩ : (CochainComplex.plus C) T.obj₁.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨n₂, _⟩ : (CochainComplex.plus C) T.obj₂.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · dsimp
      simp only [plus_quotient_obj_iff]
      exact ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _
        (by simp) (by simp)⟩
    · simp [hf]

instance [HasZeroObject C] [HasBinaryBiproducts C] : (plus C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded below cochain complexes. -/
abbrev Plus := (plus C).FullSubcategory

namespace Plus

/-- The inclusion of the homotopy category of bounded below cochain complexes
in the homotopy category category of all cochain complexes. -/
abbrev ι : Plus C ⥤ HomotopyCategory C (.up ℤ) := (plus C).ι

/-- The inclusion functor
`HomotopyCategory.ι C : HomotopyCategory.Plus C ⥤ HomotopyCategory C (.up ℤ)` is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- The class of quasi-isomorphisms in the homotopy category of bounded below cochain
complexes. -/
def quasiIso : MorphismProperty (Plus A) :=
  (HomotopyCategory.quasiIso A _).inverseImage (ι A)
deriving MorphismProperty.IsMultiplicative

lemma quasiIso_iff {K L : Plus A} (f : K ⟶ L) :
    quasiIso A f ↔ (HomotopyCategory.quasiIso A _) f.hom := Iff.rfl

instance : (quasiIso A).IsCompatibleWithShift ℤ where
  condition a := by
    ext X Y f
    simp only [quasiIso_iff, ← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso _ _) f.hom a]
    exact (HomotopyCategory.quasiIso _ _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

instance : (quasiIso A).RespectsIso := by
  dsimp only [quasiIso]
  infer_instance

/-- The full and essentially surjective functor
`CochainComplex.Plus C ⥤ HomotopyCategory.Plus C`. -/
@[simps!]
def quotient : CochainComplex.Plus C ⥤ Plus C :=
  ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up ℤ)) (by
      rintro ⟨K, h⟩
      simpa [plus_quotient_obj_iff])

/-- The functor
`HomotopyCategory.Plus.quotient C : CochainComplex.Plus C ⥤ HomotopyCategory.Plus C`
is induced by the functor `HomotopyCategory.quotient C (.up ℤ)` from `CochainComplex C ℤ`
to `HomotopyCategory C (.up ℤ)`. -/
def quotientCompιIso :
    quotient C ⋙ ι C ≅ CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up ℤ) :=
  ObjectProperty.liftCompιIso ..

variable {C} in
lemma quotient_obj_surjective : Function.Surjective (quotient C).obj :=
  fun K ↦ by
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, by ext; exact hL⟩
    rw [← HomotopyCategory.plus_quotient_obj_iff, hL]
    exact K.property

instance : (quotient C).EssSurj where
  mem_essImage K := by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective K
    exact ⟨L, ⟨Iso.refl _⟩⟩

instance : (quotient C).Full := by dsimp [quotient]; infer_instance

section

variable [HasZeroObject C] [HasBinaryBiproducts C]

open HomologicalComplex in
instance :
    (quotient C).IsLocalization
      ((homotopyEquivalences C (.up ℤ)).inverseImage (CochainComplex.Plus.ι C)) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      simpa [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι C),
        ← inverseImage_quotient_isomorphisms] using hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    replace hf := homotopyOfEq f₀ f₁ ((HomotopyCategory.Plus.ι _).congr_map hf)
    exact ⟨K.precylinder, Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
      { h := cylinder.desc _ _ hf }, ⟨cylinder.homotopyEquiv _ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩⟩)

/-- The collection of all single functors `C ⥤ HomotopyCategory.Plus C` for `n : ℤ`
along with their compatibilities with shifts. -/
noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n ↦ (plus C).lift (singleFunctor C n)
    (fun X ↦ by
      rw [← quotient_obj_singleFunctors_obj, plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩))
    (fun _ ↦ Iso.refl _)

/-- The single functor `C ⥤ HomotopyCategory.Plus C`. -/
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C :=
  (singleFunctors C).functor n

/-- The single functor `C ⥤ HomotopyCategory.Plus C` is induced by
`HomotopyCategory.singleFunctor C n : C ⥤ HomotopyCategory C (.up ℤ)`. -/
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n :=
  Iso.refl _

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end

end Plus

end HomotopyCategory
