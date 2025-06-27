/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.BifunctorTriangulated
import Mathlib.Algebra.Homology.BifunctorColimits
import Mathlib.Algebra.Homology.HomotopyCategory.MonoidalTriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Devissage
import Mathlib.Algebra.Homology.HomotopyCategory.PreservesQuasiIso
import Mathlib.Algebra.Homology.LeftResolutions.CochainComplex
import Mathlib.Algebra.Homology.LeftResolutions.Reduced
import Mathlib.Algebra.Homology.DerivedCategory.Monoidal
import Mathlib.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
import Mathlib.CategoryTheory.Localization.OfQuotient
import Mathlib.CategoryTheory.GuitartExact.Quotient

/-!
# Flat objects and K-flat complexes

-/

open CategoryTheory MonoidalCategory Limits Opposite ZeroObject

section

@[simps obj]
def Antitone.functor {α β : Type*} [Preorder α] [Preorder β]
    {f : α → β} (hf : Antitone f) :
    αᵒᵖ ⥤ β where
  obj a := f a.unop
  map φ := homOfLE (hf (leOfHom φ.unop))

lemma Int.antitone_neg : Antitone (fun (n : ℤ) ↦ -n) := fun _ _ _ ↦ by dsimp; omega

@[simps]
def Int.opEquivalence : ℤᵒᵖ ≌ ℤ where
  functor := Int.antitone_neg.functor
  inverse := Int.antitone_neg.functor.rightOp
  unitIso := NatIso.ofComponents (fun n ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun n ↦ eqToIso (by simp))

end

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex

open HomologicalComplex

abbrev KFlat := (quasiIso A (.up ℤ)).KFlat
noncomputable abbrev ιKFlat : KFlat A ⥤ CochainComplex A ℤ := MorphismProperty.ιKFlat _

variable {A}

lemma kFlat_iff_preservesQuasiIso (K : CochainComplex A ℤ) :
    (quasiIso A (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨_, isZero_zero _, by
    rw [kFlat_iff_preservesQuasiIso]
    constructor
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← tensor_id, id_zero, MonoidalPreadditive.zero_tensor]
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← tensor_id, id_zero, MonoidalPreadditive.tensor_zero]⟩

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    rw [ObjectProperty.prop_shift_iff, kFlat_iff_preservesQuasiIso]
    constructor
    · exact (preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexObjShiftIso (curriedTensor A) K n)).2
          (hK.1.comp (preservesQuasiIso_shiftFunctor A n))
    · exact (preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexFlipObjShiftIso (curriedTensor A) K n)).2
          (hK.2.comp (preservesQuasiIso_shiftFunctor A n))⟩

lemma kFlat_shift_iff (K : CochainComplex A ℤ) (n : ℤ) :
    (quasiIso A (.up ℤ)).kFlat (K⟦n⟧) ↔ (quasiIso A (.up ℤ)).kFlat K := by
  apply ObjectProperty.prop_shift_iff_of_isStableUnderShift

variable (A) in
lemma closedUnderColimitsOfShape_kFlat (J : Type*) [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).obj X)] :
    ClosedUnderColimitsOfShape J (quasiIso A (.up ℤ)).kFlat := by
  intro F c hc hF
  rw [kFlat_iff_preservesQuasiIso]
  have hJ := isStableUnderColimitsOfShape_preservesQuasiIso A A (.up ℤ) (.up ℤ) J
  constructor
  · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)) :=
      inferInstanceAs (PreservesColimitsOfShape _
        (Functor.bifunctorMapHomologicalComplex _ _ _ _))
    exact hJ (isColimitOfPreserves (curriedTensor _) hc) (fun j ↦ (hF j).1)
  · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)).flip :=
      inferInstanceAs (PreservesColimitsOfShape _
        (Functor.bifunctorMapHomologicalComplex _ _ _ _).flip)
    exact hJ (isColimitOfPreserves (curriedTensor _).flip hc) (fun j ↦ (hF j).2)

end CochainComplex

namespace HomotopyCategory

variable {A}

lemma kFlat_iff_preservesQuasiIso (K : HomotopyCategory A (.up ℤ)) :
    (quasiIso A (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

lemma kFlat_quotient_obj_iff (K : CochainComplex A ℤ) :
    (quasiIso A (.up ℤ)).kFlat ((quotient _ _).obj K) ↔
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K := by
  rw [kFlat_iff_preservesQuasiIso, CochainComplex.kFlat_iff_preservesQuasiIso]
  apply and_congr <;> exact Functor.preservesQuasiIso_iff_of_factors (Iso.refl _)

instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨(quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
    rw [kFlat_quotient_obj_iff]
    exact ObjectProperty.prop_zero _⟩

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    rw [kFlat_quotient_obj_iff] at hK
    rw [ObjectProperty.prop_shift_iff]
    refine ((quasiIso A (ComplexShape.up ℤ)).kFlat.prop_iff_of_iso
      (((quotient A (.up ℤ)).commShiftIso n).app K)).1 ?_
    dsimp
    rw [kFlat_quotient_obj_iff]
    exact (HomologicalComplex.quasiIso A (.up ℤ)).kFlat.le_shift n _ hK⟩

lemma kFlat_iff_preserves_acyclic (K : HomotopyCategory A (.up ℤ)) :
    (quasiIso A (.up ℤ)).kFlat K ↔ ∀ (Z : HomotopyCategory A (.up ℤ))
        (_ : subcategoryAcyclic A Z), subcategoryAcyclic A (K ⊗ Z) ∧
          subcategoryAcyclic A (Z ⊗ K) := by
  rw [kFlat_iff_preservesQuasiIso]
  simp only [preservesQuasiIso_iff_preserves_acyclic]
  constructor
  · rintro ⟨h₁, h₂⟩ Z hZ
    exact ⟨h₁ _ hZ, h₂ _ hZ⟩
  · rintro hZ
    exact ⟨fun _ hX ↦ (hZ _ hX).1, fun _ hX ↦ (hZ _ hX).2⟩

instance : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦ by
    simp only [HomotopyCategory.kFlat_iff_preserves_acyclic] at h₁ h₃ ⊢
    intro Z hZ
    exact ⟨(HomotopyCategory.subcategoryAcyclic A).ext_of_isTriangulatedClosed₂ _
      (((curriedTensor _).flip.obj Z).map_distinguished _ hT) (h₁ Z hZ).1 (h₃ Z hZ).1,
        (HomotopyCategory.subcategoryAcyclic A).ext_of_isTriangulatedClosed₂ _
      (((curriedTensor _).obj Z).map_distinguished _ hT) (h₁ Z hZ).2 (h₃ Z hZ).2⟩)

variable (A) in
lemma closedUnderLimitsOfShape_discrete_kFlat (J : Type) [Finite J] :
    ClosedUnderLimitsOfShape (Discrete J) (quasiIso A (.up ℤ)).kFlat := by
  apply ObjectProperty.closedUnderLimitsOfShape_discrete_of_isTriangulated

instance : (quasiIso A (.up ℤ)).kFlat.IsClosedUnderRetracts where
  of_retract {K L} e hL := by
    have : (subcategoryAcyclic A).IsClosedUnderRetracts := inferInstance
    rw [kFlat_iff_preserves_acyclic] at hL ⊢
    intro Z hZ
    exact ⟨ObjectProperty.prop_of_retract _ (e.map (tensorRight Z)) (hL Z hZ).1,
      ObjectProperty.prop_of_retract _ (e.map (tensorLeft Z)) (hL Z hZ).2⟩

end HomotopyCategory

namespace CochainComplex

variable {A}

open HomologicalComplex

instance : (quasiIso A (.up ℤ)).kFlat.IsClosedUnderRetracts where
  of_retract e h := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff] at h ⊢
    exact ObjectProperty.prop_of_retract _ (e.map (HomotopyCategory.quotient _ _)) h

variable (A) in
lemma closedUnderLimitsOfShape_discrete_kFlat (J : Type) [Finite J] :
    ClosedUnderLimitsOfShape (Discrete J) (quasiIso A (.up ℤ)).kFlat := by
  intro F c hc hF
  rw [← HomotopyCategory.kFlat_quotient_obj_iff]
  apply HomotopyCategory.closedUnderLimitsOfShape_discrete_kFlat A J
    (isLimitOfPreserves (HomotopyCategory.quotient _ _) hc)
  rintro j
  dsimp
  rw [HomotopyCategory.kFlat_quotient_obj_iff]
  exact hF j

lemma kFlat_prod {K L : CochainComplex A ℤ} (hK : (quasiIso A (.up ℤ)).kFlat K)
    (hL : (quasiIso A (.up ℤ)).kFlat L) :
    (quasiIso A (.up ℤ)).kFlat (K ⨯ L) :=
  closedUnderLimitsOfShape_discrete_kFlat A WalkingPair (limit.isLimit (pair K L))
    (by rintro (_ | _) <;> assumption)

lemma kFlat_biprod {K L : CochainComplex A ℤ} (hK : (quasiIso A (.up ℤ)).kFlat K)
    (hL : (quasiIso A (.up ℤ)).kFlat L) :
    (quasiIso A (.up ℤ)).kFlat (K ⊞ L) :=
  ObjectProperty.prop_of_iso _ (biprod.isoProd K L).symm (kFlat_prod hK hL)

lemma kFlat_single_obj_iff_flat (X : A) (n : ℤ) :
    (quasiIso A (.up ℤ)).kFlat ((single _ _ n).obj X) ↔ ObjectProperty.flat X := by
  trans (quasiIso A (.up ℤ)).kFlat ((single _ _ 0).obj X)
  · rw [← kFlat_shift_iff ((single _ _ 0).obj X) (-n)]
    exact ((quasiIso A (ComplexShape.up ℤ)).kFlat.prop_iff_of_iso
      (((CochainComplex.singleFunctors A).shiftIso (-n) n 0 (by simp)).app X).symm)
  · simp only [kFlat_iff_preservesQuasiIso, ObjectProperty.flat,
      Functor.exactFunctor_iff_preservesQuasiIso _ (.up ℤ) (i₀ := 0) rfl (by simp)]
    apply and_congr
    · exact preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexObjSingleIso (curriedTensor A) X)
    · exact preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexFlipObjSingleIso (curriedTensor A) X)

instance : (ObjectProperty.flat (A := A)).ContainsZero where
  exists_zero := ⟨0, isZero_zero A, by
    rw [← kFlat_single_obj_iff_flat _ 0]
    apply ObjectProperty.prop_of_isZero
    apply Functor.map_isZero
    apply Limits.isZero_zero⟩

variable (A) in
lemma closedUnderLimitsOfShape_discrete_flat (J : Type) [Finite J] :
    ClosedUnderLimitsOfShape (Discrete J) (ObjectProperty.flat (A := A)) := by
  intro F c hc hF
  simp only [← kFlat_single_obj_iff_flat _ 0] at hF ⊢
  apply closedUnderLimitsOfShape_discrete_kFlat A J
    (isLimitOfPreserves (single _ (.up ℤ) 0) hc)
  exact hF

instance : HasFiniteProducts (ObjectProperty.flat (A := A)).FullSubcategory where
  out n := by
    apply hasLimitsOfShape_of_closedUnderLimits
    apply closedUnderLimitsOfShape_discrete_flat

instance : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance : (ObjectProperty.flat (A := A)).IsClosedUnderRetracts where
  of_retract e h := by
    rw [← kFlat_single_obj_iff_flat _ 0] at h ⊢
    exact ObjectProperty.prop_of_retract _ (e.map ((single _ (.up ℤ) 0))) h

variable (A) in
lemma closedUnderColimitsOfShape_flat (J : Type*) [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).obj X)] :
    ClosedUnderColimitsOfShape J (ObjectProperty.flat (A := A)) := by
  intro F c hc hF
  simp only [← kFlat_single_obj_iff_flat _ 0] at hF ⊢
  apply closedUnderColimitsOfShape_kFlat A J (isColimitOfPreserves (single _ (.up ℤ) 0) hc)
  exact hF

lemma kFlat_of_bounded_of_flat (K : CochainComplex A ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, ObjectProperty.flat (K.X n)) :
    (quasiIso A (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff]
  apply HomotopyCategory.mem_subcategory_of_strictly_bounded _ K a b
  intro n _ _
  replace hK := hK n
  rw [← kFlat_single_obj_iff_flat _ 0,
    ← HomotopyCategory.kFlat_quotient_obj_iff] at hK
  exact ObjectProperty.prop_of_iso _
    ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).symm.app (K.X n)) hK

-- to be moved
section

variable (K : CochainComplex A ℤ)

@[simps]
noncomputable def coconeStupidFiltrationGE :
    Cocone K.stupidFiltrationGE where
  pt := K
  ι := { app n := K.ιStupidTrunc _ }

noncomputable def isColimitCoconeStupidFiltrationGE :
    IsColimit K.coconeStupidFiltrationGE :=
  HomologicalComplex.isColimitOfEval _ _ (fun n ↦ by
    apply isColimitOfIsEventuallyConstant _ (op n)
    rintro ⟨j⟩ ⟨h⟩
    obtain ⟨i, rfl⟩ := Int.le.dest (leOfHom h)
    exact isIso_ιStupidTrunc_f _ _ rfl)

variable [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

lemma kFlat_of_isStrictlyLE_of_flat (b : ℤ) [K.IsStrictlyLE b]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    (hK : ∀ n, ObjectProperty.flat (K.X n)) :
    (quasiIso A (.up ℤ)).kFlat K := by
  apply (closedUnderColimitsOfShape_kFlat A ℤ)
    (K.isColimitCoconeStupidFiltrationGE.whiskerEquivalence
      Int.opEquivalence.symm)
  intro i
  apply kFlat_of_bounded_of_flat (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-i))) (-i) b
  intro n
  by_cases hn : -i ≤ n
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    let φ := (ιStupidTrunc K (ComplexShape.embeddingUpIntGE (-i))).f n
    have : IsIso φ := isIso_ιStupidTrunc_f K _ (i := k) (by dsimp; omega)
    exact ObjectProperty.prop_of_iso _ (asIso φ).symm (hK n)
  · apply ObjectProperty.prop_of_isZero
    apply isZero_stupidTrunc_X K (ComplexShape.embeddingUpIntGE (-i)) n
    intro
    dsimp
    omega

variable (A) in
lemma cochainComplexMinus_flat_le_kFlat
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A] :
    ObjectProperty.flat.cochainComplexMinus ≤ (quasiIso A (.up ℤ)).kFlat := by
  rintro K ⟨hK, n, h₂⟩
  exact kFlat_of_isStrictlyLE_of_flat K n hK

end

end CochainComplex

namespace CategoryTheory.Abelian

variable {A} {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
  {ι : C ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
  (Λ : LeftResolutions ι) [Λ.F.PreservesZeroMorphisms]
  (hι : ι.essImage ≤ ObjectProperty.flat)


namespace LeftResolutions

namespace kFlatLocalizerSquare

variable (A)

def L : LocalizerMorphism (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).WKFlat
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).WKFlat where
  functor := ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ HomotopyCategory.quotient _ _)
    (fun ⟨K, hK⟩ ↦ by
      dsimp
      rwa [HomotopyCategory.kFlat_quotient_obj_iff])
  map := by
    rintro ⟨K, hK⟩ ⟨L, hL⟩ (f : K ⟶ L) hf
    simpa [MorphismProperty.WKFlat, HomotopyCategory.quotient_map_mem_quasiIso_iff] using hf

abbrev R : LocalizerMorphism (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) where
  functor := HomotopyCategory.quotient _ _
  map _ _ _ _ := by simpa [HomotopyCategory.quotient_map_mem_quasiIso_iff]

noncomputable abbrev T := (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat

noncomputable abbrev B := (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat

def WL : MorphismProperty (HomologicalComplex.quasiIso A (.up ℤ)).KFlat :=
  (HomologicalComplex.homotopyEquivalences A (.up ℤ)).inverseImage (T A).functor

instance : (L A).functor.EssSurj where
  mem_essImage := by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := K.functor_obj_surjective
    replace hK := (HomotopyCategory.kFlat_quotient_obj_iff K).1 hK
    exact ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩

instance : (L A).functor.Full where
  map_surjective {K L} f := by
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    exact ⟨g, rfl⟩

noncomputable def iso : (T A).functor ⋙ (R A).functor ≅ (L A).functor ⋙ (B A).functor :=
  Iso.refl _

variable {A} in
lemma kFlat_cylinder (K : CochainComplex A ℤ)
    (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K.cylinder := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff]
  apply ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished _)
  · dsimp
    rwa [HomotopyCategory.kFlat_quotient_obj_iff]
  · dsimp
    rw [HomotopyCategory.kFlat_quotient_obj_iff]
    exact CochainComplex.kFlat_biprod hK hK

open HomologicalComplex
instance : (L A).functor.IsLocalization (WL A) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      have := (NatIso.isIso_map_iff (iso A) f).1
        (HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _ hf)
      dsimp only [Functor.comp_map] at this
      apply isIso_of_reflects_iso _ ((B A).functor)) (by
      rintro ⟨K₁, hK₁⟩ ⟨K₂, _⟩ (f₀ f₁ : K₁ ⟶ K₂) hf
      exact ⟨⟨K₁.cylinder, kFlat_cylinder _ hK₁⟩,
        cylinder.ι₀ _, cylinder.ι₁ _, cylinder.π _,
        ⟨cylinder.homotopyEquiv K₁ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩,
        cylinder.ι₀_π _, cylinder.ι₁_π _, cylinder.desc f₀ f₁
          (HomotopyCategory.homotopyOfEq _ _ hf),
        cylinder.ι₀_desc _ _ _, cylinder.ι₁_desc _ _ _⟩)

instance : (L A).IsLocalizedEquivalence :=
  (L A).isLocalizedEquivalence_of_isLocalization (WL A)
    (fun _ _ _ hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf) (by
      rintro ⟨K, hK⟩ ⟨L, hL⟩ f hf
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
      obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
      rw [HomotopyCategory.kFlat_quotient_obj_iff] at hK hL
      simp only [MorphismProperty.WKFlat, MorphismProperty.inverseImage_iff, ObjectProperty.ι_obj,
        ObjectProperty.ι_map, HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
      exact ⟨⟨K, hK⟩, ⟨L, hL⟩, f, hf, ⟨Iso.refl _⟩⟩)

instance : (R A).IsLocalizedEquivalence := by
  have : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).HasLocalization := .standard _
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization (R A)
    HomologicalComplexUpToQuasiIso.Qh

instance : (R A).functor.EssSurj := by
  dsimp [R]
  infer_instance

instance : TwoSquare.GuitartExact (iso A).inv :=
  TwoSquare.GuitartExact.quotient (iso A).symm (by
    rintro ⟨K₁, hK₁⟩ K₂ (f₀ f₁ : K₁ ⟶ K₂) hf
    refine ⟨⟨K₁.cylinder, kFlat_cylinder _ hK₁⟩, cylinder.ι₀ _, cylinder.ι₁ _,
      HomotopyCategory.eq_of_homotopy _ _ (cylinder.homotopy₀₁ K₁ (fun n ↦ ⟨n -1, by simp⟩)),
      cylinder.desc f₀ f₁ (HomotopyCategory.homotopyOfEq _ _ hf),
      cylinder.ι₀_desc _ _ _, cylinder.ι₁_desc _ _ _⟩)

end kFlatLocalizerSquare

variable [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

noncomputable def colimitOfShapeFlatResolutionFunctorObj (K : CochainComplex A ℤ) :
    ObjectProperty.flat.cochainComplexMinus.ColimitOfShape ℤ (Λ.resolutionFunctor.obj K) :=
  (Λ.colimitOfShapeResolutionFunctorObj K).ofLE
    (ObjectProperty.monotone_cochainComplexMinus hι)

include hι in
lemma kFlat_resolutionFunctor_obj (K : CochainComplex A ℤ) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat (Λ.resolutionFunctor.obj K) := by
  let e := (Λ.colimitOfShapeResolutionFunctorObj K).ofLE
    ((ObjectProperty.monotone_cochainComplexMinus hι).trans
      (CochainComplex.cochainComplexMinus_flat_le_kFlat A))
  exact CochainComplex.closedUnderColimitsOfShape_kFlat A ℤ e.isColimit e.hF

noncomputable def kFlatResolutionFunctor : CochainComplex A ℤ ⥤ CochainComplex.KFlat A :=
  ObjectProperty.lift _ Λ.resolutionFunctor (Λ.kFlat_resolutionFunctor_obj hι)

noncomputable def kFlatResolutionNatTrans :
    Λ.kFlatResolutionFunctor hι ⋙ CochainComplex.ιKFlat A ⟶ 𝟭 _ :=
  Λ.resolutionNatTrans

instance (K : CochainComplex A ℤ) : QuasiIso ((Λ.kFlatResolutionNatTrans hι).app K) := by
  dsimp [kFlatResolutionNatTrans]
  infer_instance

include Λ hι in
lemma cochainComplex_kFlat_isLeftDerivabilityStructure :
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
  LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat (Λ.kFlatResolutionNatTrans hι)
    (fun _ ↦ by rw [HomologicalComplex.mem_quasiIso_iff]; dsimp; infer_instance)

include Λ hι in
lemma homotopyCategory_kFlat_isLeftDerivabilityStructure :
    (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  have := Λ.cochainComplex_kFlat_isLeftDerivabilityStructure hι
  exact LocalizerMorphism.isLeftDerivabilityStructure_of_isLocalizedEquivalence
    (kFlatLocalizerSquare.iso A)

end LeftResolutions

variable [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

instance [HasFunctorialFlatResolutions A] :
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  let Λ : LeftResolutions (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
  exact Λ.reduced.cochainComplex_kFlat_isLeftDerivabilityStructure (by simp)

instance [HasFunctorialFlatResolutions A] :
    (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  let Λ : LeftResolutions (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
  exact Λ.reduced.homotopyCategory_kFlat_isLeftDerivabilityStructure (by simp)

noncomputable example [HasFunctorialFlatResolutions A] [HasDerivedCategory A] :
    MonoidalCategory (DerivedCategory A) := inferInstance

end CategoryTheory.Abelian
