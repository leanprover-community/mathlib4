/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.BifunctorTriangulated
public import Mathlib.Algebra.Homology.BifunctorColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MonoidalTriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Devissage
public import Mathlib.Algebra.Homology.HomotopyCategory.PreservesQuasiIso
public import Mathlib.Algebra.Homology.LeftResolution.CochainComplex
public import Mathlib.Algebra.Homology.LeftResolution.Reduced
public import Mathlib.Algebra.Homology.DerivedCategory.Monoidal
public import Mathlib.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.GuitartExact.Quotient

/-!
# Flat objects and K-flat complexes

-/

@[expose] public section

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

set_option backward.isDefEq.respectTransparency false in
instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨_, isZero_zero _, by
    rw [kFlat_iff_preservesQuasiIso]
    constructor
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← id_tensorHom_id, id_zero, MonoidalPreadditive.zero_tensor]
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← id_tensorHom_id, id_zero, MonoidalPreadditive.tensor_zero]⟩

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    rw [ObjectProperty.prop_shift_iff, kFlat_iff_preservesQuasiIso]
    constructor
    · exact (preservesQuasiIso.prop_iff_of_iso
        ((curriedTensor A).map₂CochainComplexObjShiftIso _ _)).2
        (hK.1.comp (preservesQuasiIso_shiftFunctor A n))
    · exact (preservesQuasiIso.prop_iff_of_iso
        ((curriedTensor A).map₂CochainComplexFlipObjShiftIso _ _)).2
        (hK.2.comp (preservesQuasiIso_shiftFunctor A n))⟩

lemma kFlat_shift_iff (K : CochainComplex A ℤ) (n : ℤ) :
    (quasiIso A (.up ℤ)).kFlat (K⟦n⟧) ↔ (quasiIso A (.up ℤ)).kFlat K := by
  apply ObjectProperty.prop_shift_iff_of_isStableUnderShift

variable (A) in
instance closedUnderColimitsOfShape_kFlat (J : Type*) [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).obj X)] :
    (quasiIso A (.up ℤ)).kFlat.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    rw [kFlat_iff_preservesQuasiIso]
    have hJ := isStableUnderColimitsOfShape_preservesQuasiIso A A (.up ℤ) (.up ℤ) J
    constructor
    · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)) :=
        inferInstanceAs (PreservesColimitsOfShape _
          (Functor.map₂CochainComplex _))
      exact ObjectProperty.prop_of_isColimit _
        ((isColimitOfPreserves (curriedTensor _) p.isColimit))
        (fun j ↦ (p.prop_diag_obj j).1)
    · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)).flip :=
        inferInstanceAs (PreservesColimitsOfShape _
          (Functor.map₂CochainComplex _).flip)
      exact ObjectProperty.prop_of_isColimit _
        ((isColimitOfPreserves (curriedTensor _).flip p.isColimit))
        (fun j ↦ (p.prop_diag_obj j).2)

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

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts where
  of_retract {K L} e hL := by
    have : (subcategoryAcyclic A).IsStableUnderRetracts := inferInstance
    rw [kFlat_iff_preserves_acyclic] at hL ⊢
    intro Z hZ
    exact ⟨ObjectProperty.prop_of_retract _ (e.map (tensorRight Z)) (hL Z hZ).1,
      ObjectProperty.prop_of_retract _ (e.map (tensorLeft Z)) (hL Z hZ).2⟩

end HomotopyCategory

namespace CochainComplex

variable {A}

open HomologicalComplex

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts where
  of_retract e h := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff] at h ⊢
    exact ObjectProperty.prop_of_retract _ (e.map (HomotopyCategory.quotient _ _)) h

variable (A) in
instance closedUnderLimitsOfShape_discrete_kFlat (J : Type) [Finite J] :
    (quasiIso A (.up ℤ)).kFlat.IsClosedUnderLimitsOfShape (Discrete J) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    rw [← HomotopyCategory.kFlat_quotient_obj_iff]
    refine ObjectProperty.prop_of_isLimit _
      ((isLimitOfPreserves (HomotopyCategory.quotient _ _) p.isLimit)) (fun j ↦ ?_)
    dsimp
    rw [HomotopyCategory.kFlat_quotient_obj_iff]
    apply p.prop_diag_obj

lemma kFlat_prod {K L : CochainComplex A ℤ} (hK : (quasiIso A (.up ℤ)).kFlat K)
    (hL : (quasiIso A (.up ℤ)).kFlat L) :
    (quasiIso A (.up ℤ)).kFlat (K ⨯ L) :=
  ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair K L)) (by rintro (_ | _) <;> assumption)

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
        (map₂HomologicalComplexObjSingleIso (curriedTensor A) X)
    · exact preservesQuasiIso.prop_iff_of_iso
        (map₂HomologicalComplexFlipObjSingleIso (curriedTensor A) X)

instance : (ObjectProperty.flat (A := A)).ContainsZero where
  exists_zero := ⟨0, isZero_zero A, by
    rw [← kFlat_single_obj_iff_flat _ 0]
    apply ObjectProperty.prop_of_isZero
    apply Functor.map_isZero
    apply Limits.isZero_zero⟩

variable (A) in
instance closedUnderLimitsOfShape_discrete_flat (J : Type) [Finite J] :
    (ObjectProperty.flat (A := A)).IsClosedUnderLimitsOfShape (Discrete J) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    rw [← kFlat_single_obj_iff_flat _ 0]
    refine ObjectProperty.prop_of_isLimit _
      (isLimitOfPreserves (single _ (.up ℤ) 0) p.isLimit) (fun j ↦ ?_)
    simpa only [← kFlat_single_obj_iff_flat _ 0] using p.prop_diag_obj j

instance : HasFiniteProducts (ObjectProperty.flat (A := A)).FullSubcategory where
  out n := by
    apply hasLimitsOfShape_of_closedUnderLimits

instance : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance : (ObjectProperty.flat (A := A)).IsStableUnderRetracts where
  of_retract e h := by
    rw [← kFlat_single_obj_iff_flat _ 0] at h ⊢
    exact ObjectProperty.prop_of_retract _ (e.map ((single _ (.up ℤ) 0))) h

variable (A) in
lemma closedUnderColimitsOfShape_flat (J : Type*) [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).obj X)] :
    (ObjectProperty.flat (A := A)).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    simp only [← kFlat_single_obj_iff_flat _ 0]
    refine ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (single _ (.up ℤ) 0) p.isColimit) (fun j ↦ ?_)
    simpa only [← kFlat_single_obj_iff_flat _ 0] using p.prop_diag_obj j

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
  refine ObjectProperty.prop_of_isColimit _
    (K.isColimitCoconeStupidFiltrationGE.whiskerEquivalence Int.opEquivalence.symm)
    (fun i ↦ kFlat_of_bounded_of_flat
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-i))) (-i) b (fun n ↦ ?_))
  by_cases hn : -i ≤ n
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    let φ := (ιStupidTrunc K (ComplexShape.embeddingUpIntGE (-i))).f n
    have : IsIso φ := isIso_ιStupidTrunc_f K _ (i := k) (by dsimp; omega)
    exact ObjectProperty.prop_of_iso _ (asIso φ).symm (hK n)
  · apply ObjectProperty.prop_of_isZero
    apply isZero_stupidTrunc_X K (ComplexShape.embeddingUpIntGE (-i)) n
    intro
    dsimp
    lia

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
  (Λ : LeftResolution ι) [Λ.F.PreservesZeroMorphisms]
  (hι : ι.essImage ≤ ObjectProperty.flat)


namespace LeftResolution

namespace kFlatLocalizerSquare

variable (A)

def L : LocalizerMorphism (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).WKFlat
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).WKFlat where
  functor := ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ HomotopyCategory.quotient _ _)
    (fun ⟨K, hK⟩ ↦ by
      dsimp
      rwa [HomotopyCategory.kFlat_quotient_obj_iff])
  map := by
    rintro ⟨K, hK⟩ ⟨L, hL⟩ ⟨f : K ⟶ L⟩ hf
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
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient _ _).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g, by cat_disch⟩

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

set_option backward.isDefEq.respectTransparency false in
instance : (L A).functor.IsLocalization (WL A) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      have := (NatIso.isIso_map_iff (iso A) f).1
        (HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _ hf)
      dsimp only [Functor.comp_map] at this
      apply isIso_of_reflects_iso _ ((B A).functor)) (by
      rintro ⟨K₁, hK₁⟩ ⟨K₂, hK₂⟩ (f₀ f₁) hf
      refine ⟨⟨K₁.cylinder, kFlat_cylinder _ hK₁⟩,
        ObjectProperty.homMk (cylinder.ι₀ _),
        ObjectProperty.homMk (cylinder.ι₁ _),
        ObjectProperty.homMk (cylinder.π _),
        ⟨cylinder.homotopyEquiv K₁ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩,
        by cat_disch, by cat_disch,
        ObjectProperty.homMk (cylinder.desc f₀.hom f₁.hom
          (HomotopyCategory.homotopyOfEq _ _ ((ObjectProperty.ι _).congr_map hf))),
        by cat_disch, by cat_disch⟩)

instance : (L A).IsLocalizedEquivalence :=
  (L A).isLocalizedEquivalence_of_isLocalization (WL A)
    (fun _ _ _ hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf) (by
      rintro ⟨K, hK⟩ ⟨L, hL⟩ f hf
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
      rw [HomotopyCategory.kFlat_quotient_obj_iff] at hK hL
      obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
      obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
      refine ⟨⟨K, hK⟩, ⟨L, hL⟩, ObjectProperty.homMk f, ?_, ⟨Iso.refl _⟩⟩
      simpa [MorphismProperty.WKFlat, HomotopyCategory.quotient_map_mem_quasiIso_iff] using hf)

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
    refine ⟨⟨K₁.cylinder, kFlat_cylinder _ hK₁⟩, ObjectProperty.homMk (cylinder.ι₀ _),
      ObjectProperty.homMk (cylinder.ι₁ _), ?_,
      cylinder.desc f₀ f₁ (HomotopyCategory.homotopyOfEq _ _ hf),
      cylinder.ι₀_desc _ _ _, cylinder.ι₁_desc _ _ _⟩
    ext : 1
    exact HomotopyCategory.eq_of_homotopy _ _ (cylinder.homotopy₀₁ K₁ (fun n ↦ ⟨n -1, by simp⟩)))

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
  exact ObjectProperty.prop_of_isColimit _ e.isColimit e.prop_diag_obj

noncomputable def kFlatResolutionFunctor : CochainComplex A ℤ ⥤ CochainComplex.KFlat A :=
  ObjectProperty.lift _ Λ.resolutionFunctor (Λ.kFlat_resolutionFunctor_obj hι)

noncomputable def kFlatResolutionNatTrans :
    Λ.kFlatResolutionFunctor hι ⋙ CochainComplex.ιKFlat A ⟶ 𝟭 _ :=
  Λ.resolutionNatTrans

set_option backward.isDefEq.respectTransparency false in
instance (K : CochainComplex A ℤ) : QuasiIso ((Λ.kFlatResolutionNatTrans hι).app K) := by
  dsimp [kFlatResolutionNatTrans]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
include Λ hι in
lemma cochainComplex_kFlat_isLeftDerivabilityStructure :
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
  LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat (Λ.kFlatResolutionNatTrans hι)
    (fun _ ↦ by rw [HomologicalComplex.mem_quasiIso_iff]; dsimp; infer_instance) rfl

include Λ hι in
lemma homotopyCategory_kFlat_isLeftDerivabilityStructure :
    (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  have := Λ.cochainComplex_kFlat_isLeftDerivabilityStructure hι
  exact LocalizerMorphism.isLeftDerivabilityStructure_of_isLocalizedEquivalence
    (kFlatLocalizerSquare.iso A)

end LeftResolution

variable [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

instance [HasFunctorialFlatResolution A] :
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  let Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
  exact Λ.reduced.cochainComplex_kFlat_isLeftDerivabilityStructure (by simp)

instance [HasFunctorialFlatResolution A] :
    (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  let Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
  exact Λ.reduced.homotopyCategory_kFlat_isLeftDerivabilityStructure (by simp)

noncomputable example [HasFunctorialFlatResolution A] [HasDerivedCategory A] :
    MonoidalCategory (DerivedCategory A) := inferInstance

end CategoryTheory.Abelian
