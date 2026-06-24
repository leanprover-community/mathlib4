/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.GuitartExact.Quotient
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# The injective derivability structure

-/

@[expose] public section

universe w₁ w₂

open HomotopicalAlgebra CategoryTheory Limits ZeroObject Category

variable (C : Type*) [Category C] [Abelian C]
  {H : Type*} [Category H]

namespace CategoryTheory

abbrev InjectiveObject := ObjectProperty.FullSubcategory (fun (X : C) => Injective X)

namespace InjectiveObject

instance closedUnderLimitsOfShapeDiscrete (J : Type*) :
    ObjectProperty.IsClosedUnderLimitsOfShape (fun (X : C) => Injective X) (Discrete J) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have : HasLimit p.diag := ⟨_, p.isLimit⟩
    let X := fun j => p.diag.obj ⟨j⟩
    let e := Discrete.natIsoFunctor (F := p.diag)
    have : HasProduct X := hasLimit_of_iso e
    have : HasLimit (Discrete.functor (p.diag.obj ∘ Discrete.mk)) := by
      change HasProduct X
      infer_instance
    have : ∀ j, Injective (X j) := fun j => p.prop_diag_obj ⟨j⟩
    have e' : ∏ᶜ X ≅ Y := IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      ((IsLimit.postcomposeHomEquiv e _).symm p.isLimit)
    exact Injective.of_iso e' inferInstance

instance : HasFiniteProducts (InjectiveObject C) where
  out n := by infer_instance

instance : HasFiniteBiproducts (InjectiveObject C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance : HasBinaryBiproducts (InjectiveObject C) := hasBinaryBiproducts_of_finite_biproducts _

instance : HasZeroObject (InjectiveObject C) where
  zero := by
    refine ⟨⟨0, inferInstance⟩, ?_⟩
    rw [IsZero.iff_id_eq_zero]
    ext : 1
    apply id_zero

abbrev ι : InjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : InjectiveObject C) : Injective ((ι C).obj X) := X.2

instance (X : InjectiveObject C) : Injective X.obj := X.2

instance (X : HomotopyCategory.Plus (InjectiveObject C)) (n : ℤ) :
    Injective (((ι C).mapHomotopyCategoryPlus.obj X).obj.as.X n) := by
  change Injective ((ι C).obj (X.obj.as.X n))
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (K : CochainComplex.Plus (InjectiveObject C)) :
    CochainComplex.IsKInjective
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K.obj) := by
  obtain ⟨K, n, hn⟩ := K
  let L := ((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K
  have (n : ℤ) : Injective (L.X n) := by dsimp [L]; infer_instance
  exact CochainComplex.isKInjective_of_injective L n

end InjectiveObject

end CategoryTheory

namespace CochainComplex.Plus

variable {C}

lemma exists_injective_resolution [EnoughInjectives C]
    (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsStrictlyGE n] :
    ∃ (L : CochainComplex.Plus (InjectiveObject C)) (_ : L.obj.IsStrictlyGE n)
      (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L),
        quasiIso C i := by
  obtain ⟨L, i, _, _, _⟩ := modelCategoryQuillen.exists_quasiIso_injective K.obj n
  let L' : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ L inferInstance
  have hL' : L'.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    ext
    exact (L.isZero_of_isStrictlyGE n i).eq_of_src _ _
  exact ⟨⟨L', n, hL'⟩, hL', ObjectProperty.homMk i, by assumption⟩

end CochainComplex.Plus

namespace DerivedCategory.Plus

variable {C} [HasDerivedCategory C]

lemma exists_injective_resolution [EnoughInjectives C] (K : DerivedCategory.Plus C)
    (n : ℤ) [K.IsGE n] :
    ∃ (L : CochainComplex.Plus (InjectiveObject C)) (_ : L.obj.IsStrictlyGE n),
      Nonempty (DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj L) ≅ K) := by
  have : K.obj.IsGE n := (K.isGE_ι_obj_iff n).2 (by assumption)
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K.obj n
  obtain ⟨M, _, i, hi⟩ :=
    CochainComplex.Plus.exists_injective_resolution ⟨L, ⟨n, inferInstance⟩⟩ n
  have : QuasiIso i.hom := by assumption
  exact ⟨M, inferInstance,
    ⟨DerivedCategory.Plus.ι.preimageIso ((asIso (DerivedCategory.Q.map i.hom)).symm ≪≫ e.symm)⟩⟩

end DerivedCategory.Plus

namespace CochainComplex.Plus

@[simps]
def localizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (quasiIso C) where
  functor := (InjectiveObject.ι C).mapCochainComplexPlus
  map := by rfl

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance (K : Plus (InjectiveObject C)) (n : ℤ) :
    Injective (K.obj.X n).obj :=
  (K.obj.X n).property

variable [EnoughInjectives C]

open modelCategoryQuillen

instance (K : FibrantObject (Plus C)) (n : ℤ) :
    Injective (K.obj.obj.X n) := by
  obtain ⟨K, hK⟩ := K
  rw [fibrantObjects, modelCategoryQuillen.isFibrant_iff] at hK
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
def fibrantObjectEquivalence :
    Plus (InjectiveObject C) ≌ FibrantObject (Plus C) where
  functor := ObjectProperty.lift _ (InjectiveObject.ι C).mapCochainComplexPlus (fun K ↦ by
    dsimp [fibrantObjects]
    rw [modelCategoryQuillen.isFibrant_iff]
    intro n
    dsimp
    infer_instance)
  inverse := ObjectProperty.lift _
    (HomologicalComplex.liftFunctorObjectProperty _ (FibrantObject.ι ⋙ Plus.ι C)
      (fun K n ↦ by dsimp; infer_instance)) (by
        rintro ⟨⟨K, n, hn⟩, _⟩
        refine ⟨n, ?_⟩
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]
        ext
        apply (K.isZero_of_isStrictlyGE n i hi).eq_of_tgt)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def fibrantObjectLocalizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (weakEquivalences (FibrantObject (Plus C))) where
  functor := (fibrantObjectEquivalence C).functor
  map := by rfl

instance : (fibrantObjectLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

set_option backward.defeqAttrib.useBackward true in
instance : (fibrantObjectLocalizerMorphism C).functor.IsEquivalence := by
  dsimp; infer_instance

instance : (localizerMorphism C).IsRightDerivabilityStructure := by
  rw [LocalizerMorphism.isRightDerivabilityStructure_iff_of_equivalences
    (T := localizerMorphism C) (B := FibrantObject.localizerMorphism (Plus C))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  exact inferInstanceAs (FibrantObject.localizerMorphism (Plus C)).IsRightDerivabilityStructure

instance : (localizerMorphism C).arrow.HasRightResolutions := by
  rw [LocalizerMorphism.hasRightResolutions_arrow_iff_of_equivalences
    (T := localizerMorphism C) (B := FibrantObject.localizerMorphism (Plus C))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  exact inferInstanceAs (FibrantObject.localizerMorphism (Plus C)).arrow.HasRightResolutions

end CochainComplex.Plus


end

end HomotopyCategory.Plus
