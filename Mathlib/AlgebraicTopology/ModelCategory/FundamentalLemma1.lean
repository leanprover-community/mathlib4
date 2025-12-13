/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The fundamental lemma of homotopical algebra

In this file, we show that if `C` is a model category, then
the localization of the full subcategory of cofibrant objects in `C` with
respect to weak equivalences identifies to the localization of `C` with
respect to weak equivalences.

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C] [ModelCategory C]

namespace CofibrantObject

def homRel : HomRel (CofibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

lemma homRel_iff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

abbrev π := Quotient (CofibrantObject.homRel C)

variable {C}

def toπ : CofibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toπ.map f = toπ.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toπ_map_eq_iff {X Y : CofibrantObject C} [IsFibrant Y.1] (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g := by
  dsimp [toπ]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    compClosure_homRel]
  exact (RightHomotopyRel.equivalence _ _).eqvGen_iff

end CofibrantObject

namespace FibrantObject

def homRel : HomRel (FibrantObject C) :=
  fun X Y ↦ LeftHomotopyRel (X := X.1) (Y := Y.1)

lemma homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

abbrev π := Quotient (FibrantObject.homRel C)

variable {C}

def toπ : FibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toπ.map f = toπ.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toπ_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.1] (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g := by
  dsimp [toπ]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    compClosure_homRel]
  exact (LeftHomotopyRel.equivalence _ _).eqvGen_iff

end FibrantObject

namespace CofibrantObject

instance : (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    rw [← weakEquivalence_iff, ← weakEquivalence_iff, weakEquivalence_iff_ι_map,
      weakEquivalence_iff_ι_map]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff
  compClosure_eq_self := compClosure_homRel C

instance : CategoryWithWeakEquivalences (CofibrantObject.π C) where
  weakEquivalences := (weakEquivalences _).quotient _

variable {C} in
lemma weakEquivalence_toπ_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toπ.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

def toπLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (CofibrantObject.π C)) where
  functor := toπ
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toπ_map_iff]

lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (CofibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [← h.h₀, ← h.h₁]
    change L.map (homMk h.h ≫ homMk P.p₀) = L.map (homMk h.h ≫ homMk P.p₁)
    simp only [Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    rw [← weakEquivalence_iff]
    rw [weakEquivalence_iff_ι_map]
    change WeakEquivalence P.ι
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]

instance : (toπLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category D] (L : CofibrantObject.π C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toπ ⋙ L).IsLocalization (weakEquivalences _) := by
  change ((toπLocalizerMorphism C).functor ⋙ L).IsLocalization (weakEquivalences _)
  infer_instance

end CofibrantObject

namespace FibrantObject

-- dualize

end FibrantObject

namespace CofibrantObject

variable {C}

def π.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsCofibrant X') (p : X' ⟶ X), Fibration p ∧ WeakEquivalence p := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

noncomputable def π.resolutionObj (X : C) : CofibrantObject C :=
    ⟨(exists_resolution X).choose,
      (exists_resolution X).choose_spec.choose⟩

noncomputable def π.pResolutionObj (X : C) : ι.obj (resolutionObj X) ⟶ X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Fibration (π.pResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (π.pResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.2

def π.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      ι.map g ≫ pResolutionObj Y = pResolutionObj X ≫ f := by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

noncomputable def π.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
lemma π.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    ι.map (resolutionMap f) ≫ pResolutionObj Y =
      pResolutionObj X ≫ f :=
  (exists_resolution_map f).choose_spec

@[simp]
lemma π.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [weakEquivalence_iff_ι_map,
    ← weakEquivalence_postcomp_iff _ (pResolutionObj Y),
    π.resolutionMap_fac, weakEquivalence_precomp_iff]

lemma π.resolutionObj_hom_ext {X : CofibrantObject C} {Y : C} {f g : X ⟶ resolutionObj Y}
    (h : LeftHomotopyRel (ι.map f ≫ pResolutionObj Y) (ι.map g ≫ pResolutionObj Y)) :
    toπ.map f = toπ.map g := by
  apply toπ_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X.obj) (g := pResolutionObj Y)).1 h

noncomputable def π.resolution : C ⥤ CofibrantObject.π C where
  obj X := toπ.obj (resolutionObj X)
  map f := toπ.map (resolutionMap f)
  map_id X := by
    rw [← toπ.map_id]
    apply resolutionObj_hom_ext
    rw [resolutionMap_fac, Category.comp_id, ι.map_id, Category.id_comp]
    exact .refl _
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toπ.map_comp]
    apply resolutionObj_hom_ext
    rw [resolutionMap_fac, ι.map_comp_assoc, resolutionMap_fac, resolutionMap_fac_assoc]
    exact .refl _

variable (C) in
@[simps]
noncomputable def π.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (CofibrantObject.π C)) where
  functor := π.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, π.resolution,
      weakEquivalence_toπ_map_iff, weakEquivalence_resolutionMap_iff] using h

@[simps]
noncomputable def π.ιCompResolutionNatTrans : ι ⋙ π.resolution (C := C) ⟶ toπ where
  app X := toπ.map (pResolutionObj (ι.obj X))
  naturality _ _ f := toπ.congr_map (π.resolutionMap_fac (ι.map f))

instance π.weakEquivalence_ιCompResolutionNatTrans_app (X : CofibrantObject C) :
    WeakEquivalence (ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toπ_map_iff, weakEquivalence_iff_ι_map]
  dsimp
  infer_instance

instance {D : Type*} [Category D] (L : CofibrantObject.π C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (Functor.whiskerRight π.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

def π.toLocalization : π C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h ↦ (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ ↦ Localization.inverts L (weakEquivalences _) _))

def π.toπCompToLocalizationIso : toπ ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

noncomputable def π.resolutionCompToLocalizationNatTrans :
    π.resolution ⋙ π.toLocalization L ⟶ L where
  app X := L.map (pResolutionObj X)
  naturality _ _ f := by simpa using L.congr_map (π.resolutionMap_fac f)

instance : IsIso (π.resolutionCompToLocalizationNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

end

end CofibrantObject

namespace FibrantObject

-- dualize

end FibrantObject


namespace CofibrantObject

@[simps]
def localizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

open Functor in
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hcof := (weakEquivalences (π C)).Localization
  let Lcofπ : π C ⥤ Hcof := (weakEquivalences (CofibrantObject.π C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toπ ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let eF' : π.toLocalization L ≅ Lcofπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (π.toπCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hcof := (π.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : π.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (π.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting L (weakEquivalences C)
      (π.resolution ⋙ π.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C))
        (ι ⋙ π.resolution ⋙ Lcofπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof (ι ⋙ π.resolution ⋙ Lcofπ) _ _
      ((asIso (whiskerRight π.ιCompResolutionNatTrans Lcofπ)).symm ≪≫
          associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _) (π.resolution ⋙ π.toLocalization L) L _ _
      (asIso (π.resolutionCompToLocalizationNatTrans L)))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

instance {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ι ⋙ L).IsLocalization (weakEquivalences _) := by
  change ((localizerMorphism C).functor ⋙ L).IsLocalization _
  infer_instance

end CofibrantObject

namespace FibrantObject

-- dualize

end FibrantObject

end HomotopicalAlgebra
