/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The homotopy category of cofibrant objects

Let `C` be a model category. By using the right homotopy relation,
we introduce the homotopy category `CofibrantObject.HoCat C` of cofibrant objects
in `C`, and we define a cofibrant resolution functor
`CofibrantObject.HoCat.resolution : C ⥤ CofibrantObject.HoCat C`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace CofibrantObject

variable (C) in
/-- The right homotopy relation on the category of cofibrant objects. -/
def homRel : HomRel (CofibrantObject C) :=
  fun _ _ f g ↦ RightHomotopyRel f.hom g.hom

lemma homRel_iff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel f.hom g.hom := Iff.rfl

instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _

instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _

lemma homRel_equivalence_of_isFibrant_tgt {X Y : CofibrantObject C} [IsFibrant Y.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (RightHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) ↦ f.hom)

variable (C) in
/-- The homotopy category of cofibrant objects. -/
abbrev HoCat := Quotient (CofibrantObject.homRel C)

/-- The quotient functor from the category of cofibrant objects to its
homotopy category. -/
def toHoCat : CofibrantObject C ⥤ HoCat C := Quotient.functor _

lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance

lemma toHoCat_map_eq {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toHoCat_map_eq_iff {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    HomRel.compClosure_eq_self, homRel_equivalence_of_isFibrant_tgt.eqvGen_eq]

instance : (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

instance : CategoryWithWeakEquivalences (CofibrantObject.HoCat C) where
  weakEquivalences := (weakEquivalences _).quotient _

lemma weakEquivalence_toHoCat_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toHoCat.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/-- The functor `CofibrantObject C ⥤ HoCat C`, considered as a localizer morphism. -/
def toHoCatLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (CofibrantObject.HoCat C)) where
  functor := toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

variable (C) in
lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (CofibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]

instance : (toHoCatLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category* D] (L : CofibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toHoCat ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((toHoCatLocalizerMorphism C).functor ⋙ L).IsLocalization _)

lemma HoCat.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsCofibrant X') (p : X' ⟶ X), Fibration p ∧ WeakEquivalence p := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

/-- Given `X : C`, this is a cofibrant object `X'` equipped with a
trivial fibration `X' ⟶ X` (see `HoCat.pResolutionObj`). -/
noncomputable def HoCat.resolutionObj (X : C) : C :=
    (exists_resolution X).choose

instance (X : C) : IsCofibrant (HoCat.resolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose

/-- This is a trivial fibration `resolutionObj X ⟶ X` where
`resolutionObj X` is a choice of a cofibrant resolution of `X`. -/
noncomputable def HoCat.pResolutionObj (X : C) : resolutionObj X ⟶ X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Fibration (HoCat.pResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (HoCat.pResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2

lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      g ≫ pResolutionObj Y = pResolutionObj X ≫ f := by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- A lifting of a morphism `f : X ⟶ Y` on cofibrant resolutions.
(This is functorial only up to homotopy, see `HoCat.resolution`.) -/
noncomputable def HoCat.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
lemma HoCat.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    resolutionMap f ≫ pResolutionObj Y =
      pResolutionObj X ≫ f :=
  (exists_resolution_map f).choose_spec

@[simp]
lemma HoCat.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_postcomp_iff _ (pResolutionObj Y),
    HoCat.resolutionMap_fac, weakEquivalence_precomp_iff]

lemma HoCat.resolutionObj_hom_ext {X : C} [IsCofibrant X] {Y : C} {f g : X ⟶ resolutionObj Y}
    (h : LeftHomotopyRel (f ≫ pResolutionObj Y) (g ≫ pResolutionObj Y)) :
    toHoCat.map (homMk f) = toHoCat.map (homMk g) := by
  apply toHoCat_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X) (g := pResolutionObj Y)).injective h

/-- A cofibrant resolution functor from a model category to the homotopy category
of cofibrant objects. -/
noncomputable def HoCat.resolution : C ⥤ CofibrantObject.HoCat C where
  obj X := toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The cofibration resolution functor `HoCat.resolution`, as a localizer morphism. -/
@[simps]
noncomputable def HoCat.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (CofibrantObject.HoCat C)) where
  functor := HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `HoCat.pResolutionObj`, when applied to already cofibrant objects, gives
a natural transformation `ι ⋙ HoCat.resolution ⟶ toπ`. -/
@[simps]
noncomputable def HoCat.ιCompResolutionNatTrans :
    ι ⋙ HoCat.resolution (C := C) ⟶ toHoCat where
  app X := toHoCat.map { hom := (HoCat.pResolutionObj (ι.obj X)) }
  naturality _ _ f :=  toHoCat.congr_map (by
    ext : 1
    exact HoCat.resolutionMap_fac f.hom)

instance (X : CofibrantObject C) :
    WeakEquivalence (HoCat.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toHoCat_map_iff, weakEquivalence_iff_of_objectProperty]
  infer_instance

instance {D : Type*} [Category* D] (L : CofibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (Functor.whiskerRight HoCat.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- The induced functor `CofibrantObject.HoCat C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences. -/
def HoCat.toLocalization : HoCat C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h ↦ (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ ↦ Localization.inverts L (weakEquivalences _) _))

/-- The isomorphism `toHoCat ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of cofibrant objects factors through the homotopy category
of cofibrant objects. -/
def HoCat.toπCompToLocalizationIso : toHoCat ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

/-- The natural isomorphism `HoCat.resolution ⋙ HoCat.toLocalization L ⟶ L` when
`L : C ⥤ D` is a localization functor. -/
noncomputable def HoCat.resolutionCompToLocalizationNatTrans :
    HoCat.resolution ⋙ HoCat.toLocalization L ⟶ L where
  app X := L.map (pResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using L.congr_map (HoCat.resolutionMap_fac f)

instance : IsIso (HoCat.resolutionCompToLocalizationNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

end

variable (C) in
/-- The inclusion `CofibrantObject C ⥤ C`, as a localizer morphism. -/
@[simps]
def localizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

open Functor in
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hcof := (weakEquivalences (HoCat C)).Localization
  let Lcofπ : HoCat C ⥤ Hcof := (weakEquivalences (CofibrantObject.HoCat C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toHoCat ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let eF' : HoCat.toLocalization L ≅ Lcofπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toπCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hcof := (HoCat.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : HoCat.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lcofπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof (ι ⋙ HoCat.resolution ⋙ Lcofπ) _ _
      ((asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lcofπ)).symm ≪≫
          associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

instance (X : CofibrantObject C) :
    IsCofibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (CofibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end CofibrantObject

end HomotopicalAlgebra
