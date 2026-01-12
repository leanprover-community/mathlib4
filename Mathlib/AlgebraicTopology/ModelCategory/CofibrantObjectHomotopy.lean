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
we introduce the homotopy category `CofibrantObject.π C` of cofibrant objects
in `C`, and we define a cofibrant resolution functor
`CofibrantObject.π.resolution : C ⥤ CofibrantObject.π C`.

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

variable (C) in
/-- The homotopy category of cofibrant objects. -/
abbrev π := Quotient (CofibrantObject.homRel C)

/-- The quotient functor from the category of cofibrant objects to its
homotopy category. -/
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
    HomRel.compClosure_eq_self]
  refine ⟨?_, .rel _ _⟩
  rw [homRel_iff_rightHomotopyRel]
  intro h
  induction h with
  | rel _ _ h => exact h
  | refl => exact .refl _
  | symm _ _ _ h => exact .symm h
  | trans _ _ _ _ _ h h' => exact .trans h h'

instance : (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

instance : CategoryWithWeakEquivalences (CofibrantObject.π C) where
  weakEquivalences := (weakEquivalences _).quotient _

lemma weakEquivalence_toπ_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toπ.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/-- The functor `CofibrantObject C ⥤ π C`, considered as a localizer morphism. -/
def toπLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (CofibrantObject.π C)) where
  functor := toπ
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toπ_map_iff]

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

instance : (toπLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category* D] (L : CofibrantObject.π C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toπ ⋙ L).IsLocalization (weakEquivalences _) := by
  change ((toπLocalizerMorphism C).functor ⋙ L).IsLocalization (weakEquivalences _)
  infer_instance

lemma π.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsCofibrant X') (p : X' ⟶ X), Fibration p ∧ WeakEquivalence p := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

/-- Given `X : C`, this is a cofibrant object `X'` equipped with a
trivial fibration `X' ⟶ X` (see `π.pResolutionObj`). -/
noncomputable def π.resolutionObj (X : C) : C :=
    (exists_resolution X).choose

instance (X : C) : IsCofibrant (π.resolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose

/-- This is the trivial fibration `resolutionObj X ⟶ X` where
`resolutionObj X` is a choice of a cofibrant resolution of `X`. -/
noncomputable def π.pResolutionObj (X : C) : resolutionObj X ⟶ X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Fibration (π.pResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (π.pResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.2

lemma π.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      g ≫ pResolutionObj Y = pResolutionObj X ≫ f := by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- The lifting of a morphism `f : X ⟶ Y` on cofibrant resolutions.
(This is functorial only up to homotopy, see `π.resolution`.) -/
noncomputable def π.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
lemma π.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    resolutionMap f ≫ pResolutionObj Y =
      pResolutionObj X ≫ f :=
  (exists_resolution_map f).choose_spec

@[simp]
lemma π.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_postcomp_iff _ (pResolutionObj Y),
    π.resolutionMap_fac, weakEquivalence_precomp_iff]

lemma π.resolutionObj_hom_ext {X : C} [IsCofibrant X] {Y : C} {f g : X ⟶ resolutionObj Y}
    (h : LeftHomotopyRel (f ≫ pResolutionObj Y) (g ≫ pResolutionObj Y)) :
    toπ.map (homMk f) = toπ.map (homMk g) := by
  apply toπ_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X) (g := pResolutionObj Y)).1 h

/-- The cofibrant resolution functor from a model category to the homotopy category
of cofibrant objects. -/
noncomputable def π.resolution : C ⥤ CofibrantObject.π C where
  obj X := toπ.obj (mk (resolutionObj X))
  map f := toπ.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toπ.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toπ.map_comp]
    refine resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The cofibration resolution functor, as a localizer morphism. -/
@[simps]
noncomputable def π.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (CofibrantObject.π C)) where
  functor := π.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, π.resolution,
      weakEquivalence_toπ_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `π.pResolutionObj`, when applied to already cofibrant objects, gives
a natural transformation `ι ⋙ π.resolution ⟶ toπ`. -/
@[simps]
noncomputable def π.ιCompResolutionNatTrans : ι ⋙ π.resolution (C := C) ⟶ toπ where
  app X := toπ.map { hom := (π.pResolutionObj (ι.obj X)) }
  naturality _ _ f :=  toπ.congr_map (by
    ext : 1
    exact π.resolutionMap_fac f.hom)

instance (X : CofibrantObject C) :
    WeakEquivalence (π.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toπ_map_iff, weakEquivalence_iff_of_objectProperty]
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

/-- The induced functor `CofibrantObject.π C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences. -/
def π.toLocalization : π C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h ↦ (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ ↦ Localization.inverts L (weakEquivalences _) _))

/-- The isomorphism `toπ ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of cofibrant objects factors through the homotopy category
of cofibrant objects. -/
def π.toπCompToLocalizationIso : toπ ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

/-- The natural isomorphism `π.resolution ⋙ π.toLocalization L ⟶ L` when
`L : C ⥤ D` is a localization functor. -/
noncomputable def π.resolutionCompToLocalizationNatTrans :
    π.resolution ⋙ π.toLocalization L ⟶ L where
  app X := L.map (pResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using L.congr_map (π.resolutionMap_fac f)

instance : IsIso (π.resolutionCompToLocalizationNatTrans L) := by
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

instance (X : CofibrantObject C) :
    IsCofibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance

instance {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (CofibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end CofibrantObject

end HomotopicalAlgebra
