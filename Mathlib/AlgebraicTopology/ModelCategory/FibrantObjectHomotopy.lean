/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The homotopy category of fibrant objects

Let `C` be a model category. By using the left homotopy relation,
we introduce the homotopy category `FibrantObject.HoCat C` of fibrant objects
in `C`, and we define a fibrant resolution functor
`FibrantObject.HoCat.resolution : C ⥤ FibrantObject.HoCat C`.

This file was obtained by dualizing the definitions in
`Mathlib/AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace FibrantObject

variable (C) in
/-- The left homotopy relation on the category of fibrant objects. -/
def homRel : HomRel (FibrantObject C) :=
  fun _ _ f g ↦ LeftHomotopyRel f.hom g.hom

lemma homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := Iff.rfl

instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _

instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _

lemma homRel_equivalence_of_isCofibrant_src {X Y : FibrantObject C} [IsCofibrant X.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (LeftHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) ↦ f.hom)

variable (C) in
/-- The homotopy category of fibrant objects. -/
abbrev HoCat := Quotient (FibrantObject.homRel C)

/-- The quotient functor from the category of fibrant objects to its
homotopy category. -/
def toHoCat : FibrantObject C ⥤ HoCat C := Quotient.functor _

lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance

lemma toHoCat_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toHoCat_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    HomRel.compClosure_eq_self, homRel_equivalence_of_isCofibrant_src.eqvGen_eq]

instance : (weakEquivalences (FibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

instance : CategoryWithWeakEquivalences (FibrantObject.HoCat C) where
  weakEquivalences := (weakEquivalences _).quotient _

lemma weakEquivalence_toHoCat_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toHoCat.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/-- The functor `FibrantObject C ⥤ HoCat C`, considered as a localizer morphism. -/
def toHoCatLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (FibrantObject C))
      (weakEquivalences (FibrantObject.HoCat C)) where
  functor := toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

variable (C) in
lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (FibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  let L := (weakEquivalences (FibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.i₀) = L.map (homMk P.i₁) by
    simp only [show f = homMk P.i₀ ≫ homMk h.h by cat_disch,
      show g = homMk P.i₁ ≫ homMk h.h by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.π) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp [← cancel_mono (L.map (homMk P.π)), ← L.map_comp]

instance : (toHoCatLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category* D] (L : FibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toHoCat ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((toHoCatLocalizerMorphism C).functor ⋙ L).IsLocalization _)

lemma HoCat.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsFibrant X') (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
  infer_instance

/-- Given `X : C`, this is a fibrant object `X'` equipped with a
trivial cofibration `X ⟶ X'` (see `HoCat.iResolutionObj`). -/
noncomputable def HoCat.resolutionObj (X : C) : C :=
    (exists_resolution X).choose

instance (X : C) : IsFibrant (HoCat.resolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose

/-- This is a trivial cofibration `X ⟶ resolutionObj X` where
`resolutionObj X` is a choice of a fibrant resolution of `X`. -/
noncomputable def HoCat.iResolutionObj (X : C) : X ⟶ resolutionObj X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Cofibration (HoCat.iResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (HoCat.iResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2

lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      iResolutionObj X ≫ g = f ≫ iResolutionObj Y := by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- A lifting of a morphism `f : X ⟶ Y` on fibrant resolutions.
(This is functorial only up to homotopy, see `HoCat.resolution`.) -/
noncomputable def HoCat.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
lemma HoCat.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    iResolutionObj X ≫ resolutionMap f =
      f ≫ iResolutionObj Y :=
  (exists_resolution_map f).choose_spec

@[simp]
lemma HoCat.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_precomp_iff (iResolutionObj X),
    HoCat.resolutionMap_fac, weakEquivalence_postcomp_iff]

lemma HoCat.resolutionObj_hom_ext {X Y : C} [IsFibrant Y] {f g : resolutionObj X ⟶ Y}
    (h : RightHomotopyRel (iResolutionObj X ≫ f) (iResolutionObj X ≫ g)) :
    toHoCat.map (homMk f) = toHoCat.map (homMk g) := by
  apply toHoCat_map_eq
  rw [homRel_iff_leftHomotopyRel]
  apply RightHomotopyRel.leftHomotopyRel
  rw [← RightHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    (f := iResolutionObj X) (Z := Y)).1 h

/-- A fibrant resolution functor from a model category to the homotopy category
of fibrant objects. -/
noncomputable def HoCat.resolution : C ⥤ FibrantObject.HoCat C where
  obj X := toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The fibrant resolution functor `HoCat.resolution`, as a localizer morphism. -/
@[simps]
noncomputable def HoCat.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (FibrantObject.HoCat C)) where
  functor := HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `HoCat.iResolutionObj`, when applied to already fibrant objects, gives
a natural transformation `toHoCat ⟶ ι ⋙ HoCat.resolution`. -/
@[simps]
noncomputable def HoCat.ιCompResolutionNatTrans : toHoCat ⟶ ι ⋙ HoCat.resolution (C := C) where
  app X := toHoCat.map { hom := (HoCat.iResolutionObj (ι.obj X)) }
  naturality _ _ f :=  toHoCat.congr_map (by
    ext : 1
    exact (HoCat.resolutionMap_fac f.hom).symm )

instance (X : FibrantObject C) :
    WeakEquivalence (HoCat.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toHoCat_map_iff, weakEquivalence_iff_of_objectProperty]
  infer_instance

instance {D : Type*} [Category* D] (L : FibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (Functor.whiskerRight HoCat.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- The induced functor `FibrantObject.HoCat C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences. -/
def HoCat.toLocalization : HoCat C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h ↦ (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ ↦ Localization.inverts L (weakEquivalences _) _))

/-- The isomorphism `toHoCat ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of fibrant objects factors through the homotopy category
of fibrant objects. -/
def HoCat.toHoCatCompToLocalizationIso : toHoCat ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

/-- The natural isomorphism `L ⟶ HoCat.resolution ⋙ HoCat.toLocalization L` when
`L : C ⥤ D` is a localization functor. -/
noncomputable def HoCat.resolutionCompToLocalizationNatTrans :
    L ⟶ HoCat.resolution ⋙ HoCat.toLocalization L where
  app X := L.map (iResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using L.congr_map (HoCat.resolutionMap_fac f).symm

instance : IsIso (HoCat.resolutionCompToLocalizationNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

end

variable (C) in
/-- The inclusion `FibrantObject C ⥤ C`, as a localizer morphism. -/
@[simps]
def localizerMorphism : LocalizerMorphism (weakEquivalences (FibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

open Functor in
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hfib := (weakEquivalences (HoCat C)).Localization
  let Lfibπ : HoCat C ⥤ Hfib := (weakEquivalences (FibrantObject.HoCat C)).Q
  let Lfib : FibrantObject C ⥤ Hfib := toHoCat ⋙ Lfibπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lfib L
  let eF : ι ⋙ L ≅ Lfib ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lfib L F
  let eF' : HoCat.toLocalization L ≅ Lfibπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hfib := (HoCat.localizerMorphismResolution C).localizedFunctor L Lfibπ
  let eG : HoCat.resolution ⋙ Lfibπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lfibπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lfib (weakEquivalences (FibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lfibπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hfib ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lfib (weakEquivalences _) Lfib (ι ⋙ HoCat.resolution ⋙ Lfibπ) _ _
        (asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lfibπ) ≪≫ associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)).symm)
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lfib L F

instance (X : FibrantObject C) :
    IsFibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (FibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end FibrantObject

end HomotopicalAlgebra
