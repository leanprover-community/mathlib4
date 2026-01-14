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
# The homotopy category of fibrant objects

Let `C` be a model category. By using the left homotopy relation,
we introduce the homotopy category `FibrantObject.π C` of fibrant objects
in `C`, and we define a fibrant resolution functor
`FibrantObject.π.resolution : C ⥤ FibrantObject.π C`.

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

variable (C) in
/-- The homotopy category of fibrant objects. -/
abbrev π := Quotient (FibrantObject.homRel C)

/-- The quotient functor from the category of fibrant objects to its
homotopy category. -/
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
    HomRel.compClosure_eq_self]
  refine ⟨?_, .rel _ _⟩
  rw [homRel_iff_leftHomotopyRel]
  intro h
  induction h with
  | rel _ _ h => exact h
  | refl => exact .refl _
  | symm _ _ _ h => exact .symm h
  | trans _ _ _ _ _ h h' => exact .trans h h'

instance : (weakEquivalences (FibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff

instance : CategoryWithWeakEquivalences (FibrantObject.π C) where
  weakEquivalences := (weakEquivalences _).quotient _

lemma weakEquivalence_toπ_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toπ.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/-- The functor `FibrantObject C ⥤ π C`, considered as a localizer morphism. -/
def toπLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (FibrantObject C))
      (weakEquivalences (FibrantObject.π C)) where
  functor := toπ
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toπ_map_iff]

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

instance : (toπLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category* D] (L : FibrantObject.π C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toπ ⋙ L).IsLocalization (weakEquivalences _) := by
  change ((toπLocalizerMorphism C).functor ⋙ L).IsLocalization (weakEquivalences _)
  infer_instance

lemma π.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsFibrant X') (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
  infer_instance

/-- Given `X : C`, this is a fibrant object `X'` equipped with a
trivial cofibration `X ⟶ X'` (see `π.iResolutionObj`). -/
noncomputable def π.resolutionObj (X : C) : C :=
    (exists_resolution X).choose

instance (X : C) : IsFibrant (π.resolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose

/-- This is the trivial cofibration `X ⟶ resolutionObj X` where
`resolutionObj X` is a choice of a fibrant resolution of `X`. -/
noncomputable def π.iResolutionObj (X : C) : X ⟶ resolutionObj X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Cofibration (π.iResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (π.iResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.2

lemma π.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      iResolutionObj X ≫ g = f ≫ iResolutionObj Y := by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- The lifting of a morphism `f : X ⟶ Y` on fibrant resolutions.
(This is functorial only up to homotopy, see `π.resolution`.) -/
noncomputable def π.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
lemma π.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    iResolutionObj X ≫ resolutionMap f =
      f ≫ iResolutionObj Y :=
  (exists_resolution_map f).choose_spec

@[simp]
lemma π.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_precomp_iff (iResolutionObj X),
    π.resolutionMap_fac, weakEquivalence_postcomp_iff]

lemma π.resolutionObj_hom_ext {X Y : C} [IsFibrant Y] {f g : resolutionObj X ⟶ Y}
    (h : RightHomotopyRel (iResolutionObj X ≫ f) (iResolutionObj X ≫ g)) :
    toπ.map (homMk f) = toπ.map (homMk g) := by
  apply toπ_map_eq
  rw [homRel_iff_leftHomotopyRel]
  apply RightHomotopyRel.leftHomotopyRel
  rw [← RightHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    (f := iResolutionObj X) (Z := Y)).1 h

/-- The fibrant resolution functor from a model category to the homotopy category
of fibrant objects. -/
noncomputable def π.resolution : C ⥤ FibrantObject.π C where
  obj X := toπ.obj (mk (resolutionObj X))
  map f := toπ.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toπ.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toπ.map_comp]
    refine resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The fibration resolution functor, as a localizer morphism. -/
@[simps]
noncomputable def π.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (FibrantObject.π C)) where
  functor := π.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, π.resolution,
      weakEquivalence_toπ_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

end FibrantObject

end HomotopicalAlgebra
