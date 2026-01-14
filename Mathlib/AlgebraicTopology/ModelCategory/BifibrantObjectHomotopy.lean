/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
# The homotopy category of bifibrant objects

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace BifibrantObject

variable (C) in
/-- The homotopy relation on the category of bifibrant objects. -/
def homRel : HomRel (BifibrantObject C) :=
  fun _ _ f g ↦ RightHomotopyRel f.hom g.hom

lemma homRel_iff_rightHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel f.hom g.hom := Iff.rfl

lemma homRel_iff_leftHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]

instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _

instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _

instance : Congruence (homRel C) where
  equivalence :=
    { refl _ := .refl _
      symm h := .symm h
      trans h₁ h₂ := .trans h₁ h₂ }

variable (C) in
/-- The homotopy category of bifibrant objects. -/
abbrev π := Quotient (BifibrantObject.homRel C)

/-- The quotient functor from the category of bifibrant objects to its
homotopy category. -/
def toπ : BifibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq {X Y : BifibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toπ.map f = toπ.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toπ_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _

section

variable {D : Type*} [Category* D]

lemma inverts_iff_factors (F : BifibrantObject C ⥤ D) :
    (weakEquivalences _).IsInvertedBy F ↔
    ∀ ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L),
      homRel C f g → F.map f = F.map g := by
  refine ⟨fun H K L f g h ↦ ?_, fun h X Y f hf ↦ ?_⟩
  · obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
    have := isCofibrant_of_cofibration P.ι
    have : IsIso (F.map (homMk P.ι)) := H _ (by
      rw [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
      exact inferInstanceAs (WeakEquivalence P.ι))
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp]
    congr 1
    simp [← cancel_epi (F.map (homMk P.ι)), ← Functor.map_comp]
  · rw [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty] at hf
    obtain ⟨g', h₁, h₂⟩ := RightHomotopyClass.whitehead f.hom
    refine ⟨F.map (homMk g'), ?_, ?_⟩
    all_goals
      rw [← F.map_comp, ← F.map_id]
      apply h
      assumption

/-- The strict universal property of the localization with respect
to weak equivalences for the quotient functor
`toπ : BifibrantObject C ⥤ BifibrantObject.π C`. -/
def strictUniversalPropertyFixedTargetToπ :
    Localization.StrictUniversalPropertyFixedTarget
      toπ (weakEquivalences (BifibrantObject C)) D where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

instance : toπ.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ strictUniversalPropertyFixedTargetToπ strictUniversalPropertyFixedTargetToπ

instance {X Y : BifibrantObject C} (f : X ⟶ Y) [hf : WeakEquivalence f] :
    IsIso (toπ.map f) :=
  Localization.inverts toπ (weakEquivalences _) f (by rwa [weakEquivalence_iff] at hf)

section

variable {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]

/-- Right homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.π`. -/
def π.homEquivRight :
    RightHomotopyClass X Y ≃ (toπ.obj (mk X) ⟶ toπ.obj (mk Y)) where
  toFun := Quot.lift (fun f ↦ toπ.map (homMk f)) (fun _ _ h ↦ by rwa [toπ_map_eq_iff])
  invFun := Quot.lift (fun f ↦ .mk f.hom) (fun _ _ h ↦ by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
lemma π.homEquivRight_apply (f : X ⟶ Y) :
    π.homEquivRight (.mk f) = toπ.map (homMk f) := rfl

@[simp]
lemma π.homEquivRight_symm_apply (f : X ⟶ Y) :
    π.homEquivRight.symm (toπ.map (homMk f)) = .mk f := rfl

/-- Left homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.π`. -/
def π.homEquivLeft :
    LeftHomotopyClass X Y ≃ (toπ.obj (mk X) ⟶ toπ.obj (mk Y)) :=
  leftHomotopyClassEquivRightHomotopyClass.trans π.homEquivRight

@[simp]
lemma π.homEquivLeft_apply (f : X ⟶ Y) :
    π.homEquivLeft (.mk f) = toπ.map (homMk f) := by
  simp [homEquivLeft]

@[simp]
lemma π.homEquivLeft_symm_apply (f : X ⟶ Y) :
    π.homEquivRight.symm (toπ.map (homMk f)) = .mk f := rfl

end

/-- The inclusion functor `BifibrantObject.π C ⥤ FibrantObject.π C`. -/
def π.ιFibrantObject : π C ⥤ FibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιFibrantObject ⋙ FibrantObject.toπ) (fun _ _ _ _ h ↦ by
      simpa [FibrantObject.toπ_map_eq_iff, FibrantObject.homRel_iff_leftHomotopyRel,
        homRel_iff_leftHomotopyRel] using h)

@[simp]
lemma π.ιFibrantObject_obj (X : BifibrantObject C) :
    π.ιFibrantObject.obj (toπ.obj X) =
      FibrantObject.toπ.obj (BifibrantObject.ιFibrantObject.obj X) :=
  rfl

@[simp]
lemma π.ιFibrantObject_map_toπ_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    π.ιFibrantObject.map (toπ.map f) =
      FibrantObject.toπ.map (FibrantObject.homMk f.hom) :=
  rfl

/-- The isomomorphism `toπ ⋙ π.ιFibrantObject ≅ ιFibrantObject ⋙ FibrantObject.toπ`
between functors `BifibrantObject C ⥤ FibrantObject.π C`. -/
def toπCompιFibrantObject :
    toπ (C := C) ⋙ π.ιFibrantObject ≅
      ιFibrantObject ⋙ FibrantObject.toπ := Iso.refl _

/-- The inclusion functor `BifibrantObject.π C ⥤ CofibrantObject.π C`. -/
def π.ιCofibrantObject : π C ⥤ CofibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιCofibrantObject ⋙ CofibrantObject.toπ) (fun _ _ _ _ h ↦ by
      simpa [CofibrantObject.toπ_map_eq_iff])

@[simp]
lemma π.ιCofibrantObject_obj (X : BifibrantObject C) :
    π.ιCofibrantObject.obj (toπ.obj X) =
      CofibrantObject.toπ.obj (BifibrantObject.ιCofibrantObject.obj X) :=
  rfl

@[simp]
lemma π.ιCofibrantObject_map_toπ_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    π.ιCofibrantObject.map (toπ.map f) =
      CofibrantObject.toπ.map (CofibrantObject.homMk f.hom) :=
  rfl

/-- The isomomorphism `toπ ⋙ π.ιCofibrantObject ≅ ιCofibrantObject ⋙ CofibrantObject.toπ`
between functors `BifibrantObject C ⥤ CofibrantObject.π C`. -/
def toπCompιCofibrantObject :
    toπ (C := C) ⋙ π.ιCofibrantObject ≅
      ιCofibrantObject ⋙ CofibrantObject.toπ := Iso.refl _

end BifibrantObject

namespace CofibrantObject

lemma exists_bifibrant (X : CofibrantObject C) :
    ∃ (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y),
      Cofibration (ι.map i) ∧ WeakEquivalence (ι.map i) := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, homMk h.i, inferInstanceAs (Cofibration h.i),
    inferInstanceAs (WeakEquivalence h.i)⟩

/-- Given `X : CofibrantObject C`, this is a choice of bifibrant resolution of `X`. -/
noncomputable def bifibrantResolutionObj (X : CofibrantObject C) :
    BifibrantObject C :=
  (exists_bifibrant X).choose

/-- Given `X : CofibrantObject C`, this is a trivial cofibration
from `X` to a choice of bifibrant resolution. -/
noncomputable def iBifibrantResolutionObj (X : CofibrantObject C) :
    X ⟶ BifibrantObject.ιCofibrantObject.obj (bifibrantResolutionObj X) :=
  (exists_bifibrant X).choose_spec.choose

instance (X : CofibrantObject C) :
    Cofibration (iBifibrantResolutionObj X).hom :=
  (exists_bifibrant X).choose_spec.choose_spec.1

instance (X : CofibrantObject C) :
    WeakEquivalence (iBifibrantResolutionObj X).hom :=
  (exists_bifibrant X).choose_spec.choose_spec.2

instance (X : CofibrantObject C) :
    WeakEquivalence (iBifibrantResolutionObj X) := by
  rw [weakEquivalence_iff_of_objectProperty]
  infer_instance

instance (X : BifibrantObject C) :
    IsFibrant (ι.obj (BifibrantObject.ιCofibrantObject.obj X)) := X.2.2

lemma exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    ∃ (g : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂),
      iBifibrantResolutionObj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) =
      f ≫ iBifibrantResolutionObj X₂ := by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (iBifibrantResolutionObj X₁).hom (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨BifibrantObject.homMk sq.lift, by cat_disch⟩

/-- Given a morphism in `CofibrantObject C`, this is a choice of morphism
(well defined only up to homotopy) between the chosen bifibrant resolutions. -/
noncomputable def bifibrantResolutionMap {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose

@[reassoc (attr := simp)]
lemma bifibrantResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    iBifibrantResolutionObj X₁ ≫ homMk (bifibrantResolutionMap f).hom  =
      f ≫ iBifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose_spec

instance {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) [WeakEquivalence f] :
    WeakEquivalence (bifibrantResolutionMap f) := by
  rw [weakEquivalence_iff]
  change weakEquivalences _ (CofibrantObject.homMk (bifibrantResolutionMap f).hom)
  rw [← weakEquivalence_iff, ← weakEquivalence_precomp_iff (iBifibrantResolutionObj X₁),
    bifibrantResolutionMap_fac, weakEquivalence_precomp_iff]
  infer_instance

@[reassoc (attr := simp)]
lemma bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    toπ.map X₁.iBifibrantResolutionObj ≫
    toπ.map (homMk (bifibrantResolutionMap f).hom) =
    toπ.map f ≫ toπ.map X₂.iBifibrantResolutionObj :=
  toπ.congr_map (bifibrantResolutionMap_fac f)

lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.π C} {f g :
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.π.ιCofibrantObject.map f =
      CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.π.ιCofibrantObject.map g) :
    f = g := by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toπ_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toπ.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toπ.map_surjective g
  change toπ.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toπ.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map g) at h
  rw [CofibrantObject.toπ_map_eq_iff,
    CofibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff] at h
  rw [BifibrantObject.toπ_map_eq_iff,
    BifibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff]
  apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    _ (iBifibrantResolutionObj X).hom).1
  simpa only [ObjectProperty.ι_obj, ObjectProperty.ιOfLE_obj_obj, ObjectProperty.ι_map,
    RightHomotopyClass.precomp_mk] using h

/-- The bifibrant resolution functor from the category of cofibrant objects
to the homotopy category of bifibrant objects. -/
@[simps]
noncomputable def π.bifibrantResolution' : CofibrantObject C ⥤ BifibrantObject.π C where
  obj X := BifibrantObject.toπ.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toπ.map (bifibrantResolutionMap f)
  map_id X := bifibrantResolutionObj_hom_ext (by simp)
  map_comp {X₁ X₂ X₃} f g := bifibrantResolutionObj_hom_ext (by simp)

/-- The bifibrant resolution functor from the homotopy category of
cofibrant objects to the homotopy category of bifibrant objects. -/
noncomputable def π.bifibrantResolution :
    CofibrantObject.π C ⥤ BifibrantObject.π C :=
  CategoryTheory.Quotient.lift _ CofibrantObject.π.bifibrantResolution' (by
    intro X Y f g h
    apply bifibrantResolutionObj_hom_ext
    simpa [← Functor.map_comp, toπ_map_eq_iff] using h.postcomp _)

@[simp]
lemma π.bifibrantResolution_obj (X : CofibrantObject C) :
    π.bifibrantResolution.obj (CofibrantObject.toπ.obj X) =
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) := rfl

@[simp]
lemma π.bifibrantResolution_map {X Y : CofibrantObject C} (f : X ⟶ Y) :
    π.bifibrantResolution.map (CofibrantObject.toπ.map f) =
      BifibrantObject.toπ.map (bifibrantResolutionMap f) := rfl

/-- Auxiliary definition for `CofibrantObject.π.adj`. -/
noncomputable def π.adjUnit :
    𝟭 (π C) ⟶ π.bifibrantResolution ⋙ BifibrantObject.π.ιCofibrantObject :=
  Quotient.natTransLift _
    { app X := toπ.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

lemma π.adjUnit_app (X : CofibrantObject C) :
    π.adjUnit.app (toπ.obj X) =
      toπ.map (iBifibrantResolutionObj X) := rfl

instance (X : CofibrantObject.π C) : WeakEquivalence (π.adjUnit.app X) := by
  obtain ⟨X, rfl⟩ := toπ_obj_surjective X
  rw [π.adjUnit_app, weakEquivalence_toπ_map_iff,
    weakEquivalence_iff_of_objectProperty]
  infer_instance

/-- Auxiliary definition for `CofibrantObject.π.adj`. -/
noncomputable def π.adjCounit' :
    𝟭 (BifibrantObject.π C) ⟶ BifibrantObject.π.ιCofibrantObject ⋙ π.bifibrantResolution :=
  Quotient.natTransLift _
    { app X :=
        BifibrantObject.toπ.map
          (BifibrantObject.homMk (iBifibrantResolutionObj (.mk X.obj)).hom)
      naturality X₁ X₂ f := BifibrantObject.toπ.congr_map (by
        have := (ObjectProperty.ι _).congr_map
          (bifibrantResolutionMap_fac (CofibrantObject.homMk f.hom)).symm
        ext : 1
        dsimp
        exact this ) }

lemma π.adjCounit'_app (X : BifibrantObject C) :
    π.adjCounit'.app (BifibrantObject.toπ.obj X) =
      BifibrantObject.toπ.map (BifibrantObject.homMk
        (iBifibrantResolutionObj (.mk X.obj)).hom) := rfl

instance (X : BifibrantObject.π C) : IsIso (π.adjCounit'.app X) := by
  obtain ⟨X, rfl⟩ := BifibrantObject.toπ_obj_surjective X
  rw [π.adjCounit'_app]
  have : WeakEquivalence (C := BifibrantObject C)
      (BifibrantObject.homMk ((mk X.obj).iBifibrantResolutionObj).hom) := by
    simp only [BifibrantObject.weakEquivalence_homMk_iff]
    infer_instance
  infer_instance

instance : IsIso (π.adjCounit' (C := C)) := NatIso.isIso_of_isIso_app _

/-- Auxiliary definition for `CofibrantObject.π.adj`. -/
noncomputable def π.adjCounitIso :
    BifibrantObject.π.ιCofibrantObject ⋙ bifibrantResolution ≅ 𝟭 (BifibrantObject.π C) :=
  (asIso π.adjCounit').symm

lemma π.adjCounitIso_inv_app (X : BifibrantObject C) :
    π.adjCounitIso.inv.app (BifibrantObject.toπ.obj X) =
      BifibrantObject.toπ.map (BifibrantObject.homMk
        ((iBifibrantResolutionObj (.mk X.obj))).hom) := rfl

/-- The adjunction between the category `CofibrantObject.π C` and `BifibrantObject.π C`. -/
noncomputable def π.adj :
    π.bifibrantResolution (C := C) ⊣ BifibrantObject.π.ιCofibrantObject where
  unit := π.adjUnit
  counit := π.adjCounitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toπ_obj_surjective X
    obtain ⟨X, _, rfl⟩ := CofibrantObject.mk_surjective X
    rw [← cancel_mono (π.adjCounitIso.inv.app _), Category.assoc, Iso.hom_inv_id_app]
    apply bifibrantResolutionObj_hom_ext
    dsimp
    simp only [π.adjCounitIso_inv_app, Category.comp_id, Category.id_comp,
      BifibrantObject.π.ιCofibrantObject_map_toπ_map, ObjectProperty.homMk_hom]
    apply bifibrantResolutionMap_fac'
  right_triangle_components X := by
    obtain ⟨X, rfl⟩ := BifibrantObject.toπ_obj_surjective X
    rw [← cancel_mono (BifibrantObject.π.ιCofibrantObject.map (π.adjCounitIso.inv.app _)),
      Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    cat_disch

instance : IsIso (π.adj (C := C)).counit := by
  dsimp [π.adj]
  infer_instance

instance : (BifibrantObject.π.ιCofibrantObject (C := C)).Full :=
  π.adj.fullyFaithfulROfIsIsoCounit.full

instance : (BifibrantObject.π.ιCofibrantObject (C := C)).Faithful :=
  π.adj.fullyFaithfulROfIsIsoCounit.faithful

instance (X : CofibrantObject.π C) : WeakEquivalence (π.adj.unit.app X) := by
  obtain ⟨X, rfl⟩ := toπ_obj_surjective X
  dsimp [π.adj]
  infer_instance

instance : π.bifibrantResolution.IsLocalization (weakEquivalences (π C)) :=
  π.adj.isLocalization_leftAdjoint _ (by
    intro X Y f hf
    obtain ⟨X, rfl⟩ := toπ_obj_surjective X
    obtain ⟨Y, rfl⟩ := toπ_obj_surjective Y
    obtain ⟨f, rfl⟩ := toπ.map_surjective f
    rw [← weakEquivalence_iff, weakEquivalence_toπ_map_iff] at hf
    rw [π.bifibrantResolution_map]
    apply Localization.inverts _ (weakEquivalences _)
    rw [← weakEquivalence_iff]
    infer_instance) (fun X ↦ by
    rw [← weakEquivalence_iff]
    dsimp
    infer_instance)

end CofibrantObject

namespace BifibrantObject

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ C`, as a localizer morphism. -/
def localizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C)) (weakEquivalences C) where
  functor := ι
  map := by rfl

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ CofibrantObject C`, as a localizer morphism. -/
@[simps]
def ιCofibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (CofibrantObject C)) where
  functor := ιCofibrantObject
  map _ _ _ h := h

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ FibrantObject C`, as a localizer morphism. -/
@[simps]
def ιFibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (FibrantObject C)) where
  functor := ιFibrantObject
  map _ _ _ h := h

open Functor

instance : (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence := by
  have : CatCommSq (ιCofibrantObjectLocalizerMorphism C).functor toπ
      (CofibrantObject.toπ ⋙ CofibrantObject.π.bifibrantResolution) (𝟭 _) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight toπCompιCofibrantObject.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso CofibrantObject.π.adj.counit)⟩
  exact LocalizerMorphism.IsLocalizedEquivalence.mk'
    (ιCofibrantObjectLocalizerMorphism C) BifibrantObject.toπ
    (CofibrantObject.toπ ⋙ CofibrantObject.π.bifibrantResolution) (𝟭 _)

instance : (localizerMorphism C).IsLocalizedEquivalence :=
  inferInstanceAs ((ιCofibrantObjectLocalizerMorphism C).comp
    (CofibrantObject.localizerMorphism C)).IsLocalizedEquivalence

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (BifibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

instance : (ιFibrantObjectLocalizerMorphism C).IsLocalizedEquivalence := by
  let L := FibrantObject.ι ⋙ (weakEquivalences C).Q
  have : ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization
    (weakEquivalences _) :=
    inferInstanceAs ((ι ⋙ (weakEquivalences C).Q).IsLocalization (weakEquivalences _))
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ L

instance {D : Type*} [Category D] (L : FibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιFibrantObject ⋙ L).IsLocalization (weakEquivalences _) := by
  change ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _
  infer_instance

end BifibrantObject

end HomotopicalAlgebra
