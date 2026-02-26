/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
public import Mathlib.CategoryTheory.Quotient.LocallySmall

/-!
# The homotopy category of bifibrant objects

We construct the homotopy category `BifibrantObject.HoCat C` of bifibrant
objects in a model category `C` and show that the functor
`BifibrantObject.toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`
is a localization functor with respect to weak equivalences.
We also show that certain localizer morphisms are localized weak equivalences,
which can be understood by saying that we obtain the same localized
category (up to equivalence) by inverting weak equivalences in `C`,
`CofibrantObject C`, `FibrantObject C` or `BifibrantObject C`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

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
abbrev HoCat := Quotient (BifibrantObject.homRel C)

/-- The quotient functor from the category of bifibrant objects to its
homotopy category. -/
def toHoCat : BifibrantObject C ⥤ HoCat C := Quotient.functor _

lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance

lemma toHoCat_map_eq {X Y : BifibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toHoCat_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _

instance [LocallySmall.{w} C] : LocallySmall.{w} (HoCat C) := by
  dsimp [HoCat]
  infer_instance

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
`toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`. -/
def strictUniversalPropertyFixedTargetToHoCat :
    Localization.StrictUniversalPropertyFixedTarget
      toHoCat (weakEquivalences (BifibrantObject C)) D where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

instance : toHoCat.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ strictUniversalPropertyFixedTargetToHoCat
    strictUniversalPropertyFixedTargetToHoCat

instance {X Y : BifibrantObject C} (f : X ⟶ Y) [hf : WeakEquivalence f] :
    IsIso (toHoCat.map f) :=
  Localization.inverts toHoCat (weakEquivalences _) f (by rwa [weakEquivalence_iff] at hf)

section

variable {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]

/-- Right homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.HoCat`. -/
def HoCat.homEquivRight :
    RightHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) where
  toFun := Quot.lift (fun f ↦ toHoCat.map (homMk f)) (fun _ _ h ↦ by rwa [toHoCat_map_eq_iff])
  invFun := Quot.lift (fun f ↦ .mk f.hom) (fun _ _ h ↦ by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
lemma HoCat.homEquivRight_apply (f : X ⟶ Y) :
    HoCat.homEquivRight (.mk f) = toHoCat.map (homMk f) := rfl

@[simp]
lemma HoCat.homEquivRight_symm_apply (f : X ⟶ Y) :
    HoCat.homEquivRight.symm (toHoCat.map (homMk f)) = .mk f := rfl

/-- Left homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.HoCat`. -/
def HoCat.homEquivLeft :
    LeftHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) :=
  leftHomotopyClassEquivRightHomotopyClass.trans HoCat.homEquivRight

@[simp]
lemma HoCat.homEquivLeft_apply (f : X ⟶ Y) :
    HoCat.homEquivLeft (.mk f) = toHoCat.map (homMk f) := by
  simp [homEquivLeft]

@[simp]
lemma HoCat.homEquivLeft_symm_apply (f : X ⟶ Y) :
    HoCat.homEquivRight.symm (toHoCat.map (homMk f)) = .mk f := rfl

end

/-- The inclusion functor `BifibrantObject.HoCat C ⥤ FibrantObject.HoCat C`. -/
def HoCat.ιFibrantObject : HoCat C ⥤ FibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιFibrantObject ⋙ FibrantObject.toHoCat) (fun _ _ _ _ h ↦ by
      simpa [FibrantObject.toHoCat_map_eq_iff, FibrantObject.homRel_iff_leftHomotopyRel,
        homRel_iff_leftHomotopyRel] using h)

@[simp]
lemma HoCat.ιFibrantObject_obj (X : BifibrantObject C) :
    HoCat.ιFibrantObject.obj (toHoCat.obj X) =
      FibrantObject.toHoCat.obj (BifibrantObject.ιFibrantObject.obj X) :=
  rfl

@[simp]
lemma HoCat.ιFibrantObject_map_toHoCat_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    HoCat.ιFibrantObject.map (toHoCat.map f) =
      FibrantObject.toHoCat.map (FibrantObject.homMk f.hom) :=
  rfl

/-- The isomomorphism `toHoCat ⋙ HoCat.ιFibrantObject ≅ ιFibrantObject ⋙ FibrantObject.toHoCat`
between functors `BifibrantObject C ⥤ FibrantObject.HoCat C`. -/
def toHoCatCompιFibrantObject :
    toHoCat (C := C) ⋙ HoCat.ιFibrantObject ≅
      ιFibrantObject ⋙ FibrantObject.toHoCat := Iso.refl _

/-- The inclusion functor `BifibrantObject.HoCat C ⥤ CofibrantObject.HoCat C`. -/
def HoCat.ιCofibrantObject : HoCat C ⥤ CofibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιCofibrantObject ⋙ CofibrantObject.toHoCat) (fun _ _ _ _ h ↦ by
      simpa [CofibrantObject.toHoCat_map_eq_iff])

@[simp]
lemma HoCat.ιCofibrantObject_obj (X : BifibrantObject C) :
    HoCat.ιCofibrantObject.obj (toHoCat.obj X) =
      CofibrantObject.toHoCat.obj (BifibrantObject.ιCofibrantObject.obj X) :=
  rfl

@[simp]
lemma HoCat.ιCofibrantObject_map_toHoCat_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    HoCat.ιCofibrantObject.map (toHoCat.map f) =
      CofibrantObject.toHoCat.map (CofibrantObject.homMk f.hom) :=
  rfl

/-- The isomomorphism
`toHoCat ⋙ HoCat.ιCofibrantObject ≅ ιCofibrantObject ⋙ CofibrantObject.toHoCat`
between functors `BifibrantObject C ⥤ CofibrantObject.HoCat C`. -/
def toHoCatCompιCofibrantObject :
    toHoCat (C := C) ⋙ HoCat.ιCofibrantObject ≅
      ιCofibrantObject ⋙ CofibrantObject.toHoCat := Iso.refl _

end BifibrantObject

namespace CofibrantObject

lemma exists_bifibrant (X : CofibrantObject C) :
    ∃ (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y),
      Cofibration (ι.map i) ∧ WeakEquivalence (ι.map i) := by
  let h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
instance {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) [WeakEquivalence f] :
    WeakEquivalence (bifibrantResolutionMap f) := by
  rw [weakEquivalence_iff]
  change weakEquivalences _ (CofibrantObject.homMk (bifibrantResolutionMap f).hom)
  rw [← weakEquivalence_iff, ← weakEquivalence_precomp_iff (iBifibrantResolutionObj X₁),
    bifibrantResolutionMap_fac, weakEquivalence_precomp_iff]
  infer_instance

@[reassoc (attr := simp)]
lemma bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    toHoCat.map X₁.iBifibrantResolutionObj ≫
    toHoCat.map (homMk (bifibrantResolutionMap f).hom) =
    toHoCat.map f ≫ toHoCat.map X₂.iBifibrantResolutionObj :=
  toHoCat.congr_map (bifibrantResolutionMap_fac f)

lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.HoCat C} {f g :
      BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.HoCat.ιCofibrantObject.map f =
      CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.HoCat.ιCofibrantObject.map g) :
    f = g := by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toHoCat_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective g
  change toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map g) at h
  rw [CofibrantObject.toHoCat_map_eq_iff,
    CofibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff] at h
  rw [BifibrantObject.toHoCat_map_eq_iff,
    BifibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff]
  apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    _ (iBifibrantResolutionObj X).hom).1
  simpa using h

set_option backward.isDefEq.respectTransparency false in
/-- The bifibrant resolution functor from the category of cofibrant objects
to the homotopy category of bifibrant objects. -/
@[simps]
noncomputable def HoCat.bifibrantResolution' : CofibrantObject C ⥤ BifibrantObject.HoCat C where
  obj X := BifibrantObject.toHoCat.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toHoCat.map (bifibrantResolutionMap f)
  map_id X := bifibrantResolutionObj_hom_ext (by simp)
  map_comp {X₁ X₂ X₃} f g := bifibrantResolutionObj_hom_ext (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The bifibrant resolution functor from the homotopy category of
cofibrant objects to the homotopy category of bifibrant objects. -/
noncomputable def HoCat.bifibrantResolution :
    CofibrantObject.HoCat C ⥤ BifibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _ CofibrantObject.HoCat.bifibrantResolution' (by
    intro X Y f g h
    apply bifibrantResolutionObj_hom_ext
    simpa [← Functor.map_comp, toHoCat_map_eq_iff] using h.postcomp _)

@[simp]
lemma HoCat.bifibrantResolution_obj (X : CofibrantObject C) :
    HoCat.bifibrantResolution.obj (CofibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) := rfl

@[simp]
lemma HoCat.bifibrantResolution_map {X Y : CofibrantObject C} (f : X ⟶ Y) :
    HoCat.bifibrantResolution.map (CofibrantObject.toHoCat.map f) =
      BifibrantObject.toHoCat.map (bifibrantResolutionMap f) := rfl

/-- Auxiliary definition for `CofibrantObject.HoCat.adj`. -/
noncomputable def HoCat.adjUnit :
    𝟭 (HoCat C) ⟶ HoCat.bifibrantResolution ⋙ BifibrantObject.HoCat.ιCofibrantObject :=
  Quotient.natTransLift _
    { app X := toHoCat.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

lemma HoCat.adjUnit_app (X : CofibrantObject C) :
    HoCat.adjUnit.app (toHoCat.obj X) =
      toHoCat.map (iBifibrantResolutionObj X) := rfl

set_option backward.isDefEq.respectTransparency false in
instance (X : CofibrantObject.HoCat C) : WeakEquivalence (HoCat.adjUnit.app X) := by
  obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
  rw [HoCat.adjUnit_app, weakEquivalence_toHoCat_map_iff,
    weakEquivalence_iff_of_objectProperty]
  infer_instance

/-- Auxiliary definition for `CofibrantObject.HoCat.adj`. -/
noncomputable def HoCat.adjCounit' :
    𝟭 (BifibrantObject.HoCat C) ⟶
      BifibrantObject.HoCat.ιCofibrantObject ⋙ HoCat.bifibrantResolution :=
  Quotient.natTransLift _
    { app X :=
        BifibrantObject.toHoCat.map
          (BifibrantObject.homMk (iBifibrantResolutionObj (.mk X.obj)).hom)
      naturality X₁ X₂ f := BifibrantObject.toHoCat.congr_map (by
        have := (ObjectProperty.ι _).congr_map
          (bifibrantResolutionMap_fac (CofibrantObject.homMk f.hom)).symm
        ext : 1
        dsimp
        exact this ) }

lemma HoCat.adjCounit'_app (X : BifibrantObject C) :
    HoCat.adjCounit'.app (BifibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk
        (iBifibrantResolutionObj (.mk X.obj)).hom) := rfl

set_option backward.isDefEq.respectTransparency false in
instance (X : BifibrantObject.HoCat C) : IsIso (HoCat.adjCounit'.app X) := by
  obtain ⟨X, rfl⟩ := BifibrantObject.toHoCat_obj_surjective X
  rw [HoCat.adjCounit'_app]
  have : WeakEquivalence (C := BifibrantObject C)
      (BifibrantObject.homMk ((mk X.obj).iBifibrantResolutionObj).hom) := by
    simp only [BifibrantObject.weakEquivalence_homMk_iff]
    infer_instance
  infer_instance

instance : IsIso (HoCat.adjCounit' (C := C)) := NatIso.isIso_of_isIso_app _

/-- Auxiliary definition for `CofibrantObject.HoCat.adj`. -/
noncomputable def HoCat.adjCounitIso :
    BifibrantObject.HoCat.ιCofibrantObject ⋙ bifibrantResolution ≅ 𝟭 (BifibrantObject.HoCat C) :=
  (asIso HoCat.adjCounit').symm

lemma HoCat.adjCounitIso_inv_app (X : BifibrantObject C) :
    HoCat.adjCounitIso.inv.app (BifibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk
        ((iBifibrantResolutionObj (.mk X.obj))).hom) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the category `CofibrantObject.HoCat C` and `BifibrantObject.HoCat C`. -/
noncomputable def HoCat.adj :
    HoCat.bifibrantResolution (C := C) ⊣ BifibrantObject.HoCat.ιCofibrantObject where
  unit := HoCat.adjUnit
  counit := HoCat.adjCounitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨X, _, rfl⟩ := CofibrantObject.mk_surjective X
    rw [← cancel_mono (HoCat.adjCounitIso.inv.app _), Category.assoc, Iso.hom_inv_id_app]
    apply bifibrantResolutionObj_hom_ext
    dsimp
    simp only [HoCat.adjCounitIso_inv_app, Category.comp_id, Category.id_comp,
      BifibrantObject.HoCat.ιCofibrantObject_map_toHoCat_map, ObjectProperty.homMk_hom]
    apply bifibrantResolutionMap_fac'
  right_triangle_components X := by
    obtain ⟨X, rfl⟩ := BifibrantObject.toHoCat_obj_surjective X
    rw [← cancel_mono (BifibrantObject.HoCat.ιCofibrantObject.map (HoCat.adjCounitIso.inv.app _)),
      Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    cat_disch

instance : IsIso (HoCat.adj (C := C)).counit := by
  dsimp [HoCat.adj]
  infer_instance

instance : (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Full :=
  HoCat.adj.fullyFaithfulROfIsIsoCounit.full

instance : (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Faithful :=
  HoCat.adj.fullyFaithfulROfIsIsoCounit.faithful

set_option backward.isDefEq.respectTransparency false in
instance (X : CofibrantObject.HoCat C) : WeakEquivalence (HoCat.adj.unit.app X) := by
  obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
  dsimp [HoCat.adj]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : HoCat.bifibrantResolution.IsLocalization (weakEquivalences (HoCat C)) :=
  HoCat.adj.isLocalization_leftAdjoint _ (by
    intro X Y f hf
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨Y, rfl⟩ := toHoCat_obj_surjective Y
    obtain ⟨f, rfl⟩ := toHoCat.map_surjective f
    rw [← weakEquivalence_iff, weakEquivalence_toHoCat_map_iff] at hf
    rw [HoCat.bifibrantResolution_map]
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

instance : (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence :=
  let : CatCommSq (ιCofibrantObjectLocalizerMorphism C).functor toHoCat
      (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight toHoCatCompιCofibrantObject.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso CofibrantObject.HoCat.adj.counit)⟩
  LocalizerMorphism.IsLocalizedEquivalence.mk'
    (ιCofibrantObjectLocalizerMorphism C) BifibrantObject.toHoCat
    (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _)

instance {D : Type*} [Category D] (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιCofibrantObject ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((ιCofibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _)

instance : (localizerMorphism C).IsLocalizedEquivalence :=
  inferInstanceAs ((ιCofibrantObjectLocalizerMorphism C).comp
    (CofibrantObject.localizerMorphism C)).IsLocalizedEquivalence

instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (BifibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

instance : (ιFibrantObjectLocalizerMorphism C).IsLocalizedEquivalence :=
  let L := FibrantObject.ι ⋙ (weakEquivalences C).Q
  have : ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization
    (weakEquivalences _) :=
    inferInstanceAs ((ι ⋙ (weakEquivalences C).Q).IsLocalization (weakEquivalences _))
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ L

instance {D : Type*} [Category D] (L : FibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιFibrantObject ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _)

end BifibrantObject

lemma locallySmall_of_isLocalization {D : Type*} [Category* D]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)] [LocallySmall.{w} C] :
    LocallySmall.{w} D :=
  locallySmall_of_faithful ((BifibrantObject.localizerMorphism C).localizedFunctor
    BifibrantObject.toHoCat L).inv

end HomotopicalAlgebra
