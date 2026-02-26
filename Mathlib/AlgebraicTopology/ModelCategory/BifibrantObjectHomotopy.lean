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

We construct the homotopy category `BifibrantObject.HoCat C` of bifibrant
objects in a model category `C` and show that the functor
`BifibrantObject.toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`
is a localization functor with respect to weak equivalences.

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

end HomotopicalAlgebra
