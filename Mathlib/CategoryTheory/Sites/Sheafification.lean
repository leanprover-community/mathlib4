/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheafify J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left exact left adjoint (sheafification).

Note: to access the `HasSheafify` instance for suitable concrete categories, import the file
`Mathlib/CategoryTheory/Sites/LeftExact.lean`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/--
A proposition saying that the inclusion functor from sheaves to presheaves admits a left adjoint.
-/
abbrev HasWeakSheafify : Prop := (sheafToPresheaf J A).IsRightAdjoint

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
left adjoint (sheafification).

Given a functor, preserving finite limits, `F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A` and an adjunction
`adj : F ⊣ sheafToPresheaf J A`, use `HasSheafify.mk'` to construct a `HasSheafify` instance.
-/
class HasSheafify : Prop where
  isRightAdjoint : HasWeakSheafify J A
  isLeftExact : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)

instance [HasSheafify J A] : HasWeakSheafify J A := HasSheafify.isRightAdjoint

noncomputable section

instance [HasSheafify J A] : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint) :=
  HasSheafify.isLeftExact

theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨F, ⟨adj⟩⟩
  isLeftExact := ⟨by
    have : (sheafToPresheaf J A).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
    exact fun _ _ _ ↦ preservesLimitsOfShape_of_natIso
      (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint (sheafToPresheaf J A)))⟩

/-- The sheafification functor, left adjoint to the inclusion. -/
def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  (sheafToPresheaf J A).leftAdjoint

instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact

/-- The sheafification-inclusion adjunction. -/
def sheafificationAdjunction [HasWeakSheafify J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := Adjunction.ofIsRightAdjoint _

instance [HasWeakSheafify J A] : (presheafToSheaf J A).IsLeftAdjoint :=
  ⟨_, ⟨sheafificationAdjunction J A⟩⟩

instance [HasWeakSheafify J A] : Reflective (sheafToPresheaf J A) where
  L := presheafToSheaf J A
  adj := sheafificationAdjunction _ _

instance [HasSheafify J A] : PreservesFiniteLimits (reflector (sheafToPresheaf J A)) :=
  inferInstanceAs (PreservesFiniteLimits (presheafToSheaf _ _))

end

variable {D : Type*} [Category* D] [HasWeakSheafify J D]

/-- The sheafification of a presheaf `P`. -/
noncomputable abbrev sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  presheafToSheaf J D |>.obj P |>.obj

/-- The canonical map from `P` to its sheafification. -/
noncomputable abbrev toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ sheafify J P :=
  sheafificationAdjunction J D |>.unit.app P

@[simp]
theorem sheafificationAdjunction_unit_app (P : Cᵒᵖ ⥤ D) :
    (sheafificationAdjunction J D).unit.app P = toSheafify J P := rfl

/-- The canonical map on sheafifications induced by a morphism. -/
noncomputable abbrev sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : sheafify J P ⟶ sheafify J Q :=
  presheafToSheaf J D |>.map η |>.hom

@[simp]
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : sheafifyMap J (𝟙 P) = 𝟙 (sheafify J P) := by
  simp [sheafifyMap, sheafify]

@[simp]
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    sheafifyMap J (η ≫ γ) = sheafifyMap J η ≫ sheafifyMap J γ := by
  simp [sheafifyMap, sheafify]

@[reassoc (attr := simp)]
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η :=
  sheafificationAdjunction J D |>.unit.naturality η

variable (D)

/-- The sheafification of a presheaf `P`, as a functor. -/
noncomputable abbrev sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  presheafToSheaf J D ⋙ sheafToPresheaf J D

theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (sheafification J D).obj P = sheafify J P :=
  rfl

theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (sheafification J D).map η = sheafifyMap J η :=
  rfl

/-- The canonical map from `P` to its sheafification, as a natural transformation. -/
noncomputable abbrev toSheafification : 𝟭 _ ⟶ sheafification J D :=
  sheafificationAdjunction J D |>.unit

theorem toSheafification_app (P : Cᵒᵖ ⥤ D) : (toSheafification J D).app P = toSheafify J P :=
  rfl

variable {D}

theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (toSheafify J P) := by
  refine ⟨(sheafificationAdjunction J D |>.counit.app ⟨P, hP⟩).hom, ?_, ?_⟩
  · change _ = (𝟙 (sheafToPresheaf J D ⋙ 𝟭 (Cᵒᵖ ⥤ D)) :).app ⟨P, hP⟩
    rw [← sheafificationAdjunction J D |>.right_triangle]
    rfl
  · change (sheafToPresheaf _ _).map _ ≫ _ = _
    change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨P, hP⟩) = _
    rw [← (sheafificationAdjunction J D).inv_counit_map (X := ⟨P, hP⟩)]
    simp

/-- If `P` is a sheaf, then `P` is isomorphic to `sheafify J P`. -/
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ sheafify J P :=
  letI := isIso_toSheafify J hP
  asIso (toSheafify J P)

@[simp]
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (isoSheafify J hP).hom = toSheafify J P :=
  rfl

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from `sheafify J P` to `Q`. -/
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    sheafify J P ⟶ Q :=
  (sheafificationAdjunction J D).homEquiv P ⟨Q, hQ⟩ |>.symm η |>.hom

@[simp]
theorem sheafificationAdjunction_counit_app_val (P : Sheaf J D) :
    ((sheafificationAdjunction J D).counit.app P).hom = sheafifyLift J (𝟙 P.obj) P.property := by
  unfold sheafifyLift
  rw [Adjunction.homEquiv_counit]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    toSheafify J P ≫ sheafifyLift J η hQ = η := by
  rw [toSheafify, sheafifyLift, Adjunction.homEquiv_counit]
  change _ ≫ (sheafToPresheaf J D).map _ ≫ _ = _
  simp only [Adjunction.unit_naturality_assoc]
  change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨Q, hQ⟩) ≫ _ = _
  change _ ≫ _ ≫ (sheafToPresheaf J D).map _ = _
  rw [sheafificationAdjunction J D |>.right_triangle_components (Y := ⟨Q, hQ⟩)]
  simp

theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : sheafify J P ⟶ Q) : toSheafify J P ≫ γ = η → γ = sheafifyLift J η hQ := by
  intro h
  rw [toSheafify] at h
  rw [sheafifyLift]
  let γ' : (presheafToSheaf J D).obj P ⟶ ⟨Q, hQ⟩ := ⟨γ⟩
  change γ'.hom = _
  rw [← Sheaf.hom_ext_iff, ← Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_unit]
  exact h

@[simp]
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (isoSheafify J hP).inv = sheafifyLift J (𝟙 _) hP := by
  apply sheafifyLift_unique
  simp [Iso.comp_inv_eq]

theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : sheafify J P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : toSheafify J P ≫ η = toSheafify J P ≫ γ) : η = γ := by
  rw [sheafifyLift_unique J _ hQ _ h, ← h]
  exact (sheafifyLift_unique J _ hQ _ h.symm).symm

@[reassoc (attr := simp)]
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    sheafifyMap J η ≫ sheafifyLift J γ hR = sheafifyLift J (η ≫ γ) hR := by
  apply sheafifyLift_unique
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift]

lemma sheafifyLift_comp {F P Q : Cᵒᵖ ⥤ D} (a : F ⟶ P) (hP : Presheaf.IsSheaf J P)
    (η : P ⟶ Q) (hQ : CategoryTheory.Presheaf.IsSheaf J Q) :
    sheafifyLift J (a ≫ η) hQ = sheafifyLift _ a hP ≫ η :=
  (sheafifyLift_unique _ _ _ _ (by simp)).symm

variable {J}

/-- A sheaf `P` is isomorphic to its own sheafification. -/
@[simps]
noncomputable def sheafificationIso (P : Sheaf J D) : P ≅ (presheafToSheaf J D).obj P.obj where
  hom := ⟨(isoSheafify J P.2).hom⟩
  inv := ⟨(isoSheafify J P.2).inv⟩
  hom_inv_id := by
    ext1
    apply (isoSheafify J P.2).hom_inv_id
  inv_hom_id := by
    ext1
    apply (isoSheafify J P.2).inv_hom_id

instance isIso_sheafificationAdjunction_counit (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P) :=
  isIso_of_fully_faithful (sheafToPresheaf J D) _

instance (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P).hom :=
  inferInstanceAs (IsIso ((sheafToPresheaf J D).map _))

instance sheafification_reflective : IsIso (sheafificationAdjunction J D).counit :=
  NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma sheafifyLift_id_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    sheafifyLift J (𝟙 P) hP ≫ toSheafify J P = 𝟙 (sheafify J P) := by
  rw [← cancel_mono ((sheafificationAdjunction J D).counit.app ⟨P, hP⟩).hom]
  cat_disch

variable (J D)

/-- The natural isomorphism `𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J D`. -/
@[simps!]
noncomputable def sheafificationNatIso :
    𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J D :=
  NatIso.ofComponents (fun P => sheafificationIso P) (by cat_disch)

end CategoryTheory
