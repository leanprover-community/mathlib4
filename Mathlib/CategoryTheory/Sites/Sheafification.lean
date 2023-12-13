/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheaf J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left adjoint (sheafification).
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/--
A proposition saying that the inclusion functor from sheaves to presheaves admits a left adjoint.
-/
abbrev HasWeakSheafify := Nonempty (IsRightAdjoint (sheafToPresheaf J A))

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
left adjiont (sheafification).
-/
class HasSheafify : Prop where
  isRightAdjoint : HasWeakSheafify J A
  isLeftExact : letI := isRightAdjoint.some
    Nonempty (PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A)))

instance [HasSheafify J A] : HasWeakSheafify J A := HasSheafify.isRightAdjoint

instance [IsRightAdjoint <| sheafToPresheaf J A] : HasWeakSheafify J A := ⟨inferInstance⟩

noncomputable section

instance [h : HasWeakSheafify J A] : IsRightAdjoint (sheafToPresheaf J A) := h.some

instance [HasSheafify J A] : PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A)) :=
  HasSheafify.isLeftExact.some

theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨⟨F, adj⟩⟩
  isLeftExact :=
    let i : (h : IsRightAdjoint (sheafToPresheaf J A) := ⟨F, adj⟩) →
      F ≅ leftAdjoint (sheafToPresheaf J A) := fun _ ↦
      adj.leftAdjointUniq (Adjunction.ofRightAdjoint (sheafToPresheaf J A))
    ⟨⟨fun _ ↦ preservesLimitsOfShapeOfNatIso (i _)⟩⟩

/-- The sheafification functor, left adjoint to the inclusion. -/
def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  leftAdjoint (sheafToPresheaf J A)
set_option linter.uppercaseLean3 false in
#align category_theory.presheaf_to_Sheaf CategoryTheory.presheafToSheaf

instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact.some

/-- The sheafification-inclusion adjunction. -/
def sheafificationAdjunction [HasWeakSheafify J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := IsRightAdjoint.adj
#align category_theory.sheafification_adjunction CategoryTheory.sheafificationAdjunction

instance [HasWeakSheafify J A] : IsLeftAdjoint <| presheafToSheaf J A where
  adj := sheafificationAdjunction J A

end

variable {D : Type*} [Category D] [HasWeakSheafify J D]

namespace GrothendieckTopology

/-- The sheafification of a presheaf `P`. -/
noncomputable abbrev sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  presheafToSheaf J D |>.obj P |>.val
#align category_theory.grothendieck_topology.sheafify CategoryTheory.GrothendieckTopology.sheafify

/-- The canonical map from `P` to its sheafification. -/
noncomputable abbrev toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P :=
  sheafificationAdjunction J D |>.unit.app P
#align category_theory.grothendieck_topology.to_sheafify CategoryTheory.GrothendieckTopology.toSheafify

/-- The canonical map on sheafifications induced by a morphism. -/
noncomputable abbrev sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q :=
  presheafToSheaf J D |>.map η |>.val
#align category_theory.grothendieck_topology.sheafify_map CategoryTheory.GrothendieckTopology.sheafifyMap

@[simp]
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P) := by
  dsimp [sheafifyMap, sheafify]
  simp
#align category_theory.grothendieck_topology.sheafify_map_id CategoryTheory.GrothendieckTopology.sheafifyMap_id

@[simp]
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.sheafifyMap (η ≫ γ) = J.sheafifyMap η ≫ J.sheafifyMap γ := by
  dsimp [sheafifyMap, sheafify]
  simp
#align category_theory.grothendieck_topology.sheafify_map_comp CategoryTheory.GrothendieckTopology.sheafifyMap_comp

@[reassoc (attr := simp)]
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toSheafify _ = J.toSheafify _ ≫ J.sheafifyMap η :=
  sheafificationAdjunction J D |>.unit.naturality η
#align category_theory.grothendieck_topology.to_sheafify_naturality CategoryTheory.GrothendieckTopology.toSheafify_naturality

variable (D)

/-- The sheafification of a presheaf `P`, as a functor. -/
noncomputable abbrev sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  presheafToSheaf J D ⋙ sheafToPresheaf J D
#align category_theory.grothendieck_topology.sheafification CategoryTheory.GrothendieckTopology.sheafification

theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify P :=
  rfl
#align category_theory.grothendieck_topology.sheafification_obj CategoryTheory.GrothendieckTopology.sheafification_obj

theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (J.sheafification D).map η = J.sheafifyMap η :=
  rfl
#align category_theory.grothendieck_topology.sheafification_map CategoryTheory.GrothendieckTopology.sheafification_map

/-- The canonical map from `P` to its sheafification, as a natural transformation. -/
noncomputable abbrev toSheafification : 𝟭 _ ⟶ sheafification J D :=
  sheafificationAdjunction J D |>.unit
#align category_theory.grothendieck_topology.to_sheafification CategoryTheory.GrothendieckTopology.toSheafification

@[simp]
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) : (J.toSheafification D).app P = J.toSheafify P :=
  rfl
#align category_theory.grothendieck_topology.to_sheafification_app CategoryTheory.GrothendieckTopology.toSheafification_app

variable {D}

theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSheafify P) := by
  refine ⟨(sheafificationAdjunction J D |>.counit.app ⟨P, hP⟩).val, ?_, ?_⟩
  · change _ = (𝟙 (sheafToPresheaf J D ⋙ 𝟭 (Cᵒᵖ ⥤ D)) : _).app ⟨P, hP⟩
    rw [← sheafificationAdjunction J D |>.right_triangle]
    rfl
  · change (sheafToPresheaf _ _).map _ ≫ _ = _
    change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨P, hP⟩) = _
    erw [← inv_counit_map (sheafificationAdjunction J D) (X := ⟨P, hP⟩), comp_inv_eq_id]
#align category_theory.grothendieck_topology.is_iso_to_sheafify CategoryTheory.GrothendieckTopology.isIso_toSheafify

/-- If `P` is a sheaf, then `P` is isomorphic to `J.sheafify P`. -/
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ J.sheafify P :=
  letI := isIso_toSheafify J hP
  asIso (J.toSheafify P)
#align category_theory.grothendieck_topology.iso_sheafify CategoryTheory.GrothendieckTopology.isoSheafify

@[simp]
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).hom = J.toSheafify P :=
  rfl
#align category_theory.grothendieck_topology.iso_sheafify_hom CategoryTheory.GrothendieckTopology.isoSheafify_hom

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from `J.sheafify P` to `Q`. -/
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.sheafify P ⟶ Q :=
  (sheafificationAdjunction J D).homEquiv P ⟨Q, hQ⟩ |>.symm η |>.val
#align category_theory.grothendieck_topology.sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyLift

@[reassoc (attr := simp)]
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toSheafify P ≫ sheafifyLift J η hQ = η := by
  rw [toSheafify, sheafifyLift, Adjunction.homEquiv_counit]
  change _ ≫ (sheafToPresheaf J D).map _ ≫ _ = _
  simp only [Adjunction.unit_naturality_assoc]
  change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨Q, hQ⟩) ≫ _ = _
  change _ ≫ _ ≫ (sheafToPresheaf J D).map _ = _
  rw [sheafificationAdjunction J D |>.right_triangle_components (Y := ⟨Q, hQ⟩)]
  simp
#align category_theory.grothendieck_topology.to_sheafify_sheafify_lift CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift

theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.sheafify P ⟶ Q) : J.toSheafify P ≫ γ = η → γ = sheafifyLift J η hQ := by
  intro h
  rw [toSheafify] at h
  rw [sheafifyLift]
  let γ' : (presheafToSheaf J D).obj P ⟶ ⟨Q, hQ⟩ := ⟨γ⟩
  change γ'.val = _
  rw [← Sheaf.Hom.ext_iff, ← Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_unit]
  exact h
#align category_theory.grothendieck_topology.sheafify_lift_unique CategoryTheory.GrothendieckTopology.sheafifyLift_unique

@[simp]
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).inv = J.sheafifyLift (𝟙 _) hP := by
  apply J.sheafifyLift_unique
  simp [Iso.comp_inv_eq]
#align category_theory.grothendieck_topology.iso_sheafify_inv CategoryTheory.GrothendieckTopology.isoSheafify_inv

theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toSheafify P ≫ η = J.toSheafify P ≫ γ) : η = γ := by
  rw [sheafifyLift_unique J _ hQ _ h, ← h]
  exact (sheafifyLift_unique J _ hQ _ h.symm).symm
#align category_theory.grothendieck_topology.sheafify_hom_ext CategoryTheory.GrothendieckTopology.sheafify_hom_ext

@[reassoc (attr := simp)]
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.sheafifyMap η ≫ J.sheafifyLift γ hR = J.sheafifyLift (η ≫ γ) hR := by
  apply J.sheafifyLift_unique
  rw [← Category.assoc, ← J.toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift]
#align category_theory.grothendieck_topology.sheafify_map_sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyMap_sheafifyLift

end GrothendieckTopology

open GrothendieckTopology

variable (D)

@[simp]
theorem sheafificationAdjunction_unit_app {P : Cᵒᵖ ⥤ D} :
    (sheafificationAdjunction J D).unit.app P = J.toSheafify P := rfl

@[simp]
theorem sheafificationAdjunction_counit_app_val (P : Sheaf J D) :
    ((sheafificationAdjunction J D).counit.app P).val = J.sheafifyLift (𝟙 P.val) P.cond := by
  unfold sheafifyLift
  rw [Adjunction.homEquiv_counit]
  simp

variable {J D}

/-- A sheaf `P` is isomorphic to its own sheafification. -/
@[simps]
noncomputable def sheafificationIso (P : Sheaf J D) : P ≅ (presheafToSheaf J D).obj P.val where
  hom := ⟨(J.isoSheafify P.2).hom⟩
  inv := ⟨(J.isoSheafify P.2).inv⟩
  hom_inv_id := by
    ext1
    apply (J.isoSheafify P.2).hom_inv_id
  inv_hom_id := by
    ext1
    apply (J.isoSheafify P.2).inv_hom_id
#align category_theory.sheafification_iso CategoryTheory.sheafificationIso

instance isIso_sheafificationAdjunction_counit (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P) :=
  isIso_of_fully_faithful (sheafToPresheaf J D) _
#align category_theory.is_iso_sheafification_adjunction_counit CategoryTheory.isIso_sheafificationAdjunction_counit

instance sheafification_reflective : IsIso (sheafificationAdjunction J D).counit :=
  NatIso.isIso_of_isIso_app _
#align category_theory.sheafification_reflective CategoryTheory.sheafification_reflective

end CategoryTheory
