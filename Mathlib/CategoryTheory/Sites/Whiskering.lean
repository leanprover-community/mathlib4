/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Sheaf

#align_import category_theory.sites.whiskering from "leanprover-community/mathlib"@"9f9015c645d85695581237cc761981036be8bd37"

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `Presheaf.IsSheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `sheafCompose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`sheafCompose J F ⟶ sheafCompose J G`, which we call `sheafCompose_map J η`.

-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{v₂} A]

variable {B : Type u₃} [Category.{v₃} B]

variable {J : GrothendieckTopology C}

variable {U : C} (R : Presieve U)

variable (F G H : A ⥤ B) (η : F ⟶ G) (γ : G ⟶ H)

namespace GrothendieckTopology.Cover

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X)

/-- The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left a => eqToIso rfl
      | WalkingMulticospan.right b => eqToIso rfl)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals aesop_cat)
#align category_theory.grothendieck_topology.cover.multicospan_comp CategoryTheory.GrothendieckTopology.Cover.multicospanComp

@[simp]
theorem multicospanComp_app_left (a) :
    (S.multicospanComp F P).app (WalkingMulticospan.left a) = eqToIso rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_app_left CategoryTheory.GrothendieckTopology.Cover.multicospanComp_app_left

@[simp]
theorem multicospanComp_app_right (b) :
    (S.multicospanComp F P).app (WalkingMulticospan.right b) = eqToIso rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_app_right CategoryTheory.GrothendieckTopology.Cover.multicospanComp_app_right

@[simp]
theorem multicospanComp_hom_app_left (a) :
    (S.multicospanComp F P).hom.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_app_left CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_app_left

@[simp]
theorem multicospanComp_hom_app_right (b) :
    (S.multicospanComp F P).hom.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_app_right CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_app_right

@[simp]
theorem multicospanComp_hom_inv_left (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X) (a) :
    (S.multicospanComp F P).inv.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_inv_left CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_inv_left

@[simp]
theorem multicospanComp_hom_inv_right (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X) (b) :
    (S.multicospanComp F P).inv.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_inv_right CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_inv_right

/-- Mapping the multifork associated to a cover `S : J.Cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
def mapMultifork :
    F.mapCone (S.multifork P) ≅
      (Limits.Cones.postcompose (S.multicospanComp F P).hom).obj (S.multifork (P ⋙ F)) :=
  Cones.ext (eqToIso rfl)
    (by
      rintro (a | b)
      · dsimp
        erw [Category.id_comp, multicospanComp_hom_app_left, eqToHom_refl, Category.comp_id]
      · dsimp
        erw [Functor.map_comp, Category.assoc, Category.id_comp,
          multicospanComp_hom_app_right, eqToHom_refl, Category.comp_id]
        rfl)
#align category_theory.grothendieck_topology.cover.map_multifork CategoryTheory.GrothendieckTopology.Cover.mapMultifork

end GrothendieckTopology.Cover

variable [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F]
variable [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan G]
variable [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan H]

theorem Presheaf.IsSheaf.comp {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (P ⋙ F) := by
  rw [Presheaf.isSheaf_iff_multifork] at hP ⊢
  intro X S
  obtain ⟨h⟩ := hP X S
  replace h := isLimitOfPreserves F h
  replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork F P)
  exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp F P) _ h⟩
#align category_theory.presheaf.is_sheaf.comp CategoryTheory.Presheaf.IsSheaf.comp

variable (J)

/-- Composing a sheaf with a functor preserving the appropriate limits yields a functor
between sheaf categories. -/
@[simps]
def sheafCompose : Sheaf J A ⥤ Sheaf J B where
  obj G := ⟨G.val ⋙ F, Presheaf.IsSheaf.comp _ G.2⟩
  map η := ⟨whiskerRight η.val _⟩
  map_id _ := Sheaf.Hom.ext _ _ <| whiskerRight_id _
  map_comp _ _ := Sheaf.Hom.ext _ _ <| whiskerRight_comp _ _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_compose CategoryTheory.sheafCompose

variable {F G}

/--
If `η : F ⟶ G` is a natural transformation then we obtain a morphism of functors
`sheafCompose J F ⟶ sheafCompose J G` by whiskering with `η` on the level of presheaves.
-/
def sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where
  app := fun X => .mk <| whiskerLeft _ η

@[simp]
lemma sheafCompose_id : sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _ := rfl

@[simp]
lemma sheafCompose_comp :
    sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sheafCompose_map J γ := rfl

end CategoryTheory
