/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Fiber functors are monoidal

Let `Φ` be a point of a site `(C, J)`. Let `A` be a monoidal category where
the tensor product commutes with filtered colimits in both variables.
We show that the fiber functors `Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A`
and `Φ.sheafFiber : Sheaf J A ⥤ A` are monoidal.

## TODO (@joelriou)
* for sites that have enough points, use this to give an alternative
  proof of the assumption to `Sheaf.monoidalCategory` in the file
  `Mathlib/CategoryTheory/Sites/Monoidal`

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits MonoidalCategory Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [MonoidalCategory A] [HasColimitsOfSize.{w, w} A]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance :
    (Φ.presheafFiber (A := A)).OplaxMonoidal where
  η := Φ.presheafFiberDesc (fun _ _ ↦ 𝟙 _)
  δ P₁ P₂ :=
    Φ.presheafFiberDesc (fun X x ↦ Φ.toPresheafFiber X x P₁ ⊗ₘ Φ.toPresheafFiber X x P₂)
      (by simp [tensorHom_comp_tensorHom])
  δ_natural_left _ _ := by
    ext
    simp [tensorHom_def', ← comp_whiskerRight, ← whisker_exchange_assoc]
  δ_natural_right P f := by
    ext
    simp [tensorHom_def, ← MonoidalCategory.whiskerLeft_comp, whisker_exchange_assoc]
  oplax_associativity P₁ P₂ P₃ := by
    ext X x
    dsimp
    conv_lhs =>
      simp only [toPresheafFiber_presheafFiberDesc_assoc, tensorHom_def'_assoc,
        ← comp_whiskerRight_assoc, toPresheafFiber_presheafFiberDesc]
      rw [← tensorHom_def'_assoc, associator_naturality]
    conv_rhs =>
      simp only [toPresheafFiber_naturality_assoc, toPresheafFiber_presheafFiberDesc_assoc,
        tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp,
        toPresheafFiber_presheafFiberDesc]
      rw [← tensorHom_def]
      dsimp
  oplax_left_unitality _ := by
    ext
    simp [tensorHom_def', ← comp_whiskerRight]
  oplax_right_unitality _ := by
    ext
    simp [tensorHom_def, ← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma toPresheafFiber_η (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (𝟙_ (Cᵒᵖ ⥤ A)) ≫ OplaxMonoidal.η Φ.presheafFiber = 𝟙 (𝟙_ A) :=
  toPresheafFiber_presheafFiberDesc _ _ _ _ _

@[reassoc (attr := simp)]
lemma toPresheafFiber_δ (X : C) (x : Φ.fiber.obj X) (G₁ G₂ : Cᵒᵖ ⥤ A) :
    Φ.toPresheafFiber X x (G₁ ⊗ G₂) ≫ OplaxMonoidal.δ Φ.presheafFiber G₁ G₂ =
      Φ.toPresheafFiber X x G₁ ⊗ₘ Φ.toPresheafFiber X x G₂ :=
  toPresheafFiber_presheafFiberDesc _ _ _ _ _

variable [LocallySmall.{w} C]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

instance (M : A) :
    PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ ((curriedTensor A).flip.obj M) :=
  Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

instance (M : A) :
    PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ ((curriedTensor A).obj M) :=
  Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

attribute [local instance] IsFiltered.isConnected in
instance : IsIso (OplaxMonoidal.η (Φ.presheafFiber (A := A))) :=
  (IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberCocone (𝟙_ _))
    (isColimitConstCocone _ (𝟙_ A))).isIso_hom

instance (P₁ P₂ : Cᵒᵖ ⥤ A) :
    IsIso (OplaxMonoidal.δ Φ.presheafFiber P₁ P₂) :=
  (IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberCocone (P₁ ⊗ P₂))
    ((Φ.isColimitPresheafFiberCocone P₁).tensor (Φ.isColimitPresheafFiberCocone P₂))).isIso_hom

noncomputable instance : (Φ.presheafFiber (A := A)).Monoidal :=
  .ofOplaxMonoidal _

set_option backward.isDefEq.respectTransparency false in
lemma toPresheafFiber_ε (X : C) (x : Φ.fiber.obj X) :
    LaxMonoidal.ε Φ.presheafFiber = Φ.toPresheafFiber X x (𝟙_ (Cᵒᵖ ⥤ A)) := by
  simp [← cancel_mono (OplaxMonoidal.η Φ.presheafFiber)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma tensorHom_comp_toPresheafFiber_μ (X : C) (x : Φ.fiber.obj X) (G₁ G₂ : Cᵒᵖ ⥤ A) :
    (Φ.toPresheafFiber X x G₁ ⊗ₘ Φ.toPresheafFiber X x G₂) ≫
      LaxMonoidal.μ Φ.presheafFiber G₁ G₂ =
    Φ.toPresheafFiber X x (G₁ ⊗ G₂) := by
  simp [← cancel_mono (OplaxMonoidal.δ Φ.presheafFiber G₁ G₂)]

section

attribute [local instance] Sheaf.monoidalCategory

variable [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [HasProducts.{w} A]

noncomputable instance : (Φ.sheafFiber (A := A)).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (presheafToSheaf J A) J.W
    Φ.sheafFiber Φ.presheafFiber

instance : NatTrans.IsMonoidal (Φ.presheafToSheafCompSheafFiberIso A).hom :=
  Localization.Monoidal.lifting_isMonoidal (presheafToSheaf J A) J.W
    Φ.sheafFiber Φ.presheafFiber

end

end CategoryTheory.GrothendieckTopology.Point
