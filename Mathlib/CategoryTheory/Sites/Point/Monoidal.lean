/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Fiber functors are monoidal

Let `Φ` be a point of a site `(C, J)`. Let `A` be a monoidal category where
the tensor product commutes with filtered colimits in both variables.
We show that the fiber functors `Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A`
and `Φ.sheafFiber : Sheaf J A ⥤ A` are monoidal.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits MonoidalCategory Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [MonoidalCategory A] [HasColimitsOfSize.{w, w} A]

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
  Final.preservesColimitsOfShape_of_final (fromFilteredFinalModel.{w} _) _

instance (M : A) :
    PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ ((curriedTensor A).obj M) :=
  Final.preservesColimitsOfShape_of_final (fromFilteredFinalModel.{w} _) _

attribute [local instance] FinallySmallFiltered.isConnected in
instance : IsIso (OplaxMonoidal.η (Φ.presheafFiber (A := A))) :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitConstCocone _ (𝟙_ A))).isIso_hom

attribute [local instance] FinallySmallFiltered.isSifted in
attribute [local simp] tensorHom_def toPresheafFiber OplaxMonoidal.δ presheafFiberDesc in
instance (P₁ P₂ : Cᵒᵖ ⥤ A) :
    IsIso (OplaxMonoidal.δ Φ.presheafFiber P₁ P₂) := by
  let e := IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    ((Final.isColimitWhiskerEquiv (diag _) _ ).2
      (isColimitOfPreserves₂ (curriedTensor A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P₁))
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P₂))))
  rw [show OplaxMonoidal.δ Φ.presheafFiber P₁ P₂ =
      colimMap { app _ := by exact 𝟙 _ } ≫ e.hom by cat_disch,
    isIso_comp_right_iff]
  apply +allowSynthFailures isIso_colimMap
  rw [NatTrans.isIso_iff_isIso_app]
  intro
  dsimp
  infer_instance

noncomputable instance : (Φ.presheafFiber (A := A)).Monoidal :=
  .ofOplaxMonoidal _

attribute [local instance] Sheaf.monoidalCategory

variable {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
  [(forget A).ReflectsIsomorphisms]
  [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]
  [(J.W (A := A)).IsMonoidal]

noncomputable instance : (Φ.sheafFiber (A := A)).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (presheafToSheaf J A) J.W
    Φ.sheafFiber Φ.presheafFiber

instance : NatTrans.IsMonoidal (Φ.presheafToSheafCompSheafFiber A).hom :=
  Localization.Monoidal.lifting_isMonoidal (presheafToSheaf J A) J.W
    Φ.sheafFiber Φ.presheafFiber

end CategoryTheory.GrothendieckTopology.Point
