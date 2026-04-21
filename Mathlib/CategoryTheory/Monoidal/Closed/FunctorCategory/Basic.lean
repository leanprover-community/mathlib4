/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.FunctorCategory

/-!
# Functor categories are monoidal closed

Let `C` be a monoidal closed category. Let `J` be a category. In this file,
we obtain that the category `J ⥤ C` is monoidal closed if `C` has suitable
limits.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory

namespace MonoidalClosed

namespace FunctorCategory

open Enriched.FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {J : Type u₂} [Category.{v₂} J]
  [∀ (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom C F₁ F₂]

attribute [local simp] enrichedCategorySelf_hom

section

variable {F₁ F₂ F₂' F₃ F₃' : J ⥤ C}

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃)` when `F₁`, `F₂`
and `F₃` are functors `J ⥤ C`, and `C` is monoidal closed. -/
noncomputable def homEquiv : (F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  toFun f :=
    { app j := end_.lift (fun k ↦ F₂.map k.hom ≫ curry (f.app k.right))
        (fun k₁ k₂ φ ↦ by
          dsimp
          simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
            enrichedOrdinaryCategorySelf_eHomWhiskerRight]
          rw [← curry_natural_left_assoc, ← curry_natural_left_assoc,
            ← curry_natural_right, curry_pre_app, Category.assoc,
            ← f.naturality φ.right, Monoidal.tensorObj_map, tensorHom_def_assoc,
            ← Under.w φ, Functor.map_comp, MonoidalCategory.whiskerLeft_comp_assoc,
            whisker_exchange_assoc]) }
  invFun g :=
    { app j := uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)))
      naturality j j' φ := by
        dsimp
        rw [← uncurry_natural_right, tensorHom_def'_assoc, ← uncurry_pre_app,
          ← uncurry_natural_left, Category.assoc, Category.assoc,
          NatTrans.naturality_assoc, functorEnrichedHom_map,
          end_.lift_π_assoc, enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        dsimp
        rw [pre_id, NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
          Functor.map_id, Category.comp_id, Category.comp_id]
        congr 2
        dsimp
        rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight,
          ← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        let α : Under.mk (𝟙 j) ⟶ (Under.map φ).obj (Under.mk (𝟙 j')) := Under.homMk φ
        exact (enrichedHom_condition C (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₃) α).symm }
  left_inv f := by cat_disch
  right_inv g := by
    ext j
    dsimp
    ext k
    -- this following list was obtained by
    -- `simp? [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Under.map, Comma.mapLeft]`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, enrichedCategorySelf_hom,
      curry_uncurry, NatTrans.naturality_assoc, functorEnrichedHom_obj, functorEnrichedHom_map,
      Under.map, Comma.mapLeft, Functor.const_obj_obj, Functor.id_obj, Discrete.natTrans_app,
      StructuredArrow.left_eq_id, end_.lift_π, Under.mk_right, Under.mk_hom, Iso.refl_inv,
      NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerRight, pre_id, Iso.refl_hom,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Functor.map_id, Category.comp_id]
    congr
    simp

lemma homEquiv_naturality_two_symm (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃) :
    homEquiv.symm (f₂ ≫ g) = F₁ ◁ f₂ ≫ homEquiv.symm g := by
  dsimp [homEquiv]
  ext j
  simp [← uncurry_natural_left]

set_option backward.isDefEq.respectTransparency false in
lemma homEquiv_naturality_three [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
    (f : F₁ ⊗ F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') :
    homEquiv (f ≫ f₃) = homEquiv f ≫ (ρ_ _).inv ≫ _ ◁ functorHomEquiv _ f₃ ≫
      functorEnrichedComp C F₁ F₃ F₃' := by
  dsimp [homEquiv]
  ext j
  dsimp
  ext k
  rw [Category.assoc, Category.assoc, Category.assoc, end_.lift_π, enrichedComp_π,
    tensorHom_def, Category.assoc, whisker_exchange_assoc, whiskerRight_id_assoc,
    Iso.inv_hom_id_assoc, end_.lift_π_assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc, end_.lift_π,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
  dsimp
  rw [pre_id, NatTrans.id_app, Functor.map_id, Category.comp_id,
    Category.comp_id, homEquiv_apply_π, curry_natural_right]
  congr 2
  symm
  apply enrichedOrdinaryCategorySelf_eHomWhiskerLeft

end

variable [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
attribute [local instance] Enriched.FunctorCategory.functorEnrichedOrdinaryCategory

/-- When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint. -/
noncomputable def adj (F : J ⥤ C) :
    MonoidalCategory.tensorLeft F ⊣ (eHomFunctor _ _).obj ⟨F⟩ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

/-- When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint. -/
@[implicit_reducible]
noncomputable def closed (F : J ⥤ C) : Closed F where
  rightAdj := (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

/-- If `C` is monoidal closed and has suitable limits, the functor
category `J ⥤ C` is monoidal closed. -/
noncomputable scoped instance monoidalClosed : MonoidalClosed (J ⥤ C) where
  closed := closed

end FunctorCategory

end MonoidalClosed

end CategoryTheory
