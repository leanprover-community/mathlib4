/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Functorial
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Limits.HasLimits

#align_import category_theory.monoidal.limits from "leanprover-community/mathlib"@"744d59af0b28d0c42f631038627df9b85ae1d1ce"

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the functorial association `F ↦ limit F` is lax monoidal,
i.e. there are morphisms
* `limLax.ε : (𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `limLax.μ : limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.
-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Limits

universe v u

noncomputable section

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C] [HasLimits C]

instance limitFunctorial : Functorial fun F : J ⥤ C => limit F where
  map' := Limits.lim.map
#align category_theory.limits.limit_functorial CategoryTheory.Limits.limitFunctorial

@[simp]
theorem limitFunctorial_map {F G : J ⥤ C} (α : F ⟶ G) :
    map (fun F : J ⥤ C => limit F) α = Limits.lim.map α :=
  rfl
#align category_theory.limits.limit_functorial_map CategoryTheory.Limits.limitFunctorial_map

variable [MonoidalCategory.{v} C]

@[simps]
instance limitLaxMonoidal : LaxMonoidal fun F : J ⥤ C => limit F where
  ε :=
    limit.lift _
      { pt := _
        π := { app := fun j => 𝟙 _ } }
  μ F G :=
    limit.lift (F ⊗ G)
      { pt := limit F ⊗ limit G
        π :=
          { app := fun j => limit.π F j ⊗ limit.π G j
            naturality := fun j j' f => by
              dsimp
              -- ⊢ 𝟙 (limit F ⊗ limit G) ≫ (limit.π F j' ⊗ limit.π G j') = (limit.π F j ⊗ limit …
              simp only [Category.id_comp, ← tensor_comp, limit.w] } }
              -- 🎉 no goals
  μ_natural f g := by
    ext; dsimp
    -- ⊢ ((map (fun F => limit F) f ⊗ map (fun F => limit F) g) ≫ (fun F G => limit.l …
         -- ⊢ ((limMap f ⊗ limMap g) ≫ limit.lift (Y✝ ⊗ Y'✝) { pt := limit Y✝ ⊗ limit Y'✝, …
    simp only [limit.lift_π, Cones.postcompose_obj_π, Monoidal.tensorHom_app, limit.lift_map,
      NatTrans.comp_app, Category.assoc, ← tensor_comp, limMap_π]
  associativity X Y Z := by
    ext j; dsimp
    -- ⊢ (((fun F G => limit.lift (F ⊗ G) { pt := limit F ⊗ limit G, π := NatTrans.mk …
           -- ⊢ ((limit.lift (X ⊗ Y) { pt := limit X ⊗ limit Y, π := NatTrans.mk fun j => li …
    simp only [limit.lift_π, Cones.postcompose_obj_π, Monoidal.associator_hom_app, limit.lift_map,
      NatTrans.comp_app, Category.assoc]
    slice_lhs 2 2 => rw [← tensor_id_comp_id_tensor]
    -- ⊢ (limit.lift (X ⊗ Y) { pt := limit X ⊗ limit Y, π := NatTrans.mk fun j => lim …
    slice_lhs 1 2 =>
      rw [← comp_tensor_id, limit.lift_π]
      dsimp
    slice_lhs 1 2 => rw [tensor_id_comp_id_tensor]
    -- ⊢ ((limit.π X j ⊗ limit.π Y j) ⊗ limit.π Z j) ≫ (α_ (X.obj j) (Y.obj j) (Z.obj …
    conv_lhs => rw [associator_naturality]
    -- ⊢ (α_ (limit X) (limit Y) (limit Z)).hom ≫ (limit.π X j ⊗ limit.π Y j ⊗ limit. …
    conv_rhs => rw [← id_tensor_comp_tensor_id (limit.π (Y ⊗ Z) j)]
    -- ⊢ (α_ (limit X) (limit Y) (limit Z)).hom ≫ (limit.π X j ⊗ limit.π Y j ⊗ limit. …
    slice_rhs 2 3 =>
      rw [← id_tensor_comp, limit.lift_π]
      dsimp
    dsimp; simp
    -- ⊢ (α_ (limit X) (limit Y) (limit Z)).hom ≫ (limit.π X j ⊗ limit.π Y j ⊗ limit. …
           -- 🎉 no goals
  left_unitality X := by
    ext j; dsimp
    -- ⊢ (λ_ (limit X)).hom ≫ limit.π X j = ((limit.lift ((Functor.const J).obj tenso …
           -- ⊢ (λ_ (limit X)).hom ≫ limit.π X j = ((limit.lift ((Functor.const J).obj tenso …
    simp
    -- ⊢ (λ_ (limit X)).hom ≫ limit.π X j = (limit.lift ((Functor.const J).obj tensor …
    conv_rhs => rw [← tensor_id_comp_id_tensor (limit.π X j)]
    -- ⊢ (λ_ (limit X)).hom ≫ limit.π X j = (limit.lift ((Functor.const J).obj tensor …
    slice_rhs 1 2 =>
      rw [← comp_tensor_id]
      erw [limit.lift_π]
      dsimp
    slice_rhs 2 3 => rw [leftUnitor_naturality]
    -- ⊢ (λ_ (limit X)).hom ≫ limit.π X j = (𝟙 tensorUnit' ⊗ 𝟙 (limit X)) ≫ (λ_ (limi …
    simp
    -- 🎉 no goals
  right_unitality X := by
    ext j; dsimp
    -- ⊢ (ρ_ (limit X)).hom ≫ limit.π X j = ((𝟙 (limit X) ⊗ limit.lift ((Functor.cons …
           -- ⊢ (ρ_ (limit X)).hom ≫ limit.π X j = ((𝟙 (limit X) ⊗ limit.lift ((Functor.cons …
    simp
    -- ⊢ (ρ_ (limit X)).hom ≫ limit.π X j = (𝟙 (limit X) ⊗ limit.lift ((Functor.const …
    conv_rhs => rw [← id_tensor_comp_tensor_id _ (limit.π X j)]
    -- ⊢ (ρ_ (limit X)).hom ≫ limit.π X j = (𝟙 (limit X) ⊗ limit.lift ((Functor.const …
    slice_rhs 1 2 =>
      rw [← id_tensor_comp]
      erw [limit.lift_π]
      dsimp
    slice_rhs 2 3 => rw [rightUnitor_naturality]
    -- ⊢ (ρ_ (limit X)).hom ≫ limit.π X j = (𝟙 (limit X) ⊗ 𝟙 tensorUnit') ≫ (ρ_ (limi …
    simp
    -- 🎉 no goals
#align category_theory.limits.limit_lax_monoidal CategoryTheory.Limits.limitLaxMonoidal

/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def limLax : LaxMonoidalFunctor (J ⥤ C) C :=
  LaxMonoidalFunctor.of fun F : J ⥤ C => limit F
#align category_theory.limits.lim_lax CategoryTheory.Limits.limLax

@[simp]
theorem limLax_obj (F : J ⥤ C) : limLax.obj F = limit F :=
  rfl
#align category_theory.limits.lim_lax_obj CategoryTheory.Limits.limLax_obj

theorem limLax_obj' (F : J ⥤ C) : limLax.obj F = lim.obj F :=
  rfl
#align category_theory.limits.lim_lax_obj' CategoryTheory.Limits.limLax_obj'

@[simp]
theorem limLax_map {F G : J ⥤ C} (α : F ⟶ G) : limLax.map α = lim.map α :=
  rfl
#align category_theory.limits.lim_lax_map CategoryTheory.Limits.limLax_map

@[simp]
theorem limLax_ε :
    (@limLax J _ C _ _ _).ε =
      limit.lift _
        { pt := _
          π := { app := fun j => 𝟙 _ } } :=
  rfl
#align category_theory.limits.lim_lax_ε CategoryTheory.Limits.limLax_ε

@[simp]
theorem limLax_μ (F G : J ⥤ C) :
    (@limLax J _ C _ _ _).μ F G =
      limit.lift (F ⊗ G)
        { pt := limit F ⊗ limit G
          π :=
            { app := fun j => limit.π F j ⊗ limit.π G j
              naturality := fun j j' f => by
                dsimp
                -- ⊢ 𝟙 (limit F ⊗ limit G) ≫ (limit.π F j' ⊗ limit.π G j') = (limit.π F j ⊗ limit …
                simp only [Category.id_comp, ← tensor_comp, limit.w] } } :=
                -- 🎉 no goals
  rfl
#align category_theory.limits.lim_lax_μ CategoryTheory.Limits.limLax_μ

end

end CategoryTheory.Limits
