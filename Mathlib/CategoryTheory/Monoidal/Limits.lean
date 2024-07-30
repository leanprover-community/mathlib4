/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Functorial
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the functorial association `F ↦ limit F` is lax monoidal,
i.e. there are morphisms
* `limLax.ε : (𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `limLax.μ : limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.

## TODO
Now that we have oplax monoidal functors, assemble `Limits.colim` into an oplax monoidal functor.
-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Limits

universe v u w

noncomputable section

variable {J : Type w} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasLimitsOfShape J C]

instance limitFunctorial : Functorial fun F : J ⥤ C => limit F where
  map' := Limits.lim.map

@[simp]
theorem limitFunctorial_map {F G : J ⥤ C} (α : F ⟶ G) :
    map (fun F : J ⥤ C => limit F) α = Limits.lim.map α :=
  rfl

variable [MonoidalCategory.{v} C]

@[simps]
instance limitLaxMonoidal : LaxMonoidal fun F : J ⥤ C => limit F := .ofTensorHom
  (ε :=
    limit.lift _
      { pt := _
        π := { app := fun j => 𝟙 _ } })
  (μ := fun F G =>
    limit.lift (F ⊗ G)
      { pt := limit F ⊗ limit G
        π :=
          { app := fun j => limit.π F j ⊗ limit.π G j
            naturality := fun j j' f => by
              dsimp
              simp only [Category.id_comp, ← tensor_comp, limit.w] } })
  (μ_natural := fun f g => by
    ext; dsimp
    simp only [limit.lift_π, Cones.postcompose_obj_π, Monoidal.tensorHom_app, limit.lift_map,
      NatTrans.comp_app, Category.assoc, ← tensor_comp, limMap_π])
  (associativity := fun X Y Z => by
    ext j; dsimp
    simp only [limit.lift_π, Cones.postcompose_obj_π, Monoidal.associator_hom_app, limit.lift_map,
      NatTrans.comp_app, Category.assoc]
    slice_lhs 2 2 => rw [← tensor_id_comp_id_tensor]
    slice_lhs 1 2 =>
      rw [← comp_tensor_id, limit.lift_π]
      dsimp
    slice_lhs 1 2 => rw [tensor_id_comp_id_tensor]
    conv_lhs => rw [associator_naturality]
    conv_rhs => rw [← id_tensor_comp_tensor_id (limit.π (Y ⊗ Z) j)]
    slice_rhs 2 3 =>
      rw [← id_tensor_comp, limit.lift_π]
      dsimp
    dsimp; rw [id_tensor_comp_tensor_id])
  (left_unitality := fun X => by
    ext j; dsimp
    simp only [limit.lift_map, Category.assoc, limit.lift_π, Cones.postcompose_obj_pt,
      Cones.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj, Monoidal.tensorObj_obj,
      Monoidal.tensorUnit_obj, Monoidal.leftUnitor_hom_app]
    conv_rhs => rw [← tensor_id_comp_id_tensor (limit.π X j)]
    slice_rhs 1 2 =>
      rw [← comp_tensor_id]
      erw [limit.lift_π]
      dsimp
    slice_rhs 2 3 => rw [id_tensorHom, leftUnitor_naturality]
    simp)
  (right_unitality := fun X => by
    ext j; dsimp
    simp only [limit.lift_map, Category.assoc, limit.lift_π, Cones.postcompose_obj_pt,
      Cones.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj, Monoidal.tensorObj_obj,
      Monoidal.tensorUnit_obj, Monoidal.rightUnitor_hom_app]
    conv_rhs => rw [← id_tensor_comp_tensor_id _ (limit.π X j)]
    slice_rhs 1 2 =>
      rw [← id_tensor_comp]
      erw [limit.lift_π]
      dsimp
    slice_rhs 2 3 => rw [tensorHom_id, rightUnitor_naturality]
    simp)

/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def limLax : LaxMonoidalFunctor (J ⥤ C) C :=
  LaxMonoidalFunctor.of fun F : J ⥤ C => limit F

@[simp]
theorem limLax_obj (F : J ⥤ C) : limLax.obj F = limit F :=
  rfl

theorem limLax_obj' (F : J ⥤ C) : limLax.obj F = lim.obj F :=
  rfl

@[simp]
theorem limLax_map {F G : J ⥤ C} (α : F ⟶ G) : limLax.map α = lim.map α :=
  rfl

@[simp]
theorem limLax_ε :
    (@limLax J _ C _ _ _).ε =
      limit.lift _
        { pt := _
          π := { app := fun j => 𝟙 _ } } :=
  rfl

@[simp]
theorem limLax_μ (F G : J ⥤ C) :
    (@limLax J _ C _ _ _).μ F G =
      limit.lift (F ⊗ G)
        { pt := limit F ⊗ limit G
          π :=
            { app := fun j => limit.π F j ⊗ limit.π G j
              naturality := fun j j' f => by
                dsimp
                simp only [Category.id_comp, ← tensor_comp, limit.w] } } :=
  rfl

end

end CategoryTheory.Limits
