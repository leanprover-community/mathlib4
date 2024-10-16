/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the limit functor `lim : (J ⥤ C) ⥤ C` is lax monoidal,
i.e. there are morphisms
* `(𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.

## TODO
Now that we have oplax monoidal functors, assemble `Limits.colim` into an oplax monoidal functor.
-/

namespace CategoryTheory.Limits

open MonoidalCategory

universe v u w

noncomputable section

variable {J : Type w} [SmallCategory J] {C : Type u} [Category.{v} C] [HasLimitsOfShape J C]
  [MonoidalCategory.{v} C]

open Functor.LaxMonoidal

instance : (lim (J := J) (C := C)).LaxMonoidal where
  ε' :=
    limit.lift _
      { pt := _
        π := { app := fun _ => 𝟙 _ } }
  μ' F G :=
    limit.lift (F ⊗ G)
      { pt := limit F ⊗ limit G
        π :=
          { app := fun j => limit.π F j ⊗ limit.π G j
            naturality := fun j j' f => by
              dsimp
              simp only [Category.id_comp, ← tensor_comp, limit.w] } }
  μ'_natural_left := sorry
  μ'_natural_right := sorry
  associativity' := sorry
  left_unitality' := sorry
  right_unitality' := sorry
  /-(μ_natural := fun f g => by
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
    simp)-/

@[reassoc (attr := simp)]
lemma lim_ε_π (j : J) : ε (lim (J := J) (C := C)) ≫ limit.π _ j = 𝟙 _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma lim_μ_π (F G : J ⥤ C) (j : J) : μ lim F G ≫ limit.π _ j = limit.π F j ⊗ limit.π G j :=
  limit.lift_π _ _

end

end CategoryTheory.Limits
