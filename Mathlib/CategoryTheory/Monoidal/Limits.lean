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

instance : (lim (J := J) (C := C)).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε :=
      limit.lift _
        { pt := _
          π := { app := fun _ => 𝟙 _ } })
    (μ := fun F G ↦
      limit.lift (F ⊗ G)
        { pt := limit F ⊗ limit G
          π :=
            { app := fun j => limit.π F j ⊗ₘ limit.π G j
              naturality := fun j j' f => by
                dsimp
                simp only [Category.id_comp, ← tensor_comp, limit.w] } })
    (μ_natural := fun f g ↦ limit.hom_ext (fun j ↦ by
      dsimp
      simp only [limit.lift_π, Cones.postcompose_obj_π, Monoidal.tensorHom_app, limit.lift_map,
        NatTrans.comp_app, Category.assoc, ← tensor_comp, limMap_π]))
    (associativity := fun F G H ↦ limit.hom_ext (fun j ↦ by
      dsimp
      simp only [tensorHom_id, limit.lift_map, Category.assoc, limit.lift_π,
        id_tensorHom]
      dsimp
      conv_lhs => rw [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc,
        limit.lift_π, tensor_whiskerLeft, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id,
        ← associator_naturality_right, ← tensorHom_def_assoc]
      dsimp
      conv_rhs => rw [tensorHom_def, ← whisker_exchange,
        ← MonoidalCategory.whiskerLeft_comp_assoc, limit.lift_π,
        whisker_exchange, ← associator_naturality_left_assoc]
      dsimp only
      conv_rhs => rw [tensorHom_def, MonoidalCategory.whiskerLeft_comp,
        ← associator_naturality_middle_assoc,
        ← associator_naturality_right, ← comp_whiskerRight_assoc,
        ← tensorHom_def, ← tensorHom_def_assoc]))
    (left_unitality := fun F ↦ limit.hom_ext (fun j ↦ by
      dsimp
      simp only [tensorHom_id, limit.lift_map, Category.assoc, limit.lift_π]
      dsimp
      simp only [tensorHom_def, id_whiskerLeft, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, ← comp_whiskerRight_assoc]
      erw [limit.lift_π]
      rw [id_whiskerRight, Category.id_comp]))
    (right_unitality := fun F ↦ limit.hom_ext (fun j ↦ by
      dsimp
      simp only [id_tensorHom, limit.lift_map, Category.assoc, limit.lift_π]
      dsimp
      simp only [tensorHom_def, ← whisker_exchange,
        MonoidalCategory.whiskerRight_id, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, ← MonoidalCategory.whiskerLeft_comp_assoc]
      erw [limit.lift_π]
      rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]))

@[reassoc (attr := simp)]
lemma lim_ε_π (j : J) : ε (lim (J := J) (C := C)) ≫ limit.π _ j = 𝟙 _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma lim_μ_π (F G : J ⥤ C) (j : J) : μ lim F G ≫ limit.π _ j = limit.π F j ⊗ₘ limit.π G j :=
  limit.lift_π _ _

end

end CategoryTheory.Limits
