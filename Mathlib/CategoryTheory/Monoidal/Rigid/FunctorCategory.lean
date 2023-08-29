/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

#align_import category_theory.monoidal.rigid.functor_category from "leanprover-community/mathlib"@"a6275694804455fe8995bd530e86b67ddab5cff1"

/-!
# Functors from a groupoid into a right/left rigid category form a right/left rigid category.

(Using the pointwise monoidal structure on the functor category.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C D : Type*} [Groupoid C] [Category D] [MonoidalCategory D]

instance functorHasRightDual [RightRigidCategory D] (F : C ⥤ D) : HasRightDual F where
  rightDual :=
    { obj := fun X => (F.obj X)ᘁ
      map := fun f => (F.map (inv f))ᘁ
      map_comp := fun f g => by simp [comp_rightAdjointMate] }
                                -- 🎉 no goals
  exact :=
    { evaluation' :=
        { app := fun X => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            -- ⊢ (F.map (inv f)ᘁ ⊗ F.map f) ≫ ε_ (F.obj Y) (F.obj Y)ᘁ = ε_ (F.obj X) (F.obj X …
            rw [Category.comp_id, Functor.map_inv, ← id_tensor_comp_tensor_id, Category.assoc,
              rightAdjointMate_comp_evaluation, ← Category.assoc, ← id_tensor_comp,
              IsIso.hom_inv_id, tensor_id, Category.id_comp] }
      coevaluation' :=
        { app := fun X => η_ _ _
          naturality := fun X Y f => by
            -- ⊢ 𝟙 (𝟙_ D) ≫ η_ (F.obj Y) (F.obj Y)ᘁ = η_ (F.obj X) (F.obj X)ᘁ ≫ (F.map f ⊗ F. …
            dsimp
            rw [Functor.map_inv, Category.id_comp, ← id_tensor_comp_tensor_id, ← Category.assoc,
              coevaluation_comp_rightAdjointMate, Category.assoc, ← comp_tensor_id,
              IsIso.inv_hom_id, tensor_id, Category.comp_id] } }
#align category_theory.monoidal.functor_has_right_dual CategoryTheory.Monoidal.functorHasRightDual

instance rightRigidFunctorCategory [RightRigidCategory D] : RightRigidCategory (C ⥤ D) where
#align category_theory.monoidal.right_rigid_functor_category CategoryTheory.Monoidal.rightRigidFunctorCategory

instance functorHasLeftDual [LeftRigidCategory D] (F : C ⥤ D) : HasLeftDual F where
  leftDual :=
    { obj := fun X => ᘁ(F.obj X)
      map := fun f => ᘁ(F.map (inv f))
      map_comp := fun f g => by simp [comp_leftAdjointMate] }
                                -- 🎉 no goals
  exact :=
    { evaluation' :=
        { app := fun X => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            -- ⊢ (F.map f ⊗ ᘁF.map (inv f)) ≫ ε_ (ᘁ(F.obj Y)) (F.obj Y) = ε_ (ᘁ(F.obj X)) (F. …
            rw [Category.comp_id, Functor.map_inv, ← tensor_id_comp_id_tensor, Category.assoc,
              leftAdjointMate_comp_evaluation, ← Category.assoc, ← comp_tensor_id,
              IsIso.hom_inv_id, tensor_id, Category.id_comp] }
      coevaluation' :=
        { app := fun X => η_ _ _
          naturality := fun X Y f => by
            -- ⊢ 𝟙 (𝟙_ D) ≫ η_ (ᘁ(F.obj Y)) (F.obj Y) = η_ (ᘁ(F.obj X)) (F.obj X) ≫ ((ᘁF.map  …
            dsimp
            rw [Functor.map_inv, Category.id_comp, ← tensor_id_comp_id_tensor, ← Category.assoc,
              coevaluation_comp_leftAdjointMate, Category.assoc, ← id_tensor_comp,
              IsIso.inv_hom_id, tensor_id, Category.comp_id] } }
#align category_theory.monoidal.functor_has_left_dual CategoryTheory.Monoidal.functorHasLeftDual

instance leftRigidFunctorCategory [LeftRigidCategory D] : LeftRigidCategory (C ⥤ D) where
#align category_theory.monoidal.left_rigid_functor_category CategoryTheory.Monoidal.leftRigidFunctorCategory

instance rigidFunctorCategory [RigidCategory D] : RigidCategory (C ⥤ D) where
#align category_theory.monoidal.rigid_functor_category CategoryTheory.Monoidal.rigidFunctorCategory

end CategoryTheory.Monoidal
