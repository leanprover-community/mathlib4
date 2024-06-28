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
  exact :=
    { evaluation' :=
        { app := fun X => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Category.comp_id, Functor.map_inv, ← id_tensor_comp_tensor_id, Category.assoc,
              id_tensorHom, tensorHom_id,
              rightAdjointMate_comp_evaluation, ← MonoidalCategory.whiskerLeft_comp_assoc,
              IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp] }
      coevaluation' :=
        { app := fun X => η_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Functor.map_inv, Category.id_comp, ← id_tensor_comp_tensor_id,
              id_tensorHom, tensorHom_id, ← Category.assoc,
              coevaluation_comp_rightAdjointMate, Category.assoc, ← comp_whiskerRight,
              IsIso.inv_hom_id, id_whiskerRight, Category.comp_id] } }
#align category_theory.monoidal.functor_has_right_dual CategoryTheory.Monoidal.functorHasRightDual

instance rightRigidFunctorCategory [RightRigidCategory D] : RightRigidCategory (C ⥤ D) where
#align category_theory.monoidal.right_rigid_functor_category CategoryTheory.Monoidal.rightRigidFunctorCategory

instance functorHasLeftDual [LeftRigidCategory D] (F : C ⥤ D) : HasLeftDual F where
  leftDual :=
    { obj := fun X => ᘁ(F.obj X)
      map := fun f => ᘁ(F.map (inv f))
      map_comp := fun f g => by simp [comp_leftAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun X => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            simp [tensorHom_def, leftAdjointMate_comp_evaluation] }
      coevaluation' :=
        { app := fun X => η_ _ _
          naturality := fun X Y f => by
            dsimp
            simp [tensorHom_def, coevaluation_comp_leftAdjointMate_assoc] } }
#align category_theory.monoidal.functor_has_left_dual CategoryTheory.Monoidal.functorHasLeftDual

instance leftRigidFunctorCategory [LeftRigidCategory D] : LeftRigidCategory (C ⥤ D) where
#align category_theory.monoidal.left_rigid_functor_category CategoryTheory.Monoidal.leftRigidFunctorCategory

instance rigidFunctorCategory [RigidCategory D] : RigidCategory (C ⥤ D) where
#align category_theory.monoidal.rigid_functor_category CategoryTheory.Monoidal.rigidFunctorCategory

end CategoryTheory.Monoidal
