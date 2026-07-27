/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Dual Functors for Rigid Categories

This file defines the left and right dual functors from a rigid monoidal category
to `(Cᵒᵖ)ᴹᵒᵖ` (the monoidal opposite of the opposite category). It also defines the double right
dual endofunctor for a right rigid monoidal category.

## Main definitions

* `leftDualFunctor C`: For a left rigid category, the functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sending
  `X` to `ᘁX` and `f` to `ᘁf`.
* `rightDualFunctor C`: For a right rigid category, the functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sending
  `X` to `Xᘁ` and `f` to `fᘁ`.
* `doubleRightDualFunctor C`: The functor `C ⥤ C` on a right rigid category sending
  `X` to `Xᘁᘁ` and `f` to `fᘁᘁ`.

## Future work

* Show that in a `RigidCategory`, these functors are monoidal equivalences.

-/

namespace CategoryTheory

open Category MonoidalCategory MonoidalOpposite Opposite

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section LeftRigid

variable [LeftRigidCategory C]

/-- The left dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simps obj map, expose]
public def leftDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (ᘁX))
  map f := (ᘁf).op.mop
  map_id X := by simp [leftAdjointMate_id]
  map_comp f g := by simp [comp_leftAdjointMate]

end LeftRigid

section RightRigid

variable [RightRigidCategory C]

/-- The right dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simps obj map, expose]
public def rightDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (Xᘁ))
  map f := (fᘁ).op.mop
  map_id X := by simp [rightAdjointMate_id]
  map_comp f g := by simp [comp_rightAdjointMate]

/-- The core monoidal structure on the right dual functor. -/
@[simps!, expose]
public def rightDualFunctorCoreMonoidal : (rightDualFunctor C).CoreMonoidal where
  εIso := (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).op.mop
  μIso X Y := (rightDualTensorIso X Y).op.mop
  μIso_hom_natural_left f Z := by
    refine MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj ?_)
    dsimp [rightDualFunctor, rightDualTensorIso, Iso.mop, Iso.op, Functor.mapIso, mopFunctor]
    rw [← tensorHom_id, rightDualIso_hom_naturality, ExactPairing.rightMate_tensor,
      Iso.cancel_iso_hom_left]
    simp
  μIso_hom_natural_right Z f := by
    refine MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj ?_)
    dsimp [rightDualFunctor, rightDualTensorIso, Iso.mop, Iso.op, Functor.mapIso, mopFunctor]
    rw [← id_tensorHom, rightDualIso_hom_naturality, ExactPairing.rightMate_tensor,
      Iso.cancel_iso_hom_left]
    simp
  associativity X Y Z := by
    refine MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj ?_)
    dsimp [rightDualFunctor, Iso.mop, Iso.op, Functor.mapIso, mopFunctor, rightDualTensorIso]
    rw [← id_tensorHom, ← Iso.refl_hom, ← rightDualIso_id, ← rightDualIso_tensor, assoc,
      rightDualIso_hom_trans, rightDualIso_hom_naturality, ← tensorHom_id, ← Iso.refl_hom,
      ← rightDualIso_id, ← rightDualIso_tensor, rightDualIso_hom_trans, Iso.cancel_iso_hom_left]
    apply ExactPairing.rightHom_ext _
    rw [ExactPairing.rightMate_comp_evaluation]
    simp only [ExactPairing.tensor_evaluation]
    monoidal
  left_unitality X := by
    refine MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj ?_)
    dsimp [rightDualFunctor, Iso.mop, Iso.op, Functor.mapIso, mopFunctor, rightDualTensorIso]
    rw [← id_tensorHom, ← Iso.refl_hom, ← rightDualIso_id, ← rightDualIso_tensor, assoc,
      rightDualIso_hom_trans, rightDualIso_hom_naturality, rightDualIso_id, Iso.refl_hom, id_comp]
    apply ExactPairing.rightHom_ext _
    rw [ExactPairing.rightMate_comp_evaluation]
    simp only [ExactPairing.tensor_evaluation, ExactPairing.unit_evaluation]
    monoidal
  right_unitality X := by
    refine MonoidalOpposite.hom_ext (Quiver.Hom.unop_inj ?_)
    dsimp [rightDualFunctor, Iso.mop, Iso.op, Functor.mapIso, mopFunctor, rightDualTensorIso]
    rw [← tensorHom_id, ← Iso.refl_hom, ← rightDualIso_id, ← rightDualIso_tensor, assoc,
      rightDualIso_hom_trans, rightDualIso_hom_naturality, rightDualIso_id, Iso.refl_hom, id_comp]
    apply ExactPairing.rightHom_ext _
    rw [ExactPairing.rightMate_comp_evaluation]
    simp only [ExactPairing.tensor_evaluation, ExactPairing.unit_evaluation]
    monoidal

/-- The monoidal structure on the right dual functor. -/
public instance rightDualFunctorMonoidal : (rightDualFunctor C).Monoidal :=
  (rightDualFunctorCoreMonoidal C).toMonoidal

/-- The double (right) dual endofunctor `X ↦ Xᘁᘁ`. -/
@[simps!, expose]
public def doubleRightDualFunctor : C ⥤ C :=
  rightDualFunctor C ⋙ (rightDualFunctor C).opMop

/-- The monoidal structure on the double-right-dual functor. -/
public instance doubleRightDualFunctorMonoidal : (doubleRightDualFunctor C).Monoidal :=
  inferInstanceAs (rightDualFunctor C ⋙ (rightDualFunctor C).opMop).Monoidal

end RightRigid

end CategoryTheory
