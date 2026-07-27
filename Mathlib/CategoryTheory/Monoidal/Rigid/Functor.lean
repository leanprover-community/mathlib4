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
to `(Cᵒᵖ)ᴹᵒᵖ` (the monoidal opposite of the opposite category).

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

open Category MonoidalCategory MonoidalOpposite Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

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

/-- The canonical core monoidal structure on the right dual functor. -/
public def rightDualFunctorCoreMonoidal : (rightDualFunctor C).CoreMonoidal where
  εIso := rightDualUnitIso.op.mop
  μIso X Y := (rightDualTensorIso X Y).op.mop
  μIso_hom_natural_left {X Y} f Z := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using (rightDualTensorIso_hom_naturality f (𝟙 Z)).symm
  μIso_hom_natural_right {X Y} Z f := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using (rightDualTensorIso_hom_naturality (𝟙 Z) f).symm
  associativity X Y Z := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (show (α_ X Y Z).homᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).hom ≫
          (Zᘁ : C) ◁ (rightDualTensorIso X Y).hom =
        (rightDualTensorIso X (Y ⊗ Z)).hom ≫
          (rightDualTensorIso Y Z).hom ▷ Xᘁ ≫
            (α_ (Zᘁ : C) (Yᘁ : C) (Xᘁ : C)).hom from by
        let pX : ExactPairing X Xᘁ := inferInstance
        let pY : ExactPairing Y Yᘁ := inferInstance
        let pZ : ExactPairing Z Zᘁ := inferInstance
        let pXY : ExactPairing (X ⊗ Y) (X ⊗ Y)ᘁ := inferInstance
        let pYZ : ExactPairing (Y ⊗ Z) (Y ⊗ Z)ᘁ := inferInstance
        let pA : ExactPairing ((X ⊗ Y) ⊗ Z) ((X ⊗ Y) ⊗ Z)ᘁ := inferInstance
        let pB : ExactPairing (X ⊗ (Y ⊗ Z)) (X ⊗ (Y ⊗ Z))ᘁ := inferInstance
        change pA.rightMate pB (α_ X Y Z).hom ≫
            (rightDualIso pA (pXY.tensorOf pZ)).hom ≫
              (Zᘁ : C) ◁ (rightDualIso pXY (pX.tensorOf pY)).hom =
          (rightDualIso pB (pX.tensorOf pYZ)).hom ≫
            (rightDualIso pYZ (pY.tensorOf pZ)).hom ▷ Xᘁ ≫
              (α_ (Zᘁ : C) (Yᘁ : C) (Xᘁ : C)).hom
        have hL := rightDualIso_tensor pXY pZ (pX.tensorOf pY) pZ
        simp only [rightDualIso_id, Iso.refl_hom, id_tensorHom] at hL
        rw [← hL, rightDualIso_hom_trans]
        rw [rightDualIso_hom_naturality pA ((pX.tensorOf pY).tensorOf pZ)
          pB (pX.tensorOf (pY.tensorOf pZ)),
          ExactPairing.rightMate_associator]
        have hR := rightDualIso_tensor pX pYZ pX (pY.tensorOf pZ)
        simp only [rightDualIso_id, Iso.refl_hom, tensorHom_id] at hR
        rw [← Category.assoc, ← hR, rightDualIso_hom_trans])
  left_unitality X := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (show (ρ_ Xᘁ).inv =
        (λ_ X).homᘁ ≫ (rightDualTensorIso (𝟙_ C) X).hom ≫
          (Xᘁ : C) ◁ rightDualUnitIso.hom from by
        let pX : ExactPairing X Xᘁ := inferInstance
        let pI : ExactPairing (𝟙_ C) (𝟙_ C)ᘁ := inferInstance
        let pIX : ExactPairing (𝟙_ C ⊗ X) (𝟙_ C ⊗ X)ᘁ := inferInstance
        change (ρ_ Xᘁ).inv =
          pIX.rightMate pX (λ_ X).hom ≫
            (rightDualIso pIX (pI.tensorOf pX)).hom ≫
            (Xᘁ : C) ◁ (rightDualIso pI exactPairingUnit).hom
        have h := rightDualIso_tensor pI pX exactPairingUnit pX
        simp only [rightDualIso_id, Iso.refl_hom, id_tensorHom] at h
        rw [← h, rightDualIso_hom_trans,
          rightDualIso_hom_naturality pIX (exactPairingUnit.tensorOf pX) pX pX,
          rightDualIso_id, Iso.refl_hom, Category.id_comp]
        exact (ExactPairing.rightMate_leftUnitor pX).symm)
  right_unitality X := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (show (λ_ Xᘁ).inv =
        (ρ_ X).homᘁ ≫ (rightDualTensorIso X (𝟙_ C)).hom ≫
          rightDualUnitIso.hom ▷ Xᘁ from by
        let pX : ExactPairing X Xᘁ := inferInstance
        let pI : ExactPairing (𝟙_ C) (𝟙_ C)ᘁ := inferInstance
        let pXI : ExactPairing (X ⊗ 𝟙_ C) (X ⊗ 𝟙_ C)ᘁ := inferInstance
        change (λ_ Xᘁ).inv =
          pXI.rightMate pX (ρ_ X).hom ≫
            (rightDualIso pXI (pX.tensorOf pI)).hom ≫
            (rightDualIso pI exactPairingUnit).hom ▷ Xᘁ
        have h := rightDualIso_tensor pX pI pX exactPairingUnit
        simp only [rightDualIso_id, Iso.refl_hom, tensorHom_id] at h
        rw [← h, rightDualIso_hom_trans,
          rightDualIso_hom_naturality pXI (pX.tensorOf exactPairingUnit) pX pX,
          rightDualIso_id, Iso.refl_hom, Category.id_comp]
        exact (ExactPairing.rightMate_rightUnitor pX).symm)

/-- The canonical monoidal structure on the right dual functor. -/
@[instance_reducible, instance]
public def rightDualFunctorMonoidal : (rightDualFunctor C).Monoidal :=
  (rightDualFunctorCoreMonoidal C).toMonoidal

/-- The functor `X ↦ Xᘁᘁ`. -/
@[simps!, expose]
public def doubleRightDualFunctor : C ⥤ C :=
  rightDualFunctor C ⋙ (rightDualFunctor C).opMop

/-- The canonical monoidal structure on the double-right-dual functor. -/
public instance doubleRightDualFunctorMonoidal : (doubleRightDualFunctor C).Monoidal :=
  inferInstanceAs (rightDualFunctor C ⋙ (rightDualFunctor C).opMop).Monoidal

end RightRigid

end CategoryTheory
