/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor

/-!
# The Drinfeld isomorphism

This file defines the Drinfeld isomorphism from the identity functor to the double right dual
functor in a braided right rigid monoidal category, and proves that it is monoidal in a symmetric
monoidal category.

## Main definitions

* `drinfeldIso`: the Drinfeld isomorphism from the identity to the double right dual.
* `drinfeldIso_isMonoidal`: the Drinfeld isomorphism is monoidal in a symmetric monoidal category.
-/

namespace CategoryTheory

open BraidedCategory Category MonoidalCategory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The Drinfeld isomorphism from the identity functor to the double right dual functor
in a braided right rigid monoidal category. -/
@[simps!, expose]
public def drinfeldIso [BraidedCategory C] : 𝟭 C ≅ doubleRightDualFunctor C :=
  NatIso.ofComponents
    (fun X ↦ rightDualIso (exactPairing_swap X Xᘁ) HasRightDual.exact)
    (fun f ↦ by
      erw [← rightDualIso_hom_naturality, ExactPairing.rightMate_swap_rightMate]
      rfl)

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The Drinfeld isomorphism is monoidal in a symmetric monoidal category. This does not hold for a
general braided category. -/
public instance drinfeldIso_isMonoidal :
    NatTrans.IsMonoidal (drinfeldIso (C := C)).hom where
  unit := by
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
    simp only [drinfeldIso, Functor.id_obj, NatIso.ofComponents_hom_app,
      doubleRightDualFunctor_ε]
    erw [← rightDualIso_hom_naturality (pX₁ := exactPairing_swap (𝟙_ C) (𝟙_ C)ᘁ)]
    rw [ExactPairing.rightMate_eq_of_evaluation_eq
      (pY₂ := exactPairing_swap (𝟙_ C) (𝟙_ C)) (h := by
        rw [exactPairingSwap_evaluation exactPairingUnit,
          ExactPairing.unit_evaluation, braiding_tensorUnit_left]
        monoidal)]
    simp [rightDualIso, ExactPairing.rightMate_swap_rightMate]
  tensor X Y := by
    simp only [Functor.id_obj, drinfeldIso, NatIso.ofComponents_hom_app,
      ← rightDualIso_tensor, doubleRightDualFunctor_μ, rightDualTensorIso,
      rightDualIso_inv,
      ← rightDualIso_hom_naturality
        (pX₁ := exactPairing_swap (X ⊗ Y) (X ⊗ Y)ᘁ),
      ← Category.assoc,
      ExactPairing.rightMate_eq_of_evaluation_eq
        (h := ExactPairing.tensorOf_swap_evaluation
          HasRightDual.exact HasRightDual.exact)]
    rw [rightDualIso_id]
    simp only [Iso.refl_hom, Category.comp_id]
    rw [cancel_mono]
    simp [rightDualIso, ExactPairing.rightMate_swap_rightMate]

end Symmetric

end CategoryTheory
