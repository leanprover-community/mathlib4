/-
Copyright (c) 2026 Pedro Cortes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Cortes
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CommComon_

/-!
# Tensor-braid swap coherence in symmetric monoidal categories

The canonical rearrangement `tensorμ` intertwines the braiding on `A ⊗ Y`
with the pair of braidings on `A` and `Y` in any symmetric monoidal
category. This is the sibling of `CategoryTheory.MonObj.mul_braiding`
(`Mathlib.CategoryTheory.Monoidal.Mon_`), and yields the tensor-product
`IsCommComonObj` instance.

Placed in its own file to avoid an instance-diamond issue in `Braided/Basic.lean`,
where the ambient `[BraidedCategory C]` variable clashes with the
`[SymmetricCategory C]`-derived `BraidedCategory` instance, confusing
`rw [SymmetricCategory.symmetry]` motive extraction on Lean v4.30.0-rc2.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- **Symmetric-monoidal tensor-braid swap coherence.**
The canonical rearrangement `tensorμ` intertwines the braiding on `A ⊗ Y`
with the pair of braidings on `A` and `Y`. Both sides implement the
permutation `(a₁, a₂, y₁, y₂) ↦ (a₂, y₂, a₁, y₁)`. Sibling of
`MonObj.mul_braiding` (`Mathlib.CategoryTheory.Monoidal.Mon_`). -/
@[reassoc]
theorem MonoidalCategory.tensorμ_braid_swap (A Y : C) :
    tensorμ A A Y Y ≫ (β_ (A ⊗ Y) (A ⊗ Y)).hom =
      ((β_ A A).hom ⊗ₘ (β_ Y Y).hom) ≫ tensorμ A A Y Y := by
  simp only [tensorμ, Category.assoc,
    BraidedCategory.braiding_tensor_right_hom,
    BraidedCategory.braiding_tensor_left_hom, comp_whiskerRight,
    whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
                       SymmetricCategory.symmetry]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc,
             tensorHom_def, tensor_whiskerLeft, whiskerRight_tensor]
  monoidal

open scoped ComonObj

/-- The tensor product of two commutative comonoid objects is again a
commutative comonoid object. The proof reduces the commutativity
equation for `Δ[A ⊗ B]` to `tensorμ_braid_swap` plus the two pointwise
commutativity hypotheses `IsCommComonObj.comul_comm A`, `.comul_comm B`. -/
instance (A B : C) [ComonObj A] [ComonObj B]
    [IsCommComonObj A] [IsCommComonObj B] : IsCommComonObj (A ⊗ B) where
  comul_comm := by
    rw [Comon.tensorObj_comul, Category.assoc,
        MonoidalCategory.tensorμ_braid_swap,
        ← Category.assoc, tensorHom_comp_tensorHom,
        IsCommComonObj.comul_comm A, IsCommComonObj.comul_comm B]

end CategoryTheory
