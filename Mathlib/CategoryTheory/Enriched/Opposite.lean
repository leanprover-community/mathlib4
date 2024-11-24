/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
import Mathlib.CategoryTheory.Closed.Enrichment

/-!

# The opposite category of an enriched category

When a monoidal category `V` is braided, we may define the opposite `V`-category of a
`V`-cagtegory. The symmetry map is required to define the composition morphism.

-/

universe v₁ u₁ v u

namespace CategoryTheory

open BraidedCategory

/-- The underlying type of the enriched opposite category.

This takes `V` as an argument so that, if `C` is enriched over multiple categories,
the instances of the underlying categories on `ForgetEnrichment C` do not coincide -/
@[nolint unusedArguments]
structure eOpposite (V : Type u₁) (C : Type u) where
  as : C

namespace eOpposite

def op {V : Type u₁} {C : Type u} (x : C) : eOpposite V C := ⟨x⟩

def unop {V : Type u₁} {C : Type u} (x : eOpposite V C) : C := x.as

@[simp]
theorem op_of_unop (V : Type u₁) {C : Type u} (x : eOpposite V C) : op (unop x) = x := rfl

@[simp]
theorem unop_of_op (V : Type u₁) {C : Type u} (x : C) :  unop (V := V) (op x) = x := rfl

/-- The type-level equivalence between a type and its enriched opposite. -/
def equivToEnrichedOpposite (V : Type u₁) (C : Type u) : C ≃ eOpposite V C where
  toFun := op
  invFun := unop
  left_inv := by aesop_cat
  right_inv := by aesop_cat

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]
variable (C : Type u) [EnrichedCategory V C]

/-- The enriched category structure on `eOpposite V C` -/
instance EnrichedCategory.opposite : EnrichedCategory V (eOpposite V C) where
  Hom y x := EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right]

end eOpposite

end CategoryTheory
