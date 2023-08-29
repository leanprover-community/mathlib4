/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products

#align_import category_theory.limits.shapes.finite_products from "leanprover-community/mathlib"@"ac3ae212f394f508df43e37aa093722fa9b65d31"

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/


universe w v u

open CategoryTheory

open Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- A category has finite products if there exists a limit for every diagram
with shape `Discrete J`, where we have `[Finite J]`.

We require this condition only for `J = Fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
class HasFiniteProducts : Prop where
  /-- `C` has finite products -/
  out (n : ℕ) : HasLimitsOfShape (Discrete (Fin n)) C
#align category_theory.limits.has_finite_products CategoryTheory.Limits.HasFiniteProducts

/-- If `C` has finite limits then it has finite products. -/
instance (priority := 10) hasFiniteProducts_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteProducts C :=
  ⟨fun _ => inferInstance⟩
#align category_theory.limits.has_finite_products_of_has_finite_limits CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits

instance hasLimitsOfShape_discrete [HasFiniteProducts C] (ι : Type w) [Finite ι] :
    HasLimitsOfShape (Discrete ι) C := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  -- ⊢ HasLimitsOfShape (Discrete ι) C
  haveI : HasLimitsOfShape (Discrete (Fin n)) C := HasFiniteProducts.out n
  -- ⊢ HasLimitsOfShape (Discrete ι) C
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
  -- 🎉 no goals
#align category_theory.limits.has_limits_of_shape_discrete CategoryTheory.Limits.hasLimitsOfShape_discrete

/-- We can now write this for powers. -/
noncomputable example [HasFiniteProducts C] (X : C) : C :=
  ∏ fun _ : Fin 5 => X

/-- If a category has all products then in particular it has finite products.
-/
theorem hasFiniteProducts_of_hasProducts [HasProducts.{w} C] : HasFiniteProducts C :=
  ⟨fun _ => hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align category_theory.limits.has_finite_products_of_has_products CategoryTheory.Limits.hasFiniteProducts_of_hasProducts

/-- A category has finite coproducts if there exists a colimit for every diagram
with shape `Discrete J`, where we have `[Fintype J]`.

We require this condition only for `J = Fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
class HasFiniteCoproducts : Prop where
  /-- `C` has all finite coproducts -/
  out (n : ℕ) : HasColimitsOfShape (Discrete (Fin n)) C
#align category_theory.limits.has_finite_coproducts CategoryTheory.Limits.HasFiniteCoproducts

-- attribute [class] HasFiniteCoproducts Porting note: this doesn't seem necessary in Lean 4

instance hasColimitsOfShape_discrete [HasFiniteCoproducts C] (ι : Type w) [Finite ι] :
    HasColimitsOfShape (Discrete ι) C := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  -- ⊢ HasColimitsOfShape (Discrete ι) C
  haveI : HasColimitsOfShape (Discrete (Fin n)) C := HasFiniteCoproducts.out n
  -- ⊢ HasColimitsOfShape (Discrete ι) C
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
  -- 🎉 no goals
#align category_theory.limits.has_colimits_of_shape_discrete CategoryTheory.Limits.hasColimitsOfShape_discrete

/-- If `C` has finite colimits then it has finite coproducts. -/
instance (priority := 10) hasFiniteCoproducts_of_hasFiniteColimits [HasFiniteColimits C] :
    HasFiniteCoproducts C :=
  ⟨fun J => by infer_instance⟩
               -- 🎉 no goals
#align category_theory.limits.has_finite_coproducts_of_has_finite_colimits CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits

/-- If a category has all coproducts then in particular it has finite coproducts.
-/
theorem hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align category_theory.limits.has_finite_coproducts_of_has_coproducts CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts

end CategoryTheory.Limits
