/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.shapes.finite_products
! leanprover-community/mathlib commit ac3ae212f394f508df43e37aa093722fa9b65d31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Shapes.Products

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/


universe w v u

open CategoryTheory

open Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`out] [] -/
/-- A category has finite products if there is a chosen limit for every diagram
with shape `discrete J`, where we have `[finite J]`.

We require this condition only for `J = fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
class HasFiniteProducts : Prop where
  out (n : ℕ) : HasLimitsOfShape (Discrete (Fin n)) C
#align category_theory.limits.has_finite_products CategoryTheory.Limits.HasFiniteProducts

/-- If `C` has finite limits then it has finite products. -/
instance (priority := 10) hasFiniteProducts_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteProducts C :=
  ⟨fun n => inferInstance⟩
#align category_theory.limits.has_finite_products_of_has_finite_limits CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits

instance hasLimitsOfShape_discrete [HasFiniteProducts C] (ι : Type w) [Finite ι] :
    HasLimitsOfShape (Discrete ι) C :=
  by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  haveI := has_finite_products.out C n
  exact has_limits_of_shape_of_equivalence (discrete.equivalence e.symm)
#align category_theory.limits.has_limits_of_shape_discrete CategoryTheory.Limits.hasLimitsOfShape_discrete

/-- We can now write this for powers. -/
noncomputable example [HasFiniteProducts C] (X : C) : C :=
  ∏ fun i : Fin 5 => X

/-- If a category has all products then in particular it has finite products.
-/
theorem hasFiniteProducts_of_hasProducts [HasProducts.{w} C] : HasFiniteProducts C :=
  ⟨fun n => hasLimitsOfShapeOfEquivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align category_theory.limits.has_finite_products_of_has_products CategoryTheory.Limits.hasFiniteProducts_of_hasProducts

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`out] [] -/
/-- A category has finite coproducts if there is a chosen colimit for every diagram
with shape `discrete J`, where we have `[fintype J]`.

We require this condition only for `J = fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
class HasFiniteCoproducts : Prop where
  out (n : ℕ) : HasColimitsOfShape (Discrete (Fin n)) C
#align category_theory.limits.has_finite_coproducts CategoryTheory.Limits.HasFiniteCoproducts

attribute [class] has_finite_coproducts

instance hasColimitsOfShape_discrete [HasFiniteCoproducts C] (ι : Type w) [Finite ι] :
    HasColimitsOfShape (Discrete ι) C :=
  by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  haveI := has_finite_coproducts.out C n
  exact has_colimits_of_shape_of_equivalence (discrete.equivalence e.symm)
#align category_theory.limits.has_colimits_of_shape_discrete CategoryTheory.Limits.hasColimitsOfShape_discrete

/-- If `C` has finite colimits then it has finite coproducts. -/
instance (priority := 10) hasFiniteCoproducts_of_hasFiniteColimits [HasFiniteColimits C] :
    HasFiniteCoproducts C :=
  ⟨fun J => by infer_instance⟩
#align category_theory.limits.has_finite_coproducts_of_has_finite_colimits CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits

/-- If a category has all coproducts then in particular it has finite coproducts.
-/
theorem hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun J => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align category_theory.limits.has_finite_coproducts_of_has_coproducts CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts

end CategoryTheory.Limits

