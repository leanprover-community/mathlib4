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
  haveI : HasLimitsOfShape (Discrete (Fin n)) C := HasFiniteProducts.out n
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
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
  haveI : HasColimitsOfShape (Discrete (Fin n)) C := HasFiniteCoproducts.out n
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
#align category_theory.limits.has_colimits_of_shape_discrete CategoryTheory.Limits.hasColimitsOfShape_discrete

/-- If `C` has finite colimits then it has finite coproducts. -/
instance (priority := 10) hasFiniteCoproducts_of_hasFiniteColimits [HasFiniteColimits C] :
    HasFiniteCoproducts C :=
  ⟨fun J => by infer_instance⟩
#align category_theory.limits.has_finite_coproducts_of_has_finite_colimits CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits

/-- If a category has all coproducts then in particular it has finite coproducts.
-/
theorem hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align category_theory.limits.has_finite_coproducts_of_has_coproducts CategoryTheory.Limits.hasFiniteCoproducts_of_hasCoproducts

/-- Describes the property of having pullbacks of morphsims into a finite coproduct, where one
of the morphisms is an inclusion map into the coproduct (up to isomorphism). -/
class HasPullbacksOfInclusions : Prop where
    /-- For any morphism `f : X ⟶ Z`, where `Z` is the coproduct of `i : (a : α) → Y a ⟶ Z` with
    `α` finite, the pullback of `f` and `i a` exists for every `a : α`. -/
    has_pullback : ∀ {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbacksOfInclusions C] {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbacksOfInclusions.has_pullback f i a

/-- If `C` has pullbacks then it has the pullbacks relevant to `HasPullbacksOfInclusions` -/
instance (priority := 10) [HasPullbacks C] :
  HasPullbacksOfInclusions C := ⟨fun _ _ _ => inferInstance⟩

/-- A category is *extensive* if it has all finite coproducts and those coproducts are preserved
by pullbacks (we only require the relevant pullbacks to exist, via `HasPullbacksOfInclusions`). -/
class Extensive extends HasFiniteCoproducts C, HasPullbacksOfInclusions C : Prop where
  /-- Pulling back an isomorphism from a coproduct yields an isomorphism. -/
  sigma_desc_iso : ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
    {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

end CategoryTheory.Limits
