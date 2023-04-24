/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.adjunction.adjoint_functor_theorems
! leanprover-community/mathlib commit 361aa777b4d262212c31d7c4a245ccb23645c156
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Generator
import Mathbin.CategoryTheory.Limits.ConeCategory
import Mathbin.CategoryTheory.Limits.Constructions.WeaklyInitial
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Subobject.Comma

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint: `is_right_adjoint_of_preserves_limits_of_solution_set_condition`.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition, see `solution_set_condition_of_is_right_adjoint`
(the file `category_theory/adjunction/limits` already shows it preserves limits).

We define the *solution set condition* for the functor `G : D ⥤ C` to mean, for every object
`A : C`, there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X`
factors through one of the `f_i`.

This file also proves the special adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` is complete, well-powered and has a small coseparating
  set, then `G` has a left adjoint: `is_right_adjoint_of_preserves_limits_of_is_coseparating`

Finally, we prove the following corollary of the special adjoint functor theorem:
* If `C` is complete, well-powered and has a small coseparating set, then it is cocomplete:
  `has_colimits_of_has_limits_of_is_coseparating`

-/


universe v u u'

namespace CategoryTheory

open Limits

variable {J : Type v}

variable {C : Type u} [Category.{v} C]

/-- The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
def SolutionSetCondition {D : Type u} [Category.{v} D] (G : D ⥤ C) : Prop :=
  ∀ A : C,
    ∃ (ι : Type v)(B : ι → D)(f : ∀ i : ι, A ⟶ G.obj (B i)),
      ∀ (X) (h : A ⟶ G.obj X), ∃ (i : ι)(g : B i ⟶ X), f i ≫ G.map g = h
#align category_theory.solution_set_condition CategoryTheory.SolutionSetCondition

section GeneralAdjointFunctorTheorem

variable {D : Type u} [Category.{v} D]

variable (G : D ⥤ C)

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition.  -/
theorem solutionSetCondition_of_isRightAdjoint [IsRightAdjoint G] : SolutionSetCondition G :=
  by
  intro A
  refine'
    ⟨PUnit, fun _ => (left_adjoint G).obj A, fun _ => (adjunction.of_right_adjoint G).Unit.app A, _⟩
  intro B h
  refine' ⟨PUnit.unit, ((adjunction.of_right_adjoint G).homEquiv _ _).symm h, _⟩
  rw [← adjunction.hom_equiv_unit, Equiv.apply_symm_apply]
#align category_theory.solution_set_condition_of_is_right_adjoint CategoryTheory.solutionSetCondition_of_isRightAdjoint

/-- The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
if `G` satisfies the solution set condition then `G` is a right adjoint.
-/
noncomputable def isRightAdjointOfPreservesLimitsOfSolutionSetCondition [HasLimits D]
    [PreservesLimits G] (hG : SolutionSetCondition G) : IsRightAdjoint G :=
  by
  apply is_right_adjoint_of_structured_arrow_initials _
  intro A
  specialize hG A
  choose ι B f g using hG
  let B' : ι → structured_arrow A G := fun i => structured_arrow.mk (f i)
  have hB' : ∀ A' : structured_arrow A G, ∃ i, Nonempty (B' i ⟶ A') :=
    by
    intro A'
    obtain ⟨i, _, t⟩ := g _ A'.hom
    exact ⟨i, ⟨structured_arrow.hom_mk _ t⟩⟩
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_has_products hB'
  apply has_initial_of_weakly_initial_and_has_wide_equalizers hT
#align category_theory.is_right_adjoint_of_preserves_limits_of_solution_set_condition CategoryTheory.isRightAdjointOfPreservesLimitsOfSolutionSetCondition

end GeneralAdjointFunctorTheorem

section SpecialAdjointFunctorTheorem

variable {D : Type u'} [Category.{v} D]

/-- The special adjoint functor theorem: if `G : D ⥤ C` preserves limits and `D` is complete,
well-powered and has a small coseparating set, then `G` has a left adjoint.
-/
noncomputable def isRightAdjointOfPreservesLimitsOfIsCoseparating [HasLimits D] [WellPowered D]
    {𝒢 : Set D} [Small.{v} 𝒢] (h𝒢 : IsCoseparating 𝒢) (G : D ⥤ C) [PreservesLimits G] :
    IsRightAdjoint G :=
  have : ∀ A, HasInitial (StructuredArrow A G) := fun A =>
    hasInitial_of_isCoseparating (StructuredArrow.isCoseparating_proj_preimage A G h𝒢)
  is_right_adjoint_of_structured_arrow_initials _
#align category_theory.is_right_adjoint_of_preserves_limits_of_is_coseparating CategoryTheory.isRightAdjointOfPreservesLimitsOfIsCoseparating

/-- The special adjoint functor theorem: if `F : C ⥤ D` preserves colimits and `C` is cocomplete,
well-copowered and has a small separating set, then `F` has a right adjoint.
-/
noncomputable def isLeftAdjointOfPreservesColimitsOfIsSeparatig [HasColimits C] [WellPowered Cᵒᵖ]
    {𝒢 : Set C} [Small.{v} 𝒢] (h𝒢 : IsSeparating 𝒢) (F : C ⥤ D) [PreservesColimits F] :
    IsLeftAdjoint F :=
  have : ∀ A, HasTerminal (CostructuredArrow F A) := fun A =>
    hasTerminal_of_isSeparating (CostructuredArrow.isSeparating_proj_preimage F A h𝒢)
  is_left_adjoint_of_costructured_arrow_terminals _
#align category_theory.is_left_adjoint_of_preserves_colimits_of_is_separatig CategoryTheory.isLeftAdjointOfPreservesColimitsOfIsSeparatig

end SpecialAdjointFunctorTheorem

namespace Limits

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a small coseparating set, then it is cocomplete. -/
theorem hasColimits_of_hasLimits_of_isCoseparating [HasLimits C] [WellPowered C] {𝒢 : Set C}
    [Small.{v} 𝒢] (h𝒢 : IsCoseparating 𝒢) : HasColimits C :=
  {
    HasColimitsOfShape := fun J hJ =>
      has_colimits_of_shape_iff_is_right_adjoint_const.2
        ⟨is_right_adjoint_of_preserves_limits_of_is_coseparating h𝒢 _⟩ }
#align category_theory.limits.has_colimits_of_has_limits_of_is_coseparating CategoryTheory.Limits.hasColimits_of_hasLimits_of_isCoseparating

/-- A consequence of the special adjoint functor theorem: if `C` is cocomplete, well-copowered and
    has a small separating set, then it is complete. -/
theorem hasLimits_of_hasColimits_of_isSeparating [HasColimits C] [WellPowered Cᵒᵖ] {𝒢 : Set C}
    [Small.{v} 𝒢] (h𝒢 : IsSeparating 𝒢) : HasLimits C :=
  {
    HasLimitsOfShape := fun J hJ =>
      has_limits_of_shape_iff_is_left_adjoint_const.2
        ⟨is_left_adjoint_of_preserves_colimits_of_is_separatig h𝒢 _⟩ }
#align category_theory.limits.has_limits_of_has_colimits_of_is_separating CategoryTheory.Limits.hasLimits_of_hasColimits_of_isSeparating

end Limits

end CategoryTheory

