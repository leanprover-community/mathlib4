/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
public import Mathlib.CategoryTheory.Subobject.Comma

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint: `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition, see `solutionSetCondition_of_isRightAdjoint`
(the file `CategoryTheory/Adjunction/Limits` already shows it preserves limits).

We define the *solution set condition* for the functor `G : D ⥤ C` to mean, for every object
`A : C`, there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X`
factors through one of the `f_i`.

This file also proves the special adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` is complete, well-powered and has a small coseparating
  set, then `G` has a left adjoint: `isRightAdjoint_of_preservesLimits_of_isCoseparating`

Finally, we prove the following corollaries of the special adjoint functor theorem:
* If `C` is complete, well-powered and has a small coseparating set, then it is cocomplete:
  `hasColimits_of_hasLimits_of_isCoseparating`, `hasColimits_of_hasLimits_of_hasCoseparator`
* If `C` is cocomplete, co-well-powered and has a small separating set, then it is complete:
  `hasLimits_of_hasColimits_of_isSeparating`, `hasLimits_of_hasColimits_of_hasSeparator`

-/

@[expose] public section


universe w v v₁ u u₁ u'

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
def SolutionSetCondition {D : Type u₁} [Category.{v₁} D] (G : D ⥤ C) : Prop :=
  ∀ A : C,
    ∃ (ι : Type w) (B : ι → D) (f : ∀ i : ι, A ⟶ G.obj (B i)),
      ∀ (X) (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

section GeneralAdjointFunctorTheorem

variable {D : Type u₁} [Category.{v₁} D]
variable (G : D ⥤ C)

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition. -/
theorem solutionSetCondition_of_isRightAdjoint [G.IsRightAdjoint] : SolutionSetCondition.{w} G := by
  intro A
  refine
    ⟨PUnit, fun _ => G.leftAdjoint.obj A, fun _ => (Adjunction.ofIsRightAdjoint G).unit.app A, ?_⟩
  intro B h
  refine ⟨PUnit.unit, ((Adjunction.ofIsRightAdjoint G).homEquiv _ _).symm h, ?_⟩
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
if `G` satisfies the solution set condition then `G` is a right adjoint.
-/
lemma isRightAdjoint_of_preservesLimits_of_solutionSetCondition [HasLimitsOfSize.{w, w} D]
    [PreservesLimitsOfSize.{w, w} G] (hG : SolutionSetCondition.{w} G)
    [LocallySmall.{w} D] : G.IsRightAdjoint := by
  apply +allowSynthFailures isRightAdjointOfStructuredArrowInitials
  intro A
  choose ι B f g using hG A
  let B' (i : ι) : StructuredArrow A G := StructuredArrow.mk (f i)
  have hB' : ∀ A' : StructuredArrow A G, ∃ i, Nonempty (B' i ⟶ A') := by
    intro A'
    obtain ⟨i, _, t⟩ := g _ A'.hom
    exact ⟨i, ⟨StructuredArrow.homMk _ t⟩⟩
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hB'
  exact hasInitial_of_weakly_initial_and_hasWideEqualizers hT

end GeneralAdjointFunctorTheorem

section SpecialAdjointFunctorTheorem

variable {D : Type u₁} [Category.{v₁} D]

/-- The special adjoint functor theorem: if `G : D ⥤ C` preserves limits and `D` is complete,
well-powered and has a small coseparating set, then `G` has a left adjoint.
-/
lemma isRightAdjoint_of_preservesLimits_of_isCoseparating [HasLimitsOfSize.{w, w} D]
    [LocallySmall.{w} C] [LocallySmall.{w} D] [WellPowered.{w} D]
    {P : ObjectProperty D} [ObjectProperty.Small.{w} P]
    (hP : P.IsCoseparating) (G : D ⥤ C) [PreservesLimitsOfSize.{w, w} G] :
    G.IsRightAdjoint := by
  have := hasFiniteLimits_of_hasLimitsOfSize D
  have := PreservesLimitsOfSize.preservesFiniteLimits G
  have (A : C) : HasInitial (StructuredArrow A G) :=
    hasInitial_of_isCoseparating (StructuredArrow.isCoseparating_inverseImage_proj A G hP)
  exact isRightAdjointOfStructuredArrowInitials _

/-- The special adjoint functor theorem: if `F : C ⥤ D` preserves colimits and `C` is cocomplete,
well-copowered and has a small separating set, then `F` has a right adjoint.
-/
lemma isLeftAdjoint_of_preservesColimits_of_isSeparating [HasColimitsOfSize.{w, w} C]
    [LocallySmall.{w} C] [LocallySmall.{w} D] [WellPowered.{w} Cᵒᵖ]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (h𝒢 : P.IsSeparating) (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F] :
    F.IsLeftAdjoint :=
  have := hasFiniteColimits_of_hasColimitsOfSize C
  have := PreservesColimitsOfSize.preservesFiniteColimits F
  have (A : D) : HasTerminal (CostructuredArrow F A) :=
    hasTerminal_of_isSeparating.{w} (CostructuredArrow.isSeparating_inverseImage_proj F A h𝒢)
  isLeftAdjoint_of_costructuredArrowTerminals _

end SpecialAdjointFunctorTheorem

namespace Limits

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a small coseparating set, then it is cocomplete. -/
theorem hasColimits_of_hasLimits_of_isCoseparating
    [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] [WellPowered.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hP : P.IsCoseparating) :
    HasColimitsOfSize.{w, w} C :=
  { has_colimits_of_shape := fun _ _ =>
      hasColimitsOfShape_iff_isRightAdjoint_const.2
        (isRightAdjoint_of_preservesLimits_of_isCoseparating hP _) }

/-- A consequence of the special adjoint functor theorem: if `C` is cocomplete, well-copowered and
    has a small separating set, then it is complete. -/
theorem hasLimits_of_hasColimits_of_isSeparating
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hP : P.IsSeparating) :
    HasLimitsOfSize.{w, w} C :=
  { has_limits_of_shape := fun _ _ =>
      hasLimitsOfShape_iff_isLeftAdjoint_const.2
        (isLeftAdjoint_of_preservesColimits_of_isSeparating hP _) }

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a separator, then it is complete. -/
theorem hasLimits_of_hasColimits_of_hasSeparator
    [HasColimitsOfSize.{w, w} C] [HasSeparator C] [LocallySmall.{w} C]
    [WellPowered.{w} Cᵒᵖ] : HasLimitsOfSize.{w, w} C :=
  hasLimits_of_hasColimits_of_isSeparating <| isSeparator_separator C

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a coseparator, then it is cocomplete. -/
theorem hasColimits_of_hasLimits_of_hasCoseparator
    [HasLimitsOfSize.{w, w} C] [HasCoseparator C] [LocallySmall.{w} C]
    [WellPowered.{w} C] : HasColimitsOfSize.{w, w} C :=
  hasColimits_of_hasLimits_of_isCoseparating <| isCoseparator_coseparator C

end Limits

end CategoryTheory
