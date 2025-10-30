/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Equivalence

/-!

# AB axioms in sheaf categories

If `J` is a Grothendieck topology on a small category `C : Type v`,
and `A : Type u₁` (with `Category.{v} A`) is a Grothendieck abelian category,
then `Sheaf J A` is a Grothendieck abelian category.

-/

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits

namespace Sheaf

variable {C : Type u} {A : Type u₁} {K : Type u₂}
  [Category.{v} C] [Category.{v₁} A] [Category.{v₂} K]
  (J : GrothendieckTopology C)

section

/- The two instances in this section apply in very rare situations, as they assume
that the forgetful functor from sheaves to presheaves commutes with certain colimits.
This does apply for sheaves for the extensive topology --- condensed modules over a
ring are examples of such sheaves.  -/

variable [HasWeakSheafify J A]

instance [HasFiniteLimits A] [HasColimitsOfShape K A] [HasExactColimitsOfShape K A]
    [PreservesColimitsOfShape K (sheafToPresheaf J A)] : HasExactColimitsOfShape K (Sheaf J A) :=
  HasExactColimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

instance [HasFiniteColimits A] [HasLimitsOfShape K A] [HasExactLimitsOfShape K A]
    [PreservesFiniteColimits (sheafToPresheaf J A)] : HasExactLimitsOfShape K (Sheaf J A) :=
  HasExactLimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

end

instance hasFilteredColimitsOfSize
    [HasSheafify J A] [HasFilteredColimitsOfSize.{v₂, u₂} A] :
    HasFilteredColimitsOfSize.{v₂, u₂} (Sheaf J A) where
  HasColimitsOfShape K := by infer_instance

instance hasExactColimitsOfShape [HasFiniteLimits A] [HasSheafify J A]
    [HasColimitsOfShape K A] [HasExactColimitsOfShape K A] :
    HasExactColimitsOfShape K (Sheaf J A) :=
  (sheafificationAdjunction J A).hasExactColimitsOfShape K

instance ab5ofSize [HasFiniteLimits A] [HasSheafify J A]
    [HasFilteredColimitsOfSize.{v₂, u₂} A] [AB5OfSize.{v₂, u₂} A] :
    AB5OfSize.{v₂, u₂} (Sheaf J A) where
  ofShape K _ _ := by infer_instance

instance {C : Type v} [SmallCategory.{v} C] (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A] : IsGrothendieckAbelian.{v} (Sheaf J A) where

attribute [local instance] hasSheafifyEssentiallySmallSite in
lemma isGrothendieckAbelian_of_essentiallySmall
    {C : Type u₂} [Category.{v} C] [EssentiallySmall.{v} C]
    (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] :
      IsGrothendieckAbelian.{v} (Sheaf J A) :=
  IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).inverse.sheafInducedTopologyEquivOfIsCoverDense J A)

end Sheaf

end CategoryTheory
