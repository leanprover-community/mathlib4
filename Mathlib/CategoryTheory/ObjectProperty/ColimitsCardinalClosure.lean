/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
import Mathlib.CategoryTheory.SmallRepresentatives
import Mathlib.CategoryTheory.Comma.CardinalArrow

/-!
# Closure of a property of objects under colimits of bounded cardinality

In this file, given `P : ObjectProperty C` and `κ : Cardinal.{w}`,
we introduce the closure `P.colimitsCardinalClosure κ`
of `P` under colimits of shapes given by categories `J` such
that `HasCardinalLT (Arrow J) κ` holds.

If `C` is locally `w`-small and `P` is essentially `w`-small,
we show that this closure `P.colimitsCardinalClosure κ` is
also essentially `w`-small.

-/

universe w v' v u' u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (κ : Cardinal.{w})

/-- Given `P : ObjectProperty C` and `κ : Cardinal.{w}`, this is the closure
of `P` under colimits of shape given by categories `J` such that
`HasCardinalLT (Arrow J) κ` holds. -/
def colimitsCardinalClosure : ObjectProperty C :=
  P.colimitsClosure (SmallCategoryCardinalLT.categoryFamily κ)

lemma le_colimitsCardinalClosure : P ≤ P.colimitsCardinalClosure κ :=
  P.le_colimitsClosure _

instance : (P.colimitsCardinalClosure κ).IsClosedUnderIsomorphisms := by
  dsimp [colimitsCardinalClosure]
  infer_instance

instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (P.colimitsCardinalClosure κ) := by
  dsimp [colimitsCardinalClosure]
  infer_instance

instance (S : SmallCategoryCardinalLT κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape
      (SmallCategoryCardinalLT.categoryFamily κ S) := by
  dsimp [colimitsCardinalClosure]
  infer_instance

lemma isClosedUnderColimitsOfShape_colimitsCardinalClosure
    (J : Type u') [Category.{v'} J] (hJ : HasCardinalLT (Arrow J) κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape J := by
  obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
  rw [isClosedUnderColimitsOfShape_iff_of_equivalence _ e.symm]
  infer_instance

lemma colimitsCardinalClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      Q.IsClosedUnderColimitsOfShape J) (h : P ≤ Q) :
    P.colimitsCardinalClosure κ ≤ Q := by
  have (i : SmallCategoryCardinalLT κ) := hQ _ i.hasCardinalLT
  exact colimitsClosure_le h

section

open Limits

instance isStableUnderRetracts_colimitsCardinalClosure [Fact κ.IsRegular] :
    (P.colimitsCardinalClosure κ).IsStableUnderRetracts := by
  have := P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ
    WalkingParallelPair (HasCardinalLT.of_le (by simp; infer_instance)
    (Cardinal.IsRegular.aleph0_le Fact.out))
  infer_instance

end

end CategoryTheory.ObjectProperty
