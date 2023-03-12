/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.constructions.filtered
! leanprover-community/mathlib commit e4ee4e30418efcb8cf304ba76ad653aeec04ba6e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathbin.CategoryTheory.Limits.Opposites

/-!
# Constructing colimits from finite colimits and filtered colimits

We construct colimits of size `w` from finite colimits and filtered colimits of size `w`. Since
`w`-sized colimits are constructured from coequalizers and `w`-sized coproducts, it suffices to
construct `w`-sized coproducts from finite coproducts and `w`-sized filtered colimits.

The idea is simple: to construct coproducts of shape `α`, we take the colimit of the filtered
diagram of all coproducts of finite subsets of `α`.

We also deduce the dual statement by invoking the original statement in `Cᵒᵖ`.
-/


universe w v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C] {α : Type w}

namespace CategoryTheory.Limits

namespace CoproductsFromFiniteFiltered

attribute [local tidy] tactic.case_bash

/-- If `C` has finite coproducts, a functor `discrete α ⥤ C` lifts to a functor
    `finset (discrete α) ⥤ C` by taking coproducts. -/
@[simps]
def liftToFinset [HasFiniteCoproducts C] (F : Discrete α ⥤ C) : Finset (Discrete α) ⥤ C
    where
  obj s := ∐ fun x : s => F.obj x
  map s t h := Sigma.desc fun y => Sigma.ι (fun x : t => F.obj x) ⟨y, h.down.down y.2⟩
#align category_theory.limits.coproducts_from_finite_filtered.lift_to_finset CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinset

/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
    taking the colimit of the diagram formed by the coproducts of finite sets over the indexing
    type. -/
@[simps]
def liftToFinsetColimitCocone [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, w} C]
    [DecidableEq α] (F : Discrete α ⥤ C) : ColimitCocone F
    where
  Cocone :=
    { pt := colimit (liftToFinset F)
      ι :=
        Discrete.natTrans fun j =>
          @Sigma.ι _ _ _ (fun x : ({j} : Finset (Discrete α)) => F.obj x) _ ⟨j, by simp⟩ ≫
            colimit.ι (liftToFinset F) {j} }
  IsColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinset F)
          { pt := s.pt
            ι := { app := fun t => Sigma.desc fun x => s.ι.app x } }
      uniq := fun s m h => by
        ext (t⟨⟨j, hj⟩⟩)
        convert h j using 1
        · simp [← colimit.w (lift_to_finset F) ⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩]
          rfl
        · tidy }
#align category_theory.limits.coproducts_from_finite_filtered.lift_to_finset_colimit_cocone CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimitCocone

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

theorem hasCoproducts_of_finite_and_filtered [HasFiniteCoproducts C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasCoproducts.{w} C := fun α => by
  classical exact ⟨fun F => has_colimit.mk (lift_to_finset_colimit_cocone F)⟩
#align category_theory.limits.has_coproducts_of_finite_and_filtered CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered

theorem has_colimits_of_finite_and_filtered [HasFiniteColimits C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C :=
  have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_has_coequalizers_and_coproducts
#align category_theory.limits.has_colimits_of_finite_and_filtered CategoryTheory.Limits.has_colimits_of_finite_and_filtered

theorem hasProducts_of_finite_and_cofiltered [HasFiniteProducts C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasProducts.{w} C :=
  have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  has_products_of_opposite
#align category_theory.limits.has_products_of_finite_and_cofiltered CategoryTheory.Limits.hasProducts_of_finite_and_cofiltered

theorem has_limits_of_finite_and_cofiltered [HasFiniteLimits C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} C :=
  have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_has_equalizers_and_products
#align category_theory.limits.has_limits_of_finite_and_cofiltered CategoryTheory.Limits.has_limits_of_finite_and_cofiltered

end CategoryTheory.Limits

