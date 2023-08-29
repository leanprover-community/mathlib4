/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Opposites

#align_import category_theory.limits.constructions.filtered from "leanprover-community/mathlib"@"e4ee4e30418efcb8cf304ba76ad653aeec04ba6e"

/-!
# Constructing colimits from finite colimits and filtered colimits

We construct colimits of size `w` from finite colimits and filtered colimits of size `w`. Since
`w`-sized colimits are constructed from coequalizers and `w`-sized coproducts, it suffices to
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

/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
    `Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
def liftToFinset [HasFiniteCoproducts C] (F : Discrete α ⥤ C) : Finset (Discrete α) ⥤ C where
  obj s := ∐ fun x : s => F.obj x
  map {_ Y} h := Sigma.desc fun y =>
    Sigma.ι (fun (x : { x // x ∈ Y }) => F.obj x) ⟨y, h.down.down y.2⟩
#align category_theory.limits.coproducts_from_finite_filtered.lift_to_finset CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinset

/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
    taking the colimit of the diagram formed by the coproducts of finite sets over the indexing
    type. -/
@[simps!]
def liftToFinsetColimitCocone [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, w} C]
    (F : Discrete α ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := colimit (liftToFinset F)
      ι :=
        Discrete.natTrans fun j =>
          @Sigma.ι _ _ _ (fun x : ({j} : Finset (Discrete α)) => F.obj x) _ ⟨j, by simp⟩ ≫
                                                                                   -- 🎉 no goals
            colimit.ι (liftToFinset F) {j} }
  isColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinset F)
          { pt := s.pt
            ι := { app := fun t => Sigma.desc fun x => s.ι.app x } }
      uniq := fun s m h => by
        apply colimit.hom_ext
        -- ⊢ ∀ (j : Finset (Discrete α)), colimit.ι (liftToFinset F) j ≫ m = colimit.ι (l …
        rintro t
        -- ⊢ colimit.ι (liftToFinset F) t ≫ m = colimit.ι (liftToFinset F) t ≫ (fun s =>  …
        dsimp [liftToFinset]
        -- ⊢ colimit.ι (Functor.mk { obj := fun s => ∐ fun x => F.obj ↑x, map := fun {x Y …
        apply colimit.hom_ext
        -- ⊢ ∀ (j : Discrete { x // x ∈ t }), colimit.ι (Discrete.functor fun x => F.obj  …
        rintro ⟨⟨j, hj⟩⟩
        -- ⊢ colimit.ι (Discrete.functor fun x => F.obj ↑x) { as := { val := j, property  …
        convert h j using 1
        -- ⊢ colimit.ι (Discrete.functor fun x => F.obj ↑x) { as := { val := j, property  …
        · simp [← colimit.w (liftToFinset F) ⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩]
          -- ⊢ colimit.ι (Discrete.functor fun x => F.obj ↑x) { as := { val := j, property  …
          rfl
          -- 🎉 no goals
        · aesop_cat }
          -- 🎉 no goals
#align category_theory.limits.coproducts_from_finite_filtered.lift_to_finset_colimit_cocone CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimitCocone

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

theorem hasCoproducts_of_finite_and_filtered [HasFiniteCoproducts C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasCoproducts.{w} C := fun α => by
  classical exact ⟨fun F => HasColimit.mk (liftToFinsetColimitCocone F)⟩
  -- 🎉 no goals
#align category_theory.limits.has_coproducts_of_finite_and_filtered CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered

theorem has_colimits_of_finite_and_filtered [HasFiniteColimits C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C :=
  have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_hasCoequalizers_and_coproducts
#align category_theory.limits.has_colimits_of_finite_and_filtered CategoryTheory.Limits.has_colimits_of_finite_and_filtered

theorem hasProducts_of_finite_and_cofiltered [HasFiniteProducts C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasProducts.{w} C :=
  have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  hasProducts_of_opposite
#align category_theory.limits.has_products_of_finite_and_cofiltered CategoryTheory.Limits.hasProducts_of_finite_and_cofiltered

theorem has_limits_of_finite_and_cofiltered [HasFiniteLimits C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} C :=
  have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_hasEqualizers_and_products
#align category_theory.limits.has_limits_of_finite_and_cofiltered CategoryTheory.Limits.has_limits_of_finite_and_cofiltered

end CategoryTheory.Limits
