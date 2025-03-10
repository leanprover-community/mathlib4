/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Additional results about the `liftToFinset` construction

If `f` is a family of objects of `C`, then there is a canonical cocone whose cocone point is the
coproduct of `f` and whose legs are given by the inclusions of the finite subcoproducts. If `C`
is preadditive, then we can describe the legs of this cocone as finite sums of projections followed
by inclusions.
-/

universe w v u


namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CoproductsFromFiniteFiltered

variable [HasFiniteCoproducts C]

theorem finiteSubcoproductsCocone_ι_app_eq_sum {α : Type w} [DecidableEq α] (f : α → C)
    [HasCoproduct f] (S : Finset (Discrete α)) :
    (finiteSubcoproductsCocone f).ι.app S = ∑ a ∈ S.attach, Sigma.π _ a ≫ Sigma.ι _ a.1.as := by
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj, finiteSubcoproductsCocone_ι_app]
  ext v
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Preadditive.comp_sum]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hb₁
    rw [Sigma.ι_π_of_ne_assoc _ (Ne.symm hb₁), zero_comp]
  · simp

end CoproductsFromFiniteFiltered

namespace ProductsFromFiniteCofiltered

variable [HasFiniteProducts C]

theorem finiteSubproductsCocone_π_app_eq_sum {α : Type w} [DecidableEq α] (f : α → C) [HasProduct f]
    (S : (Finset (Discrete α))ᵒᵖ) :
    (finiteSubproductsCone f).π.app S =
      ∑ a ∈ S.unop.attach, Pi.π f a.1.as ≫ Pi.ι (fun a => f a.1.as) a := by
  dsimp only [finiteSubproductsCone_pt, Functor.const_obj_obj, liftToFinsetObj_obj,
    Discrete.functor_obj_eq_as, finiteSubproductsCone_π_app]
  ext v
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hb₁
    rw [Pi.ι_π_of_ne _ hb₁, comp_zero]
  · simp

end ProductsFromFiniteCofiltered

end CategoryTheory.Limits
