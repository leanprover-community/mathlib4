/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.abelian.generator
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Subobject
import Mathbin.CategoryTheory.Limits.EssentiallySmall
import Mathbin.CategoryTheory.Preadditive.Injective
import Mathbin.CategoryTheory.Preadditive.Generator
import Mathbin.CategoryTheory.Abelian.Opposite

/-!
# A complete abelian category with enough injectives and a separator has an injective coseparator

## Future work
* Once we know that Grothendieck categories have enough injectives, we can use this to conclude
  that Grothendieck categories have an injective coseparator.

## References
* [Peter J Freyd, *Abelian Categories* (Theorem 3.37)][freyd1964abelian]

-/


open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem has_injective_coseparator [HasLimits C] [EnoughInjectives C] (G : C) (hG : IsSeparator G) :
    ∃ G : C, Injective G ∧ IsCoseparator G :=
  by
  haveI : well_powered C := well_powered_of_is_detector G hG.is_detector
  haveI : has_products_of_shape (subobject (op G)) C := has_products_of_shape_of_small _ _
  let T : C := injective.under (pi_obj fun P : subobject (op G) => unop P)
  refine' ⟨T, inferInstance, (preadditive.is_coseparator_iff _).2 fun X Y f hf => _⟩
  refine' (preadditive.is_separator_iff _).1 hG _ fun h => _
  suffices hh : factor_thru_image (h ≫ f) = 0
  · rw [← limits.image.fac (h ≫ f), hh, zero_comp]
  let R := subobject.mk (factor_thru_image (h ≫ f)).op
  let q₁ : image (h ≫ f) ⟶ unop R :=
    (subobject.underlying_iso (factor_thru_image (h ≫ f)).op).unop.Hom
  let q₂ : unop (R : Cᵒᵖ) ⟶ pi_obj fun P : subobject (op G) => unop P :=
    section_ (pi.π (fun P : subobject (op G) => unop P) R)
  let q : image (h ≫ f) ⟶ T := q₁ ≫ q₂ ≫ injective.ι _
  exact
    zero_of_comp_mono q
      (by
        rw [← injective.comp_factor_thru q (limits.image.ι (h ≫ f)), limits.image.fac_assoc,
          category.assoc, hf, comp_zero])
#align category_theory.abelian.has_injective_coseparator CategoryTheory.Abelian.has_injective_coseparator

theorem has_projective_separator [HasColimits C] [EnoughProjectives C] (G : C)
    (hG : IsCoseparator G) : ∃ G : C, Projective G ∧ IsSeparator G :=
  by
  obtain ⟨T, hT₁, hT₂⟩ := has_injective_coseparator (op G) ((is_separator_op_iff _).2 hG)
  exact ⟨unop T, inferInstance, (is_separator_unop_iff _).2 hT₂⟩
#align category_theory.abelian.has_projective_separator CategoryTheory.Abelian.has_projective_separator

end CategoryTheory.Abelian

