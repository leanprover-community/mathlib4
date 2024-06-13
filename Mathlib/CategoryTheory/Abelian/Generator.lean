/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.Generator
import Mathlib.CategoryTheory.Abelian.Opposite

#align_import category_theory.abelian.generator from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

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
    ∃ G : C, Injective G ∧ IsCoseparator G := by
  haveI : WellPowered C := wellPowered_of_isDetector G hG.isDetector
  haveI : HasProductsOfShape (Subobject (op G)) C := hasProductsOfShape_of_small _ _
  let T : C := Injective.under (piObj fun P : Subobject (op G) => unop P)
  refine ⟨T, inferInstance, (Preadditive.isCoseparator_iff _).2 fun X Y f hf => ?_⟩
  refine (Preadditive.isSeparator_iff _).1 hG _ fun h => ?_
  suffices hh : factorThruImage (h ≫ f) = 0 by
    rw [← Limits.image.fac (h ≫ f), hh, zero_comp]
  let R := Subobject.mk (factorThruImage (h ≫ f)).op
  let q₁ : image (h ≫ f) ⟶ unop R :=
    (Subobject.underlyingIso (factorThruImage (h ≫ f)).op).unop.hom
  let q₂ : unop (R : Cᵒᵖ) ⟶ piObj fun P : Subobject (op G) => unop P :=
    section_ (Pi.π (fun P : Subobject (op G) => (unop P : C)) R)
  let q : image (h ≫ f) ⟶ T := q₁ ≫ q₂ ≫ Injective.ι _
  exact zero_of_comp_mono q
    (by rw [← Injective.comp_factorThru q (Limits.image.ι (h ≫ f)), Limits.image.fac_assoc,
      Category.assoc, hf, comp_zero])
#align category_theory.abelian.has_injective_coseparator CategoryTheory.Abelian.has_injective_coseparator

theorem has_projective_separator [HasColimits C] [EnoughProjectives C] (G : C)
    (hG : IsCoseparator G) : ∃ G : C, Projective G ∧ IsSeparator G := by
  obtain ⟨T, hT₁, hT₂⟩ := has_injective_coseparator (op G) ((isSeparator_op_iff _).2 hG)
  exact ⟨unop T, inferInstance, (isSeparator_unop_iff _).2 hT₂⟩
#align category_theory.abelian.has_projective_separator CategoryTheory.Abelian.has_projective_separator

end CategoryTheory.Abelian
