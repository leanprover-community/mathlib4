/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Types

/-!
# Limits in concrete categories

In this file, we combine the description of limits in `Types` and the API about
the preservation of products and pullbacks in order to describe these limits in a
concrete category `C`.

If `F : J → C` is a family of objects in `C`, we define a bijection
`Limits.Concrete.productEquiv F : (forget C).obj (∏ F) ≃ ∀ j, F j`.

Similarly, if `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` are two morphisms, the elements
in `pullback f₁ f₂` are identified by `Limits.Concrete.pullbackEquiv``
to compatible tuples of elements in `X₁ × X₂`.

-/

universe w v u

namespace CategoryTheory

namespace Limits

namespace Concrete

attribute [local instance] ConcreteCategory.funLike ConcreteCategory.hasCoeToSort

variable {C : Type u} [Category.{v} C]

section Products

variable [ConcreteCategory.{max w v} C] {J : Type w} (F : J → C)
  [HasProduct F] [PreservesLimit (Discrete.functor F) (forget C)]

/-- The equivalence `(forget C).obj (∏ F) ≃ ∀ j, F j` if `F : J → C` is a family of objects
in a concrete category `C`. -/
noncomputable def productEquiv : (forget C).obj (∏ F) ≃ ∀ j, F j :=
  ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} F)).toEquiv

@[simp]
lemma productEquiv_apply_apply (x : (forget C).obj (∏ F)) (j : J) :
    productEquiv F x j = Pi.π F j x :=
  congr_fun (piComparison_comp_π (forget C) F j) x

@[simp]
lemma productEquiv_symm_apply_π (x : ∀ j, F j) (j : J) :
    Pi.π F j ((productEquiv F).symm x) = x j := by
  rw [← productEquiv_apply_apply, Equiv.apply_symm_apply]

end Products

section Pullbacks

variable [ConcreteCategory.{v} C] {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] [PreservesLimit (cospan f₁ f₂) (forget C)]

/-- In a concrete category `C`, given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`,
the elements in `pullback f₁ f₁` can be identified to compatible tuples of
elements in `X₁` and `X₂`. -/
noncomputable def pullbackEquiv :
    (forget C).obj (pullback f₁ f₂) ≃ { p : X₁ × X₂ // f₁ p.1 = f₂ p.2 } :=
  (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback ((forget C).map f₁) ((forget C).map f₂)).toEquiv

/-- Constructor for elements in a pullback in a concrete category. -/
noncomputable def pullbackMk (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂) :
    (forget C).obj (pullback f₁ f₂) :=
  (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩

lemma pullbackMk_surjective (x : (forget C).obj (pullback f₁ f₂)) :
    ∃ (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂), x = pullbackMk f₁ f₂ x₁ x₂ h := by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]
lemma pullbackMk_fst (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂) :
    @pullback.fst _ _ _ _ _ f₁ f₂ _ (pullbackMk f₁ f₂ x₁ x₂ h) = x₁ :=
  (congr_fun (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_fun (Types.pullbackIsoPullback_inv_fst ((forget C).map f₁) ((forget C).map f₂)) _)

@[simp]
lemma pullbackMk_snd (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂) :
    @pullback.snd _ _ _ _ _ f₁ f₂ _ (pullbackMk f₁ f₂ x₁ x₂ h) = x₂ :=
  (congr_fun (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_fun (Types.pullbackIsoPullback_inv_snd ((forget C).map f₁) ((forget C).map f₂)) _)

end Pullbacks

end Concrete

end Limits

end CategoryTheory
