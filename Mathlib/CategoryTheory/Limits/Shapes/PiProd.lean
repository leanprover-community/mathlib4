/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# A product as a binary product

We write a product indexed by `I` as a binary product of the products indexed by a subset of `I`
and its complement.

-/

namespace CategoryTheory.Limits

variable {C I : Type*} [Category C] {X Y : I → C}
  (f : (i : I) → X i ⟶ Y i) (P : I → Prop)
  [HasProduct X] [HasProduct Y]
  [HasProduct (fun (i : {x : I // P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // P x}) ↦ Y i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) ↦ Y i.val)]

variable (X) in
/--
The projection maps of a product to the products indexed by a subset and its complement, as a
binary fan.
-/
noncomputable def Pi.binaryFanOfProp : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) ↦ X i.val)) :=
  BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ ↦ 𝟙 _)
    (Pi.map' Subtype.val fun _ ↦ 𝟙 _)

variable (X) in
/--
A product indexed by `I` is a binary product of the products indexed by a subset of `I` and its
complement.
-/
noncomputable def Pi.binaryFanOfPropIsLimit [∀ i, Decidable (P i)] :
    IsLimit (Pi.binaryFanOfProp X P) :=
  BinaryFan.isLimitMk
    (fun s ↦ Pi.lift fun b ↦ if h : P b then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) ↦ X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ P x}) ↦ X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ ↦ Pi.hom_ext _ _ fun b ↦ by
      by_cases h : P b
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])

lemma hasBinaryProduct_of_products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) ↦ X i.val)) := by
  classical exact ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

attribute [local instance] hasBinaryProduct_of_products

lemma Pi.map_eq_prod_map [∀ i, Decidable (P i)] : Pi.map f =
    ((Pi.binaryFanOfPropIsLimit X P).conePointUniqueUpToIso (prodIsProd _ _)).hom ≫
      prod.map (Pi.map (fun (i : {x : I // P x}) ↦ f i.val))
      (Pi.map (fun (i : {x : I // ¬ P x}) ↦ f i.val)) ≫
        ((Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso (prodIsProd _ _)).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  dsimp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd]
  apply prod.hom_ext
  all_goals cat_disch

end CategoryTheory.Limits
