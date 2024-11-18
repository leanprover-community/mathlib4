/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# The relationship between products and binary products
-/

namespace CategoryTheory.Limits

variable {C I : Type*} [Category C] {X Y : I → C} [HasProduct X] [HasProduct Y]
  (f : (i : I) → X i ⟶ Y i) (P : I → Prop) [∀ i, Decidable (P i)]

variable [HasProduct (fun (i : {x : I // P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // ¬ (P x)}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // P x}) ↦ Y i.val)]
  [HasProduct (fun (i : {x : I // ¬ (P x)}) ↦ Y i.val)]

variable (X) in
noncomputable def Pi.binaryFanOfProp : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ (P x)}) ↦ X i.val)) :=
  BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ ↦ 𝟙 _)
    (Pi.map' Subtype.val fun _ ↦ 𝟙 _)

variable (X) in
noncomputable def Pi.binaryFanOfPropIsLimit : IsLimit (Pi.binaryFanOfProp X P) :=
  BinaryFan.isLimitMk
    (fun s ↦ Pi.lift fun b ↦ if h : (P b) then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) ↦ X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ (P x)}) ↦ X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ ↦ Pi.hom_ext _ _ fun b ↦ by
      by_cases h : (P b)
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])

local instance : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ (P x)}) ↦ X i.val)) :=
  ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

lemma Pi.map_eq_prod_map : Pi.map f =
    ((Pi.binaryFanOfPropIsLimit X P).conePointUniqueUpToIso (prodIsProd _ _)).hom ≫
      prod.map (Pi.map (fun (i : {x : I // P x}) ↦ f i.val))
      (Pi.map (fun (i : {x : I // ¬ (P x)}) ↦ f i.val)) ≫
        ((Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso (prodIsProd _ _)).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  apply prod.hom_ext
  · simp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd, limit.cone_x,
      Functor.mapIso_hom, IsLimit.uniqueUpToIso_hom, Cones.forget_map, IsLimit.liftConeMorphism_hom,
      IsLimit.ofIsoLimit_lift, BinaryFan.mk_pt, limit.isLimit_lift, Cones.ext_hom_hom, Iso.refl_hom,
      Category.comp_id, prod.comp_lift, limit.lift_π, BinaryFan.π_app_left, BinaryFan.mk_fst,
      prod.lift_map]
    aesop_cat
  · simp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd, limit.cone_x,
      Functor.mapIso_hom, IsLimit.uniqueUpToIso_hom, Cones.forget_map, IsLimit.liftConeMorphism_hom,
      IsLimit.ofIsoLimit_lift, BinaryFan.mk_pt, limit.isLimit_lift, Cones.ext_hom_hom, Iso.refl_hom,
      Category.comp_id, prod.comp_lift, limit.lift_π, BinaryFan.π_app_right, BinaryFan.mk_snd,
      prod.lift_map]
    aesop_cat


end CategoryTheory.Limits
