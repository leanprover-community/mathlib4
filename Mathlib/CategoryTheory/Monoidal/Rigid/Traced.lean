/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Traced
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Right rigid to traced monoidal categories

## References

* [A. Joyal and R. Street and D. R. Verity, *Traced monoidal categories*][JoyalStreet1996]

-/

@[expose] public section



universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

namespace RightRigidCategory

open Category MonoidalCategory BraidedCategory ExactPairing

variable
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory.{v} C]
  [SymmetricCategory.{v} C]
  [RRC : RightRigidCategory C]

/-- `TracedCategory.trace` -/
@[inline]
def trace {A B : C} (W : C) (f : A ⊗ W ⟶ B ⊗ W) : A ⟶ B :=
  (ρ_ A).inv ≫ A ◁ η_ W Wᘁ ≫ (α_ A W Wᘁ).inv ≫ f ▷ Wᘁ ≫
    (α_ B W Wᘁ).hom ≫ B ◁ (β_ W Wᘁ).hom ≫ B ◁ ε_ W Wᘁ ≫ (ρ_ B).hom

@[simp]
lemma trace_naturality_left
    {A A' B : C}
    (W : C)
    (f : A' ⟶ A)
    (g : A ⊗ W ⟶ B ⊗ W) :
    trace W (f ▷ W ≫ g) = f ≫ trace W g := by
  simp only [trace, comp_whiskerRight, Category.assoc]
  slice_lhs 3 4 => rw [← associator_inv_naturality_left]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 1 2 => rw [← rightUnitor_inv_naturality]
  simp [Category.assoc]

@[simp]
lemma trace_naturality_right
    {A B B' : C}
    (W : C)
    (f : A ⊗ W ⟶ B ⊗ W)
    (g : B ⟶ B') :
    trace W (f ≫ g ▷ W) = trace W f ≫ g := by
  simp only [trace, comp_whiskerRight, Category.assoc]
  slice_lhs 5 6 => rw [associator_naturality_left]
  slice_lhs 6 7 => rw [← whisker_exchange]
  slice_lhs 7 8 => rw [← whisker_exchange]
  slice_lhs 8 9 => rw [rightUnitor_naturality]

@[simp]
lemma trace_dinaturality
    {A B W : C}
    (f : A ⊗ W ⟶ B ⊗ W)
    (h : W ⟶ W) :
    trace W (f ≫ B ◁ h) = trace W (A ◁ h ≫ f) := by
  simp only [trace, comp_whiskerRight, Category.assoc]
  slice_lhs 5 6 => rw [associator_naturality_middle]
  slice_lhs 6 7 => rw [← whiskerLeft_comp, braiding_naturality_left, whiskerLeft_comp]
  slice_lhs 7 8 => rw [← whiskerLeft_comp, ← rightAdjointMate_comp_evaluation, whiskerLeft_comp]
  slice_lhs 6 7 => rw [← whiskerLeft_comp, ← braiding_naturality_right, whiskerLeft_comp]
  slice_lhs 5 6 => rw [← associator_naturality_right]
  slice_lhs 4 5 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [← associator_inv_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, coevaluation_comp_rightAdjointMate, whiskerLeft_comp]
  slice_lhs 3 4 => rw [associator_inv_naturality_middle]
  simp [Category.assoc]

@[simp]
lemma trace_superposing
    {A B : C}
    (C' W : C)
    (f : A ⊗ W ⟶ B ⊗ W) :
    C' ◁ trace W f = trace W ((α_ C' A W).hom ≫ C' ◁ f ≫ (α_ C' B W).inv) := by
  simp only [trace, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

omit [RightRigidCategory C] in
@[reassoc]
lemma cap_unit (B : C) [HasRightDual (𝟙_ C)] :
    (α_ B (𝟙_ C) (𝟙_ C)ᘁ).hom ≫ B ◁ (β_ (𝟙_ C) (𝟙_ C)ᘁ).hom =
    (ρ_ B).hom ▷ (𝟙_ C)ᘁ ≫ B ◁ (ρ_ (𝟙_ C)ᘁ).inv := by
  rw [braiding_tensorUnit_left, whiskerLeft_comp, ← Category.assoc, triangle]

omit [RightRigidCategory C] [SymmetricCategory C] in
lemma unit_coevaluation [HasRightDual (𝟙_ C)] :
    η_ (𝟙_ C) (𝟙_ C)ᘁ ▷ (𝟙_ C) ≫ (α_ (𝟙_ C) (𝟙_ C)ᘁ (𝟙_ C)).hom ≫ (𝟙_ C) ◁ ε_ (𝟙_ C) (𝟙_ C)ᘁ =
    𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
  rw [evaluation_coevaluation]
  monoidal

omit [RightRigidCategory C] in
@[reassoc]
lemma unit_loop [RD : HasRightDual (𝟙_ C)] :
    η_ (𝟙_ C) (𝟙_ C)ᘁ ≫ (β_ (𝟙_ C) (𝟙_ C)ᘁ).hom ≫ ε_ (𝟙_ C) (𝟙_ C)ᘁ = 𝟙 (𝟙_ C) := by
  rw [braiding_tensorUnit_left]
  calc η_ (𝟙_ C) (𝟙_ C)ᘁ ≫ ((λ_ (𝟙_ C)ᘁ).hom ≫ (ρ_ (𝟙_ C)ᘁ).inv) ≫ ε_ (𝟙_ C) (𝟙_ C)ᘁ
      = (ρ_ (𝟙_ C)).inv ≫ (η_ (𝟙_ C) (𝟙_ C)ᘁ ▷ (𝟙_ C) ≫ (α_ (𝟙_ C) (𝟙_ C)ᘁ (𝟙_ C)).hom ≫
          (𝟙_ C) ◁ ε_ (𝟙_ C) (𝟙_ C)ᘁ) ≫ (ρ_ (𝟙_ C)).hom := by monoidal
    _ = (ρ_ (𝟙_ C)).inv ≫ 𝟙 _ ≫ (ρ_ (𝟙_ C)).hom := by rw [unit_coevaluation]
    _ = 𝟙 _ := by simp

omit [RightRigidCategory C] [SymmetricCategory C] in
@[reassoc]
lemma cup_unit (A : C) [HasRightDual (𝟙_ C)] :
    A ◁ η_ (𝟙_ C) (𝟙_ C)ᘁ ≫ (α_ A (𝟙_ C) (𝟙_ C)ᘁ).inv =
    A ◁ (η_ (𝟙_ C) (𝟙_ C)ᘁ ≫ (λ_ (𝟙_ C)ᘁ).hom) ≫ (ρ_ A).inv ▷ (𝟙_ C)ᘁ := by
  rw [whiskerLeft_comp, Category.assoc]
  congr 1
  monoidal

lemma trace_vanishing_one
    {A B : C}
    (f : A ⊗ 𝟙_ C ⟶ B ⊗ 𝟙_ C) :
    trace (𝟙_ C) f = (ρ_ A).inv ≫ f ≫ (ρ_ B).hom := by
  unfold trace
  rw [cup_unit_assoc, cap_unit_assoc, whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  congr 1
  rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc,
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc, ← braiding_tensorUnit_left]
  rw [unit_loop (RD:=RRC.rightDual (𝟙_ C)), whiskerLeft_id]
  simp

@[reassoc]
lemma trace_congr_rightDual
    {A B W : C} {W' : C} (φ : Wᘁ ≅ W') (f : A ⊗ W ⟶ B ⊗ W) :
    trace W f =
    (ρ_ A).inv ≫ A ◁ (η_ W Wᘁ ≫ W ◁ φ.hom) ≫ (α_ A W W').inv ≫ f ▷ W' ≫
    (α_ B W W').hom ≫ B ◁ ((β_ W W').hom ≫ φ.inv ▷ W ≫ ε_ W Wᘁ) ≫ (ρ_ B).hom := by
  unfold trace
  have hf : f ▷ Wᘁ = (A ⊗ W) ◁ φ.hom ≫ f ▷ W' ≫ (B ⊗ W) ◁ φ.inv := by
    rw [← whisker_exchange, ← Category.assoc, ← whiskerLeft_comp, φ.hom_inv_id,
        whiskerLeft_id, Category.id_comp]
  rw [hf]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_right_assoc]
  rw [associator_naturality_right_assoc]
  simp only [← whiskerLeft_comp_assoc]
  simp

end RightRigidCategory

end CategoryTheory
