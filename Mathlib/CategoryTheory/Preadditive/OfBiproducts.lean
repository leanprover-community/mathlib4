/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.GroupTheory.EckmannHilton
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
/-!
# Constructing a semiadditive structure from binary biproducts

We show that any category with zero morphisms and binary biproducts is enriched over the category
of commutative monoids.

-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.SemiadditiveOfBinaryBiproducts

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

section

variable (X Y : C)

/-- `f +ₗ g` is the composite `X ⟶ Y ⊞ Y ⟶ Y`, where the first map is `(f, g)` and the second map
is `(𝟙 𝟙)`. -/
@[simp]
def leftAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)

/-- `f +ᵣ g` is the composite `X ⟶ X ⊞ X ⟶ Y`, where the first map is `(𝟙, 𝟙)` and the second map
is `(f g)`. -/
@[simp]
def rightAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g

local infixr:65 " +ₗ " => leftAdd X Y

local infixr:65 " +ᵣ " => rightAdd X Y

theorem isUnital_leftAdd : EckmannHilton.IsUnital (· +ₗ ·) 0 := by
  have hr : ∀ f : X ⟶ Y, biprod.lift (0 : X ⟶ Y) f = f ≫ biprod.inr := by
    intro f
    ext
    · simp
    · simp [Category.assoc]
  have hl : ∀ f : X ⟶ Y, biprod.lift f (0 : X ⟶ Y) = f ≫ biprod.inl := by
    intro f
    ext
    · simp
    · simp [biprod.lift_snd, Category.assoc, comp_zero]
  exact {
    left_id := fun f => by simp [hr f, leftAdd, Category.assoc, Category.comp_id, biprod.inr_desc],
    right_id := fun f => by simp [hl f, leftAdd, Category.assoc, Category.comp_id, biprod.inl_desc]
  }

theorem isUnital_rightAdd : EckmannHilton.IsUnital (· +ᵣ ·) 0 := by
  have h₂ : ∀ f : X ⟶ Y, biprod.desc (0 : X ⟶ Y) f = biprod.snd ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_snd_assoc]
  have h₁ : ∀ f : X ⟶ Y, biprod.desc f (0 : X ⟶ Y) = biprod.fst ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_fst_assoc, zero_comp]
  exact {
    left_id := fun f => by simp [h₂ f, rightAdd, biprod.lift_snd_assoc, Category.id_comp],
    right_id := fun f => by simp [h₁ f, rightAdd, biprod.lift_fst_assoc, Category.id_comp]
  }

theorem distrib (f g h k : X ⟶ Y) : (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k := by
  let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift (biprod.desc f g) (biprod.desc h k)
  have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by ext <;> simp [diag]
  have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by ext <;> simp [diag]
  have h₁ : biprod.lift (f +ᵣ g) (h +ᵣ k) = biprod.lift (𝟙 X) (𝟙 X) ≫ diag := by
    ext <;> cat_disch
  have h₂ : diag ≫ biprod.desc (𝟙 Y) (𝟙 Y) = biprod.desc (f +ₗ h) (g +ₗ k) := by
    ext <;> simp [reassoc_of% hd₁, reassoc_of% hd₂]
  rw [leftAdd, h₁, Category.assoc, h₂, rightAdd]

/-- In a category with binary biproducts, the morphisms form a commutative monoid. -/
@[instance_reducible]
def addCommMonoidHomOfHasBinaryBiproducts : AddCommMonoid (X ⟶ Y) where
  add := (· +ᵣ ·)
  add_assoc :=
    (EckmannHilton.mul_assoc (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).assoc
  zero_add := (isUnital_rightAdd X Y).left_id
  add_zero := (isUnital_rightAdd X Y).right_id
  add_comm :=
    (EckmannHilton.mul_comm (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).comm
  nsmul := letI : Add (X ⟶ Y) := ⟨(· +ᵣ ·)⟩; nsmulRec

end

section

variable {X Y Z : C}

attribute [local instance] addCommMonoidHomOfHasBinaryBiproducts

theorem add_eq_right_addition (f g : X ⟶ Y) : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g :=
  rfl

theorem add_eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) :=
  congr_fun₂ (EckmannHilton.mul (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).symm f
    g

theorem add_comp (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  simp only [add_eq_right_addition, Category.assoc]
  congr
  ext <;> simp

theorem comp_add (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  simp only [add_eq_left_addition, ← Category.assoc]
  congr
  ext <;> simp

end

end CategoryTheory.SemiadditiveOfBinaryBiproducts
