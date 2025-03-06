/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The pointwise monoidal structure on the product of families of monoidal categories

Given a family of monoidal categories `C i`, we define a monoidal structure on
`Π i, C i` where the tensor product is defined pointwise.

-/

namespace CategoryTheory

namespace Pi

open Category MonoidalCategory

universe w₁ v₁ u₁

variable {I : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]
[∀ i, MonoidalCategory (C i)]

/-- `Pi.monoidal C` equips the product of an indexed family of categories with
the pointwise monoidal structure. -/
@[simps]
instance monoidal : MonoidalCategory.{max w₁ v₁} (∀ i, C i) where
  tensorObj X Y := fun i ↦ X i ⊗ Y i
  whiskerLeft X _ _ f := fun i ↦ X i ◁ f i
  whiskerRight f Z := fun i ↦ f i ▷ Z i
  tensorHom f g := fun i ↦ f i ⊗ g i
  tensorUnit := fun i ↦ 𝟙_ (C i)
  associator X Y Z := isoMk (fun i ↦ α_ (X i) (Y i) (Z i))
  leftUnitor X := isoMk (fun i ↦ λ_ (X i))
  rightUnitor X := isoMk (fun i ↦ ρ_ (X i))
  tensorHom_def _ _ := by ext i; simp only [tensorHom, tensorHom_def, comp_apply]

end Pi

end CategoryTheory
