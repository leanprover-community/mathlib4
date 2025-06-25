/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Dialectica.Basic

/-!
# The Dialectica category is symmetric monoidal

We show that the category `Dial` has a symmetric monoidal category structure.
-/

noncomputable section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

/-- The object `X ⊗ Y` in the `Dial C` category just tuples the left and right components. -/
@[simps] def tensorObjImpl (X Y : Dial C) : Dial C where
  src := X.src ⨯ Y.src
  tgt := X.tgt ⨯ Y.tgt
  rel :=
    (Subobject.pullback (prod.map π₁ π₁)).obj X.rel ⊓
    (Subobject.pullback (prod.map π₂ π₂)).obj Y.rel

/-- The functorial action of `X ⊗ Y` in `Dial C`. -/
@[simps] def tensorHomImpl {X₁ X₂ Y₁ Y₂ : Dial C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    tensorObjImpl X₁ Y₁ ⟶ tensorObjImpl X₂ Y₂ where
  f := prod.map f.f g.f
  F := π(prod.map π₁ π₁ ≫ f.F, prod.map π₂ π₂ ≫ g.F)
  le := by
    simp only [tensorObjImpl, Subobject.inf_pullback]
    apply inf_le_inf <;> rw [← Subobject.pullback_comp, ← Subobject.pullback_comp]
    · have := (Subobject.pullback (prod.map π₁ π₁ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le f)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert this using 3 <;> simp
    · have := (Subobject.pullback (prod.map π₂ π₂ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le g)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert this using 3 <;> simp

/-- The unit for the tensor `X ⊗ Y` in `Dial C`. -/
@[simps] def tensorUnitImpl : Dial C := { src := ⊤_ _, tgt := ⊤_ _, rel := ⊤ }

/-- Left unit cancellation `1 ⊗ X ≅ X` in `Dial C`. -/
@[simps!] def leftUnitorImpl (X : Dial C) : tensorObjImpl tensorUnitImpl X ≅ X :=
  isoMk (Limits.prod.leftUnitor _) (Limits.prod.leftUnitor _) <| by simp [Subobject.pullback_top]

/-- Right unit cancellation `X ⊗ 1 ≅ X` in `Dial C`. -/
@[simps!] def rightUnitorImpl (X : Dial C) : tensorObjImpl X tensorUnitImpl ≅ X :=
  isoMk (Limits.prod.rightUnitor _) (Limits.prod.rightUnitor _) <| by simp [Subobject.pullback_top]

/-- The associator for tensor, `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` in `Dial C`. -/
@[simps!]
def associatorImpl (X Y Z : Dial C) :
    tensorObjImpl (tensorObjImpl X Y) Z ≅ tensorObjImpl X (tensorObjImpl Y Z) :=
  isoMk (prod.associator ..) (prod.associator ..) <| by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_assoc]

@[simps!]
instance : MonoidalCategoryStruct (Dial C) where
  tensorUnit := tensorUnitImpl
  tensorObj := tensorObjImpl
  whiskerLeft X _ _ f := tensorHomImpl (𝟙 X) f
  whiskerRight f Y := tensorHomImpl f (𝟙 Y)
  tensorHom := tensorHomImpl
  leftUnitor := leftUnitorImpl
  rightUnitor := rightUnitorImpl
  associator := associatorImpl

theorem tensor_id (X₁ X₂ : Dial C) : (𝟙 X₁ ⊗ₘ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ ⊗ X₂ : Dial C) := by aesop_cat

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  ext <;> simp; ext <;> simp <;> (rw [← Category.assoc]; congr 1; simp)

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by aesop_cat

theorem leftUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (Dial C)) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

theorem rightUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ (Dial C))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

theorem pentagon (W X Y Z : Dial C) :
    (tensorHom (associator W X Y).hom (𝟙 Z)) ≫ (associator W (tensorObj X Y) Z).hom ≫
      (tensorHom (𝟙 W) (associator X Y Z).hom) =
    (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext <;> simp

theorem triangle (X Y : Dial C) :
    (associator X (𝟙_ (Dial C)) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
    tensorHom (rightUnitor X).hom (𝟙 Y) := by aesop_cat

instance : MonoidalCategory (Dial C) :=
  .ofTensorHom
    (tensor_id := tensor_id)
    (tensor_comp := tensor_comp)
    (associator_naturality := associator_naturality)
    (leftUnitor_naturality := leftUnitor_naturality)
    (rightUnitor_naturality := rightUnitor_naturality)
    (pentagon := pentagon)
    (triangle := triangle)

/-- The braiding isomorphism `X ⊗ Y ≅ Y ⊗ X` in `Dial C`. -/
@[simps!] def braiding (X Y : Dial C) : tensorObj X Y ≅ tensorObj Y X :=
  isoMk (prod.braiding ..) (prod.braiding ..) <| by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_comm]

theorem symmetry (X Y : Dial C) :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (tensorObj X Y) := by aesop_cat

theorem braiding_naturality_right (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z) :
    tensorHom (𝟙 X) f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ tensorHom f (𝟙 X) := by aesop_cat

theorem braiding_naturality_left {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C) :
    tensorHom f (𝟙 Z) ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ tensorHom (𝟙 Z) f := by aesop_cat

theorem hexagon_forward (X Y Z : Dial C) :
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom =
      tensorHom (braiding X Y).hom (𝟙 Z) ≫ (associator Y X Z).hom ≫
      tensorHom (𝟙 Y) (braiding X Z).hom := by aesop_cat

theorem hexagon_reverse (X Y Z : Dial C) :
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv =
      tensorHom (𝟙 X) (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
      tensorHom (braiding X Z).hom (𝟙 Y) := by aesop_cat

instance : SymmetricCategory (Dial C) where
  braiding := braiding
  braiding_naturality_right := braiding_naturality_right
  braiding_naturality_left := braiding_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  symmetry := symmetry

end Dial

end CategoryTheory
