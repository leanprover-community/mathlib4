/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
/-!
# Chosen finite products in `Type`

This file proves that the cartesian product of a pair of categories agrees with the
product in `Type`, and provides the associated `ChosenFiniteProducts` instance.
This file mirrors `CategoryTheory/ChosenFiniteProducts/Cat.lean`
-/

universe u

namespace CategoryTheory

namespace Types

open Limits

/-- The chosen terminal object in `Types`. -/
abbrev chosenTerminal : Type u := PUnit

/-- The chosen terminal object in `Type` is terminal.
Note: We are not using `Types.` isTerminalPunit because the latter is noncomputable. -/
def chosenTerminalIsTerminal : IsTerminal chosenTerminal :=
  IsTerminal.ofUniqueHom (fun _ ↦ fun _ ↦ .unit) fun _ _ ↦ rfl


/-- The chosen product of categories `C × D` yields a product cone in `Type`. -/
def prodCone (E : Type u) (F : Type u) : BinaryFan E F :=
  .mk (P := (Prod E F : Type u)) (·.fst) (·.snd)

/-- The product cone in `Type` is indeed a product. -/
def isLimitProdCone (E F : Type u) : IsLimit (prodCone E F) := by
  apply BinaryFan.isLimitMk
  rotate_right
  · exact fun S s => ⟨S.fst s, S.snd s⟩
  · exact fun _ ↦ rfl
  · exact fun _ ↦ rfl
  · intro _ _ h₁ h₂
    ext x
    · exact congrFun h₁ x
    · exact congrFun h₂ x

instance : ChosenFiniteProducts (Type u) where
  product (X Y : Type u) := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := chosenTerminalIsTerminal }

/-- A monoidal instance for Type u is provided through monoidalOfChosenFiniteProducts -/
example : MonoidalCategory (Type u) := by infer_instance

/-- A symmetric monoidal instance for Type u is provided through symmetricOfChosenFiniteProducts -/
example : SymmetricCategory (Type u) := by infer_instance

namespace Monoidal

open MonoidalCategory

lemma tensorObj (E : Type u) (F : Type u) : E ⊗ F = (E × F) := rfl

lemma whiskerLeft (X : Type u) {A : Type u} {B : Type u} (f : A ⟶ B) :
    X ◁ f =  Prod.map id f := rfl

lemma whiskerLeft_fst (X : Type u) {A : Type u} {B : Type u} (f : A ⟶ B) :
    (X ◁ f) ≫ (·.fst) = (·.fst) := rfl

lemma whiskerLeft_snd (X : Type u) {A : Type u} {B : Type u} (f : A ⟶ B) :
    (X ◁ f) ≫ (·.snd) = (·.snd) ≫ f := rfl

lemma whiskerRight {A : Type u} {B : Type u} (f : A ⟶ B) (X : Type u) :
    f ▷  X  = Prod.map f id := rfl

lemma whiskerRight_fst {A : Type u} {B : Type u} (f : A ⟶ B) (X : Type u) :
    (f ▷ X) ≫ (·.fst) = (·.fst) ≫ f := rfl

lemma whiskerRight_snd {A : Type u} {B : Type u} (f : A ⟶ B) (X : Type u) :
    (f ▷ X) ≫ (·.snd)  = (·.snd) := rfl

lemma tensorHom {A : Type u} {B : Type u} (f : A ⟶ B) {X : Type u} {Y : Type u} (g : X ⟶ Y) :
    f ⊗ g = Prod.map f g := rfl

lemma tensorUnit : 𝟙_ (Type u) = chosenTerminal := rfl

lemma associator_hom (X : Type u) (Y : Type u) (Z : Type u) :
    (associator X Y Z).hom = (Equiv.prodAssoc X Y Z).toFun := rfl

lemma associator_inv (X : Type u) (Y : Type u) (Z : Type u) :
    (associator X Y Z).inv = (Equiv.prodAssoc X Y Z).invFun := rfl

lemma leftUnitor_hom (C : Type u) : (λ_ C).hom = (·.snd) := rfl

lemma leftUnitor_inv (C : Type u) : (λ_ C).inv = fun x => ⟨.unit, x⟩:= rfl

lemma rightUnitor_hom (C : Type u) : (ρ_ C).hom = (·.fst) := rfl

lemma rightUnitor_inv (C : Type u) : (ρ_ C).inv = fun x => ⟨x, .unit⟩ := rfl

end CategoryTheory.Types.Monoidal
