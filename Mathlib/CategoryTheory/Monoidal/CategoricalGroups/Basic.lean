/-
Copyright (c) 2025 Amogh Parab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amogh Parab
-/
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import Mathlib.CategoryTheory.CommSq

/-!
# Categorical Groups

The basic definitions of categorical groups, symmetric categorical groups, and
categorical group functors.

## Implementation note

We make `BraidedCategory` another typeclass, but then have `SymmetricCategory` extend this.
The rationale is that we are not carrying any additional data, just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

## References

* [Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, Victor Ostrik, *Tensor categories*][egno15]

-/



universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/-- A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class CategoricalGroup (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  /-- The negator functor -/
  negator : C ⥤  C
  /-- Left cancellation isomorphism -/
  cancel_left : ∀ X : C, negator.obj X ⊗ X ≅ 𝟙_ C
  /-- Right cancellation isomorphism -/
  cancel_right : ∀ X : C, X ⊗ negator.obj X ≅ 𝟙_ C
  cancel_naturality_left :
    ∀  {X Y : C} (f : X ⟶ Y),
      (negator.map f) ▷ X ≫ (negator.obj Y) ◁ f ≫ (cancel_left Y).hom = (cancel_left X).hom  := by
    cat_disch
  cancel_naturality_right :
    ∀ {X Y : C} (f : X ⟶ Y),
      (X ◁ (negator.map f)) ≫ (f ▷ (negator.obj Y)) ≫ ((cancel_right Y).hom) = (cancel_right X).hom := by
    cat_disch




  /-- The first hexagon identity. -/
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    cat_disch
  /-- The second hexagon identity. -/
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
    cat_disch

attribute [reassoc (attr := simp)]
  BraidedCategory.braiding_naturality_left
  BraidedCategory.braiding_naturality_right
attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open BraidedCategory

@[inherit_doc]
notation "β_" => BraidedCategory.braiding

namespace BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

@[simp, reassoc]
theorem braiding_tensor_left_hom (X Y Z : C) :
    (β_ (X ⊗ Y) Z).hom  =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫
        (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom := by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[deprecated (since := "2025-06-24")] alias braiding_tensor_left := braiding_tensor_left_hom

@[simp, reassoc]
theorem braiding_tensor_right_hom (X Y Z : C) :
    (β_ X (Y ⊗ Z)).hom  =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv := by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[deprecated (since := "2025-06-24")] alias braiding_tensor_right := braiding_tensor_right_hom

@[simp, reassoc]
theorem braiding_tensor_left_inv (X Y Z : C) :
    (β_ (X ⊗ Y) Z).inv  =
      (α_ Z X Y).inv ≫ (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫
        X ◁ (β_ Y Z).inv ≫ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[deprecated (since := "2025-06-24")] alias braiding_inv_tensor_left := braiding_tensor_left_inv

@[simp, reassoc]
theorem braiding_tensor_right_inv (X Y Z : C) :
    (β_ X (Y ⊗ Z)).inv  =
      (α_ Y Z X).hom ≫ Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫
        (β_ X Y).inv ▷ Z ≫ (α_ X Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[deprecated (since := "2025-06-24")] alias braiding_inv_tensor_right := braiding_tensor_right_inv

@[reassoc (attr := simp)]
theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ₘ f) := by
  rw [tensorHom_def' f g, tensorHom_def g f]
  simp_rw [Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
theorem braiding_inv_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ f ≫ (β_ Z X).inv = (β_ Y X).inv ≫ f ▷ X :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality_left f X

@[reassoc (attr := simp)]
theorem braiding_inv_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z ≫ (β_ Z Y).inv = (β_ Z X).inv ≫ Z ◁ f :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality_right Z f

@[reassoc (attr := simp)]
theorem braiding_inv_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (β_ Y' Y).inv = (β_ X' X).inv ≫ (g ⊗ₘ f) :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality g f

/-- In a braided monoidal category, the functors `tensorLeft X` and
`tensorRight X` are isomorphic. -/
@[simps]
def tensorLeftIsoTensorRight (X : C) :
    tensorLeft X ≅ tensorRight X where
  hom := { app Y := (β_ X Y).hom }
  inv := { app Y := (β_ X Y).inv }

@[reassoc]
theorem yang_baxter (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
    Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫
      (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom := by
  rw [← braiding_tensor_right_hom_assoc X Y Z, ← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id, comp_id, ← braiding_naturality_right, braiding_tensor_right_hom]

theorem yang_baxter' (X Y Z : C) :
    (β_ X Y).hom ▷ Z ⊗≫ Y ◁ (β_ X Z).hom ⊗≫ (β_ Y Z).hom ▷ X =
      𝟙 _ ⊗≫ (X ◁ (β_ Y Z).hom ⊗≫ (β_ X Z).hom ▷ Y ⊗≫ Z ◁ (β_ X Y).hom) ⊗≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv, ← cancel_mono (α_ Z Y X).hom]
  convert yang_baxter X Y Z using 1
  all_goals monoidal

theorem yang_baxter_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫
    whiskerLeftIso Y (β_ X Z) ≪≫ (α_ Y Z X).symm ≪≫
    whiskerRightIso (β_ Y Z) X ≪≫ (α_ Z Y X) =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫
      whiskerRightIso (β_ X Z) Y ≪≫ α_ Z X Y ≪≫
      whiskerLeftIso Z (β_ X Y) := Iso.ext (yang_baxter X Y Z)

theorem hexagon_forward_iso (X Y Z : C) :
    α_ X Y Z ≪≫ β_ X (Y ⊗ Z) ≪≫ α_ Y Z X =
      whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) :=
  Iso.ext (hexagon_forward X Y Z)

theorem hexagon_reverse_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ β_ (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫ whiskerRightIso (β_ X Z) Y :=
  Iso.ext (hexagon_reverse X Y Z)

@[reassoc]
theorem hexagon_forward_inv (X Y Z : C) :
    (α_ Y Z X).inv ≫ (β_ X (Y ⊗ Z)).inv ≫ (α_ X Y Z).inv =
      Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z := by
  simp

@[reassoc]
theorem hexagon_reverse_inv (X Y Z : C) :
    (α_ Z X Y).hom ≫ (β_ (X ⊗ Y) Z).inv ≫ (α_ X Y Z).hom =
      (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv := by
  simp

end BraidedCategory


end CategoryTheory
