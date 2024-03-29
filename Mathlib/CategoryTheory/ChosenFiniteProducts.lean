/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Categories with chosen finite products

We introduce a class, `ChosenFiniteProducts`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

Given a category with such an instance, we also provide the associated
symmetric monoidal structure so that one can write `X ⊗ Y` for the explicit
binary product and `𝟙_ C` for the explicit terminal object.

# Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the tensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v u

/--
An instance of `ChosenFiniteProducts C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
class ChosenFiniteProducts (C : Type u) [Category.{v} C] where
  /-- A choice of a limit binary fan for any two objects of the category.-/
  product : (X Y : C) → Limits.LimitCone (Limits.pair X Y)
  /-- A choice of a terminal object. -/
  terminal : Limits.LimitCone (Functor.empty.{v} C)

namespace ChosenFiniteProducts

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    MonoidalCategory C :=
  monoidalOfChosenFiniteProducts terminal product

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    SymmetricCategory C :=
  symmetricOfChosenFiniteProducts _ _

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

open MonoidalCategory

/--
The unique map to the terminal object.
-/
def toUnit (X : C) : X ⟶ 𝟙_ C :=
  terminal.isLimit.lift <| .mk _ <| .mk (fun x => x.as.elim) fun x => x.as.elim

instance (X : C) : Unique (X ⟶ 𝟙_ C) where
  default := toUnit _
  uniq _ := terminal.isLimit.hom_ext fun ⟨j⟩ => j.elim

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
lemma toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g :=
  Subsingleton.elim _ _

/--
Construct a morphism to the product given its two components.
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊗ Y :=
  (product X Y).isLimit.lift <| Limits.BinaryFan.mk f g

/--
The first projection from the product.
-/
def fst (X Y : C) : X ⊗ Y ⟶ X :=
  letI F : Limits.BinaryFan X Y := (product X Y).cone
  F.fst

/--
The second projection from the product.
-/
def snd (X Y : C) : X ⊗ Y ⟶ Y :=
  letI F : Limits.BinaryFan X Y := (product X Y).cone
  F.snd

@[reassoc (attr := simp)]
lemma lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f := by
  simp [lift, fst]

@[reassoc (attr := simp)]
lemma lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g := by
  simp [lift, snd]

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : T ⟶ X ⊗ Y)
    (h_fst : f ≫ fst _ _ = g ≫ fst _ _)
    (h_snd : f ≫ snd _ _ = g ≫ snd _ _) :
    f = g :=
  (product X Y).isLimit.hom_ext fun ⟨j⟩ => j.recOn h_fst h_snd

/--
Construct an instance of `ChosenFiniteProducts C` given an instance of `HasFiniteProducts C`.
-/
noncomputable
def ofFiniteProducts
    (C : Type u) [Category.{v} C] [Limits.HasFiniteProducts C] :
    ChosenFiniteProducts C where
  product X Y := Limits.getLimitCone (Limits.pair X Y)
  terminal := Limits.getLimitCone (Functor.empty C)

instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : ∀ (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk <| ChosenFiniteProducts.product _ _
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ _)
  hasFiniteProducts_of_has_binary_and_terminal

end ChosenFiniteProducts

end CategoryTheory
