/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
/-!
`Cat` is a category on its own, views categories as its objects and functors as its morphism.
On one hand, we can build a cartesian product category out of a pair of categories.
On the other hand `Cat`, as a category, comes with its own definition for an object to be a product.

We verify here that the product *in* `Cat` is given by the usual product of categories viewed
as an object.

## Implementation notes

We rely on `CategoryTheory.ChosenFiniteProducts` to provide the full monoidal structure
-/

universe v u

namespace CategoryTheory.Cat

open Limits

/-- The chosen terminal object in `Cat`. -/
abbrev OneCat : Cat := Cat.of (ULift (ULiftHom (Discrete Unit)))

/-- The chosen terminal object in `Cat` is terminal. -/
def isTerminalPUnit : IsTerminal OneCat :=
  IsTerminal.ofUniqueHom (fun _ ↦ (Functor.const _).obj ⟨⟨⟨⟩⟩⟩) fun _ _ ↦ rfl

/-- The product cone in `Cat`. -/
def prodCone (C D : Cat.{v,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

/-- The product cone in `Cat` is indeed a product. -/
def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => S.fst.prod' S.snd) (fun _ => rfl) (fun _ => rfl) (fun _ _ h1 h2 =>
    Functor.hext
      (fun _ ↦ Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := isTerminalPUnit }

/-- The monoidal category instance for `Cat`-/
def catIsMonoidal := ChosenFiniteProducts.instMonoidalCategory (Cat)

example : MonoidalCategory Cat := by infer_instance

/-- The symmetric monoidal category instance for `Cat`-/
def catIsSymmetricMonoidal := ChosenFiniteProducts.instSymmetricCategory (Cat)

example : SymmetricCategory Cat := by infer_instance

end CategoryTheory.Cat
