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
abbrev OneCat : Cat := Cat.of (Discrete PUnit)

/-- The chosen terminal object in `Cat` is terminal. -/
def isTerminalPUnit : IsTerminal OneCat where
  lift s := Functor.star s.pt
  fac _ (j : Discrete PEmpty.{1}) := PEmpty.elim j.as
  uniq s m _ :=  Functor.punit_ext' m (Functor.star s.pt)

/-- The product cone in `Cat`. -/
def prodCone (C D : Cat.{v,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

/-- The product cone in `Cat` is indeed a product. -/
def isLimitProdCone (X Y : Cat.{v,u}) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => Functor.prod' S.fst S.snd)
  (fun S => rfl)
  (fun S => rfl)
  (fun S m (h1 : m ≫ Prod.fst X Y = S.fst) (h2 : m ≫ Prod.snd X Y = S.snd) => by
    fapply Functor.hext
    · intro X
      apply Prod.ext <;> simp [← h1, ← h2]
    · intro X Y f
      dsimp
      rw [← h1, ← h2]
      rfl)

instance : ChosenFiniteProducts Cat.{u,u} where
  product (X Y : Cat) := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := isTerminalPUnit }

def catIsMonoidal := ChosenFiniteProducts.instMonoidalCategory (Cat.{u,u})

/-- The monoidal category instance for `Cat`-/
instance : MonoidalCategory Cat.{u,u} := catIsMonoidal

def catIsSymmetricMonoidal := ChosenFiniteProducts.instSymmetricCategory (Cat.{u,u})

/-- The symmetric monoidal category instance for `Cat`-/
instance : SymmetricCategory Cat.{u,u} := catIsSymmetricMonoidal


end CategoryTheory.Cat
