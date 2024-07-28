/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland

-/

import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
`Cat` views categories as its objects.

It is a category on its own, and we know categories have a cartesian product, which is defined in
mathlib.

This object verifies the property required to be a product in the category `Cat`

## Implementation notes

We rely on `ChosenFiniteProducts` to provide the full monoidal structure

-/

universe v u

namespace CategoryTheory.Cat

open Limits


/-- The chosen terminal object in `Cat`. -/
abbrev One : Cat := Cat.of (Discrete PUnit)

/-- The chosen terminal object in `Cat` is terminal. -/
def isTerminalPUnit : IsTerminal One where
  lift s := Functor.star s.pt
  fac s (j : Discrete PEmpty.{1}) := by dsimp; exact PEmpty.elim j.as
  uniq s m _ :=  Functor.punit_ext' m (Functor.star s.pt)

/-- The product cone in `Cat`. -/
def prodCone (C D : Cat.{v,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

/-- The product cone in `Cat` is indeed a product. -/
def isLimitProdCone (X Y : Cat.{v,u}) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => Functor.prod' S.fst S.snd)-- def prod' (F : A ⥤ B) (G : A ⥤ C) : A ⥤ B × C
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

instance i : ChosenFiniteProducts Cat.{u,u} where
  product (X Y : Cat): _ := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := isTerminalPUnit }


end CategoryTheory.Cat
