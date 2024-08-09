/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Relation induced by a category

The hom-set of a category can be seen as a (proof relevant) relation on its objects :
Two objects are connected if there is an arrow between them.
This relation is not an equivalence but can be turned into one.

## Equivalence relation induced by a category

One can take the equivalence closure, under which two objects are connected
iif there is a zigzag of arrows between them.

As a relation, it is proof irrelavant, in the sense that it does not know by which specific zigzag
two elements are connected, only that they are.

## Implmentation notes

We rely on `CategoryTheory.ConnectedComponents` and not on `Quiver.ConnectedComponent`

-/
namespace CategoryTheory.Cat

variable {C D : Cat}
variable {a b : C}
variable (F : C ⥤ D)

open Relation

/-- A zigzag in a discrete category entails an equality of its extremities -/
lemma eq_of_zigzag (X) {a b : Discrete X} (zab : ReflTransGen Zag a b) : a.as = b.as := by
  induction zab with
  | refl => rfl
  | @tail b c _ zbc eqab  =>
    exact eqab.trans ( zbc.elim (Nonempty.elim · Discrete.eq_of_hom)
      (Eq.symm ∘ (Nonempty.elim · Discrete.eq_of_hom)))

end CategoryTheory.Cat
