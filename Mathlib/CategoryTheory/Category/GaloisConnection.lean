/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Order.GaloisConnection

/-!

# Galois connections between preorders are adjunctions.

* `GaloisConnection.adjunction` is the adjunction associated to a galois connection.

-/


universe u v

section

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- A galois connection between preorders induces an adjunction between the associated categories.
-/
def GaloisConnection.adjunction {l : X → Y} {u : Y → X} (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        ⟨fun f => CategoryTheory.homOfLE (gc.le_u f.le),
         fun f => CategoryTheory.homOfLE (gc.l_le f.le), _, _⟩ }

end

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- An adjunction between preorder categories induces a galois connection.
-/
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.hom).le, fun h => ((adj.homEquiv x y).invFun h.hom).le⟩

end CategoryTheory
