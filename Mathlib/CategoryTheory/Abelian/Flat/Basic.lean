/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory

/-!
# Flat objects

-/

namespace CategoryTheory

open MonoidalCategory

variable {A : Type*} [Category A]
  [MonoidalCategory A]

namespace ObjectProperty

def flat : ObjectProperty A := fun X ↦
  ObjectProperty.exactFunctor (tensorLeft X) ∧
    ObjectProperty.exactFunctor (tensorRight X)

variable {X : A}

lemma flat.tensorLeft (hX : flat X) :
    ObjectProperty.exactFunctor (tensorLeft X) := hX.1

lemma flat.tensorRight (hX : flat X) :
    ObjectProperty.exactFunctor (tensorRight X) := hX.2

instance : (flat (A := A)).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨ObjectProperty.exactFunctor.prop_of_iso
      ((curriedTensor A).mapIso e) h.1,
      ObjectProperty.exactFunctor.prop_of_iso
        ((curriedTensor A).flip.mapIso e) h.2⟩

end ObjectProperty

end CategoryTheory
