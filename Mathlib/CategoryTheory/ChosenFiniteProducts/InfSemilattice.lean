/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Chosen finite products for the preorder category of a meet-semilattice with a greatest element

The preorder category of a meet-semilattice `C` with a greatest element has chosen finite products.

A symmetric monoidal structure on the preorder category is automatically provided by the
instances `monoidalOfChosenFiniteProducts` and `ChosenFiniteProducts.instSymmetricCategory`.

-/

namespace CategoryTheory

open Category MonoidalCategory

universe u

variable (C : Type u) [SemilatticeInf C] [OrderTop C]

namespace SemilatticeInf

/-- Chosen finite products for the preorder category of a meet-semilattice with a greatest element-/
noncomputable scoped instance chosenFiniteProducts : ChosenFiniteProducts C where
  terminal := ⟨_, Preorder.isTerminalTop C⟩
  product X Y := ⟨_,  Preorder.isLimitBinaryFan X Y⟩

lemma tensorObj {C : Type u} [SemilatticeInf C] [OrderTop C] {X Y : C} : X ⊗ Y = X ⊓ Y := rfl

lemma tensorUnit {C : Type u} [SemilatticeInf C] [OrderTop C] :
    𝟙_ C = ⊤ := rfl

end SemilatticeInf

end CategoryTheory
