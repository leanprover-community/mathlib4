/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# Lattices have chosen finite products

The preorder category of a meet-semilattice `C` with a greatest element has chosen finite products.

-/

namespace CategoryTheory

open Category Limits MonoidalCategory

universe u

variable (C : Type u) [SemilatticeInf C] [OrderTop C]

namespace SemilatticeInf

/-- The chosen terminal object in the preorder category of `C`. -/
abbrev chosenTerminal : C := ⊤

/-- The chosen terminal object in the preoder category of `C` is terminal. -/
def chosenTerminalIsTerminal : IsTerminal (chosenTerminal C) where
  lift s := homOfLE (le_top)

section

variable {C}

variable (X Y : C)

/-- The chosen binary product in the preorder category of `C`. -/
def chosenProd : C := X ⊓ Y

namespace chosenProd

/-- The first projection `chosenProd X Y ⟶ X`. -/
def fst : chosenProd X Y ⟶ X := homOfLE (inf_le_left)

/-- The second projection `chosenProd X Y ⟶ Y`. -/
def snd : chosenProd X Y ⟶ Y := homOfLE (inf_le_right)

/-- `chosenProd X Y` is a binary product of `X` and `Y`. -/
def isLimit : IsLimit (BinaryFan.mk (fst X Y) (snd X Y)) where
  lift s := homOfLE <| le_inf (leOfHom <| s.π.app <|
  ⟨WalkingPair.left⟩) (leOfHom <| s.π.app <| ⟨WalkingPair.right⟩)

end chosenProd

end

/-- Chosen finite products for the preorder category of a meet-semilattice with a greatest element-/
noncomputable instance : ChosenFiniteProducts C where
  terminal := ⟨_, chosenTerminalIsTerminal C⟩
  product X Y := ⟨_, chosenProd.isLimit X Y⟩

/-- A monoidal structure on the preorder category of a meet-semilattice with a greatest element
is provided by the instance `monoidalOfChosenFiniteProducts`. -/
noncomputable instance : MonoidalCategory C := by
  infer_instance

noncomputable instance : SymmetricCategory C := by
  infer_instance

namespace Monoidal

open MonoidalCategory ChosenFiniteProducts

lemma tensorObj {C : Type u} [Lattice C] [OrderTop C] {X Y : C} : X ⊗ Y = X ⊓ Y := rfl

lemma tensorUnit {C : Type u} [Lattice C] [OrderTop C] :
    𝟙_ C = SemilatticeInf.chosenTerminal C := rfl

end Monoidal

end SemilatticeInf

end CategoryTheory
