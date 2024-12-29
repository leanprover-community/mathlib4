/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Limits and colimits indexed by preorders

In this file, we show that if a preordered type `J` has a least element,
then `⊥` is an initial object, which implies the existence of all limits indexed by `J`,
(The dual result is also obtained.)

-/

universe v u w

open CategoryTheory Limits

namespace Preorder

variable (J : Type w) [Preorder J] (C : Type u) [Category.{v} C]

section OrderBot

variable [OrderBot J]

/-- The least element in a preordered type is initial in the category
associated to this preorder. -/
def isInitialBot : IsInitial (⊥ : J) := IsInitial.ofUnique _

instance : HasInitial J := hasInitial_of_unique ⊥

instance : HasLimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

end OrderBot

section OrderTop

variable [OrderTop J]

/-- The greatest element of a preordered type is terminal in the category
associated to this preorder. -/
def isTerminalBot : IsTerminal (⊤ : J) := IsTerminal.ofUnique _

instance : HasTerminal J := hasTerminal_of_unique ⊤

instance : HasColimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

end OrderTop

end Preorder
