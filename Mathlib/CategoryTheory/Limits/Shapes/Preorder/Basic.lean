/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Limits and colimits indexed by preorders

In this file, we obtain the following very basic results
about limits and colimits indexed by a preordered type `J`:
* a least element in `J` implies the existence of all limits indexed by `J`
* a greatest element in `J` implies the existence of all colimits indexed by `J`

-/

public section

universe v v' u u' w

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] (J : Type w) [Preorder J]

namespace Preorder

section OrderBot

instance [OrderBot J] : HasLimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

instance [Nonempty J] [Subsingleton J] : HasLimitsOfShape J C :=
  have : OrderBot J := { bot := Classical.arbitrary _, bot_le _ := by simp }
  inferInstance

end OrderBot

section OrderTop

instance [OrderTop J] : HasColimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

instance [Nonempty J] [Subsingleton J] : HasColimitsOfShape J C :=
  have : OrderTop J := { top := Classical.arbitrary _, le_top _ := by simp }
  inferInstance

end OrderTop

end Preorder
