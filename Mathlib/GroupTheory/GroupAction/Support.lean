/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Pointwise.SMul

#align_import group_theory.group_action.support from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Support of an element under an action action

Given an action of a group `G` on a type `α`, we say that a set `s : Set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/

open Pointwise

variable {G H α β : Type*}

namespace MulAction

section SMul

variable (G) [SMul G α] [SMul G β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive "A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`."]
def Supports (s : Set α) (b : β) :=
  ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b
#align mul_action.supports MulAction.Supports
#align add_action.supports AddAction.Supports

variable {s t : Set α} {a : α} {b : β}

@[to_additive]
theorem supports_of_mem (ha : a ∈ s) : Supports G s a := fun _ h => h ha
#align mul_action.supports_of_mem MulAction.supports_of_mem
#align add_action.supports_of_mem AddAction.supports_of_mem

variable {G}

@[to_additive]
theorem Supports.mono (h : s ⊆ t) (hs : Supports G s b) : Supports G t b := fun _ hg =>
  (hs _) fun _ ha => hg <| h ha
#align mul_action.supports.mono MulAction.Supports.mono
#align add_action.supports.mono AddAction.Supports.mono

end SMul

variable [Group H] [SMul G α] [SMul G β] [MulAction H α] [SMul H β] [SMulCommClass G H β]
  [SMulCommClass G H α] {s t : Set α} {b : β}

-- TODO: This should work without `SMulCommClass`
@[to_additive]
theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) := by
  rintro g' hg'
  rw [smul_comm, h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this
#align mul_action.supports.smul MulAction.Supports.smul
#align add_action.supports.vadd AddAction.Supports.vadd

end MulAction
