/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Support of an element under an action action

Given an action of a group `G` on a type `α`, we say that a set `s : Set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/

assert_not_exists MonoidWithZero

open Pointwise

variable {G H α β : Type*}

namespace MulAction

section SMul

variable (G) [SMul G α] [SMul G β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive "A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`."]
def Supports (s : Set α) (b : β) :=
  ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b

variable {s t : Set α} {a : α} {b : β}

@[to_additive]
theorem supports_of_mem (ha : a ∈ s) : Supports G s a := fun _ h => h ha

variable {G}

@[to_additive]
theorem Supports.mono (h : s ⊆ t) (hs : Supports G s b) : Supports G t b := fun _ hg =>
  (hs _) fun _ ha => hg <| h ha

end SMul

variable [Group H] [SMul G α] [SMul G β] [MulAction H α] [SMul H β] [SMulCommClass G H β]
  [SMulCommClass G H α] {s : Set α} {b : β}

-- TODO: This should work without `SMulCommClass`
@[to_additive]
theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) := by
  rintro g' hg'
  rw [smul_comm, h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this

end MulAction
