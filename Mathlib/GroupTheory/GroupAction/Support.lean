/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Support of an element under an action

Given an action of a group `G` on a type `α`, we say that a set `s : Set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open scoped Pointwise

variable {G H α β : Type*}

namespace MonoidAction

section SMul

variable (G) [SMul G α] [SMul G β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive /-- A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`. -/]
def Supports (s : Set α) (b : β) :=
  ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.Supports := Supports
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.Supports := _root_.AddMonoidAction.Supports

variable {s t : Set α} {a : α} {b : β}

@[to_additive]
theorem supports_of_mem (ha : a ∈ s) : Supports G s a := fun _ h => h ha

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.supports_of_mem := supports_of_mem
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.supports_of_mem := _root_.AddMonoidAction.supports_of_mem

variable {G}

@[to_additive]
theorem Supports.mono (h : s ⊆ t) (hs : Supports G s b) : Supports G t b := fun _ hg =>
  (hs _) fun _ ha => hg <| h ha

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.Supports.mono := Supports.mono
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.Supports.mono := _root_.AddMonoidAction.Supports.mono

end SMul

variable [Group H] [SMul G α] [SMul G β] [MonoidAction H α] [SMul H β] [SMulCommClass G H β]
  [SMulCommClass G H α] {s : Set α} {b : β}

-- TODO: This should work without `SMulCommClass`
@[to_additive]
theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) := by
  rintro g' hg'
  rw [smul_comm, h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.Supports.smul := Supports.smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.Supports.vadd := _root_.AddMonoidAction.Supports.vadd

end MonoidAction
