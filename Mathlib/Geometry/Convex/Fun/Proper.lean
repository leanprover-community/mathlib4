/-
Copyright (c) 2026 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
module

public import Mathlib.Order.WithBot

import Mathlib.Data.Set.Basic

/-!
# Proper extended-valued functions

This file defines `Convexity.effectiveDomain` and `Convexity.IsProper`.
The effective domain excludes `⊤` but may contain points where the function takes the value `⊥`.
A proper function never takes the value `⊥` and has nonempty effective domain.
-/

@[expose] public section

open Set

namespace Convexity

variable {α β R : Type*} [PartialOrder β] [OrderTop β]

/-- The effective domain of `f` consists of the points where `f` takes a value less than `⊤`. -/
def effectiveDomain (f : α → β) : Set α := {x | f x < ⊤}

@[simp]
theorem mem_effectiveDomain {f : α → β} {x : α} : x ∈ effectiveDomain f ↔ f x < ⊤ := Iff.rfl

/-- A function is proper if it never takes the value `⊥` and its effective domain is nonempty. -/
@[mk_iff]
structure IsProper [OrderBot β] (f : α → β) : Prop where
  /-- The function is everywhere greater than `⊥`. -/
  bot_lt : ∀ x, ⊥ < f x
  /-- The function takes a value less than `⊤` somewhere. -/
  nonempty_effectiveDomain : (effectiveDomain f).Nonempty

theorem IsProper.ne_bot [OrderBot β] {f : α → β} (hf : IsProper f) (x : α) : f x ≠ ⊥ :=
  (hf.bot_lt x).ne'

@[simp]
theorem effectiveDomain_withBot_coe (g : α → β) :
    effectiveDomain (g · : α → WithBot β) = effectiveDomain g :=
  Set.ext fun _ ↦ WithBot.coe_lt_coe

@[simp]
theorem isProper_withBot_coe_iff {g : α → β} :
    IsProper (g · : α → WithBot β) ↔ (effectiveDomain g).Nonempty := by
  simp [isProper_iff, effectiveDomain_withBot_coe]

variable [PartialOrder R]

@[simp]
theorem effectiveDomain_coe (g : α → R) :
    effectiveDomain (g · : α → WithTop R) = univ := by
  simp [effectiveDomain]

theorem isProper_coe [Nonempty α] (g : α → R) :
    IsProper (g · : α → WithBot (WithTop R)) := by
  simp [isProper_iff]

end Convexity
