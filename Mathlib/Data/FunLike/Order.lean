/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.FunLike.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.GCongr.Core

/-!
# Preorder and partial order on bundled homs

In this file we define `LE`, `Preorder`, and `PartialOrder` instances
on any type with `DFunLike` instance and appropriate instances on the codomains.
-/

namespace DFunLike

variable {F : Type*} {α : Type*} {β : α → Type*} [DFunLike F α β]

instance instLE [∀ a, LE (β a)] : LE F where
  le f g := coe f ≤ coe g

@[simp, norm_cast] theorem coe_le [∀ a, LE (β a)] {f g : F} : coe f ≤ g ↔ f ≤ g := .rfl
theorem le_def [∀ a, LE (β a)] {f g : F} : f ≤ g ↔ ∀ a, f a ≤ g a := .rfl

instance instPreorder [∀ a, Preorder (β a)] : Preorder F := .lift coe

theorem lt_def [∀ a, Preorder (β a)] {f g : F} : f < g ↔ f ≤ g ∧ ∃ a, f a < g a := Pi.lt_def

instance instPartialOrder [∀ a, PartialOrder (β a)] : PartialOrder F := .lift coe coe_injective

@[gcongr] theorem apply_mono [∀ a, Preorder (β a)] {f g : F} (h : f ≤ g) (x : α) : f x ≤ g x := h x

end DFunLike
