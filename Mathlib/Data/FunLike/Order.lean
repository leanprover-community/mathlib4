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

section LE

variable (F) in
/-- A mixin typeclass saying that the order on bundled morphisms
agrees with the pointwise order on corresponding functions. -/
class PointwiseLE [∀ a, LE (β a)] [LE F] : Prop where
  le_iff : ∀ {f g : F}, f ≤ g ↔ ∀ a, f a ≤ g a := by intro; rfl

variable [∀ a, LE (β a)] [LE F] [PointwiseLE F] {f g : F}

theorem le_def : f ≤ g ↔ ∀ a, f a ≤ g a := PointwiseLE.le_iff

@[simp, norm_cast] theorem coe_le_coe : coe f ≤ g ↔ f ≤ g := le_def.symm

@[gcongr] theorem apply_mono (h : f ≤ g) (x : α) : f x ≤ g x := le_def.1 h x

end LE

theorem lt_def [∀ a, Preorder (β a)] [Preorder F] [PointwiseLE F] {f g : F} :
    f < g ↔ f ≤ g ∧ ∃ a, f a < g a := by
  rw [← coe_le_coe, ← Pi.lt_def]
  exact lt_iff_lt_of_le_iff_le' coe_le_coe.symm coe_le_coe.symm

instance (priority := 100) instPartialOrder [∀ a, PartialOrder (β a)] [Preorder F]
    [PointwiseLE F] : PartialOrder F where
  le_antisymm _a _b hab hba := coe_injective <| le_antisymm (mod_cast hab) (mod_cast hba)

end DFunLike
