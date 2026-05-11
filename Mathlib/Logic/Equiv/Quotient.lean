/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences and quotients

In this file we provide facts relating `Equiv` and `Quotient`.
-/

@[expose] public section

open Function Set

variable {α β γ : Type*}

namespace Equiv

@[simps]
protected def quotCongr {r s : α → α → Prop} (eq : r = s) : Quot r ≃ Quot s where
  toFun := Quot.lift (Quot.mk s) (by simp [eq, Quot.congr_mk])
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- If `α` is equivalent to `β`, then `Set α` is equivalent to `Set β`. -/
@[simps]
protected def congr {α β : Type*} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

end Equiv
