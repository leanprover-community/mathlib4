/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Finsupp.Defs

/-!
# Lifts a `Finsupp` from an underlying type to a `Finsupp` on a quotient
-/

@[expose] public section

noncomputable section

open Finset Function

variable {α β : Type*}

namespace Quot

variable {r : α → α → Prop} [Zero β] (f : α →₀ β) (h : ∀ a b, r a b → f a = f b)

/-- Lift a function `α →₀ β` to `Quot r →₀ β`. -/
protected def liftFinsupp : Quot r →₀ β := by
  classical
  refine ⟨image (mk r) f.support, Quot.lift f h, fun a => ⟨?_, ?_⟩⟩
  · rw [mem_image]; rintro ⟨b, hb, rfl⟩; exact Finsupp.mem_support_iff.mp hb
  · induction a using Quot.ind
    rw [lift_mk _ h]
    exact fun hb => mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hb)

@[simp]
theorem liftFinsupp_mk (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl

end Quot

namespace Quotient

variable {s : Setoid α} [Zero β] (f : α →₀ β) (h : ∀ a b, s a b → f a = f b)

/-- Lift a function `α →₀ β` to `Quot r →₀ β`. -/
protected def liftFinsupp : Quotient s →₀ β :=
  Quot.liftFinsupp f h

@[simp]
theorem liftFinsupp_mk (a : α) : Quotient.liftFinsupp f h ⟦a⟧ = f a :=
  rfl

end Quotient
