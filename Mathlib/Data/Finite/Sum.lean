/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Sum

/-!
# Finiteness of sum types
-/

variable {α β : Type*}

namespace Finite

instance [Finite α] [Finite β] : Finite (α ⊕ β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

theorem sum_left (β) [Finite (α ⊕ β)] : Finite α :=
  of_injective (Sum.inl : α → α ⊕ β) Sum.inl_injective

theorem sum_right (α) [Finite (α ⊕ β)] : Finite β :=
  of_injective (Sum.inr : β → α ⊕ β) Sum.inr_injective

end Finite
