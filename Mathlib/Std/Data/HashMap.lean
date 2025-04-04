/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Std.Data.HashMap.Basic
import Mathlib.Init

/-!
# Convenience functions for hash maps

These will be reimplemented in the Lean standard library.
-/

namespace Std.HashMap

variable {α β γ : Type _} [BEq α] [Hashable α]

/-- Apply a function to the values of a hash map. -/
def mapVal (f : α → β → γ) (m : HashMap α β) : HashMap α γ :=
  m.fold (fun acc k v => acc.insert k (f k v)) ∅

end Std.HashMap
