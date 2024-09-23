/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Std.Data.HashMap

/-!
# Convenience functions for hash maps

These will be reimplemented in the Lean standard library.
-/

namespace Std.HashMap

variable {α β γ : Type _} [BEq α] [Hashable α]

/-- Apply a function to the values of a hash map. -/
def mapVal (f : α → β → γ) (m : HashMap α β) : HashMap α γ :=
  m.fold (fun acc k v => acc.insert k (f k v)) HashMap.empty

/-- Update or remove a value in a hash map, depending on the current value (or absence thereof). -/
-- This could be implemented more efficiently.
def update (m : HashMap α β) (f : α → Option β → Option β) (k : α) : HashMap α β :=
  match f k m[k]? with
  | some v => m.insert k v
  | none => m.erase k

/--
Combine two hash maps using a function that is applied when a key is present in both hash maps.
-/
@[inline] def mergeWith (f : α → β → β → β) (m₁ m₂ : HashMap α β) : HashMap α β :=
  m₂.fold (init := m₁) fun r k v =>
    r.update (fun k v? => match v? with | some v' => some (f k v' v) | none => some v) k

end Std.HashMap
