/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap
import Std.Data.RBMap

/-!
# Additional API for `HashMap` and `RBSet`.

These should be replaced by proper implementations in Std.
-/

namespace Std.HashMap

variable [BEq α] [Hashable α]

/-- The list of keys in a `HashMap`. -/
def keys (m : HashMap α β) : List α :=
  m.fold (fun ks k _ => k :: ks) []

/-- The list of values in a `HashMap`. -/
def values (m : HashMap α β) : List β :=
  m.fold (fun vs _ v => v :: vs) []

/-- Add a value to a `HashMap α (List β)` viewed as a multimap. -/
def consVal (self : HashMap α (List β)) (a : α) (b : β) : HashMap α (List β) :=
  match self.find? a with
  | none => self.insert a [b]
  | some L => self.insert a (b::L)

end Std.HashMap

namespace Std.RBSet

/-- Insert all elements of a list into an `RBSet`. -/
def insertList {cmp} (m : RBSet α cmp) (L : List α) : RBSet α cmp :=
  L.foldl (fun m a => m.insert a) m

end Std.RBSet
