/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Mathlib.Init
import Mathlib.Tactic.TypeStar
import Batteries.Data.HashMap.Basic
import Batteries.Data.RBMap.Basic

/-!
# Additional API for `HashMap` and `RBSet`.

As `HashMap` has been completely reimplemented in `Batteries`,
nothing from the mathlib3 file `data.hash_map` is reflected here.
The porting header is just here to mark that no further work on `data.hash_map` is desired.
-/

variable {α β : Type*}

namespace Batteries.HashMap

-- not an exact match, the Lean3 version was dependently-typed

variable [BEq α] [Hashable α]

/-- The list of keys in a `HashMap`. -/
@[deprecated "This declaration is unused in Mathlib: if you need it, \
  please file an issue in the Batteries repository." (since := "2024-06-12")]
def keys (m : HashMap α β) : List α :=
  m.fold (fun ks k _ => k :: ks) []

/-- The list of values in a `HashMap`. -/
@[deprecated "This declaration is unused in Mathlib: if you need it, \
  please file an issue in the Batteries repository." (since := "2024-06-12")]
def values (m : HashMap α β) : List β :=
  m.fold (fun vs _ v => v :: vs) []

/-- Add a value to a `HashMap α (List β)` viewed as a multimap. -/
@[deprecated "This declaration is unused in Mathlib: if you need it, \
  please file an issue in the Batteries repository." (since := "2024-06-12")]
def consVal (self : HashMap α (List β)) (a : α) (b : β) : HashMap α (List β) :=
  match self.find? a with
  | none => self.insert a [b]
  | some L => self.insert a (b::L)

end Batteries.HashMap

namespace Batteries.RBSet

/-- Insert all elements of a list into an `RBSet`. -/
@[deprecated "This declaration is unused in Mathlib: if you need it, \
  please file an issue in the Batteries repository." (since := "2024-06-12")]
def insertList {cmp} (m : RBSet α cmp) (L : List α) : RBSet α cmp :=
  L.foldl (fun m a => m.insert a) m

end Batteries.RBSet
