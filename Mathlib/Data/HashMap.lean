/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.hash_map
! leanprover-community/mathlib commit 2220b0cbab795e73674b8191170b0cc68c6b54a8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.

As `HashMap` has been completely reimplemented in `Std`,
nothing from the mathlib3 file `data.hash_map` is reflected here.
The porting header is just here to mark that no further work on `data.hash_map` is desired.
-/
import Mathlib.Init.Align
import Std.Data.HashMap
import Std.Data.RBMap

/-!
# Additional API for `HashMap` and `RBSet`.

These should be replaced by proper implementations in Std.
-/

namespace Std.HashMap

-- not an exact match, the Lean3 version was dependently-typed
#align hash_map Std.HashMapₓ

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
