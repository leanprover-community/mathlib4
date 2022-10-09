/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap

/-!
# Additional operations on `Std.HashMap`.
-/

open Std

variable [BEq α] [Hashable α] [DecidableEq β]

namespace Std.HashMap

/-- Keep only those key-value pairs `(a, b)` such that `p a`. -/
-- This is the most naive possible implementation, and should be replaced.
def filterKeys (f : HashMap α β) (p : α → Bool) : HashMap α β :=
  .ofList <| f.toList.filter (p ·.1)

/-!
## Algebraic structures on `HashMap`.
-/

/-- Pointwise addition of `HashMap`s. -/
def add [Add β] (f g : HashMap α β) : HashMap α β :=
  f.mergeWith (fun _ b b' => b + b') g

-- Note that we do not get an `[AddMonoid (HashMap α β)]` instance from `[AddMonoid β]`.
-- However we do if we restrict to `HashMap`s with all zero values deleted.
