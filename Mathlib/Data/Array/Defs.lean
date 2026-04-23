/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule

/-!
# Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions.
-/

deprecated_module (since := "2026-03-05")

@[expose] public section

namespace Array

universe u
variable {α : Type u}

/-- Permute the array using a sequence of indices defining a cyclic permutation.
  If the list of indices `l = [i₁, i₂, ..., iₙ]` are all distinct then
  `(cyclicPermute! a l)[iₖ₊₁] = a[iₖ]` and `(cyclicPermute! a l)[i₀] = a[iₙ]` -/
@[deprecated "This is now in `Mathlib.Tactic.Translate.Reorder.permute!`" (since := "2026-03-05")]
def cyclicPermute! [Inhabited α] : Array α → List Nat → Array α
  | a, [] => a
  | a, i :: is => cyclicPermuteAux a is a[i]! i
where cyclicPermuteAux : Array α → List Nat → α → Nat → Array α
| a, [], x, i0 => a.set! i0 x
| a, i :: is, x, i0 =>
  let (y, a) := a.swapAt! i x
  cyclicPermuteAux a is y i0

set_option linter.deprecated false

/-- Permute the array using a list of cycles. -/
@[deprecated "This is now in `Mathlib.Tactic.Translate.Reorder.permute!`" (since := "2026-03-05")]
def permute! [Inhabited α] (a : Array α) (ls : List (List Nat)) : Array α :=
ls.foldl (init := a) (·.cyclicPermute! ·)

end Array
