/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Deprecated.AlgebraClasses
import Mathlib.Order.RelClasses

/-!
# Note about deprecated files

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in
`Mathlib/Deprecated/AlgebraClasses.lean`.

-/

set_option linter.deprecated false

universe u v

variable {α : Type u}

open Function

@[deprecated (since := "2024-07-30")]
theorem IsTotalPreorder.swap (r) [IsTotalPreorder α r] : IsTotalPreorder α (swap r) :=
  { @IsPreorder.swap α r _, @IsTotal.swap α r _ with }

@[deprecated (since := "2024-08-22")] instance [LinearOrder α] : IsTotalPreorder α (· ≤ ·) where
@[deprecated (since := "2024-08-22")] instance [LinearOrder α] : IsTotalPreorder α (· ≥ ·) where

@[deprecated (since := "2024-07-30")]
instance [LinearOrder α] : IsIncompTrans α (· < ·) := by infer_instance
