/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
The `OfScientific` instance for any characteristic zero field
is well-behaved with respect to the field operations.

It's probably possible, by adjusting the `OfScientific` instances,
to make this more general, but it's not needed at present.
-/

@[expose] public section

open Lean.Grind in
instance {K : Type*} [_root_.Field K] [CharZero K] : LawfulOfScientific K where
  ofScientific_def {m s e} := by
    rw [← NNRat.cast_ofScientific, NNRatCast.toOfScientific_def]
    simp only [LawfulOfScientific.ofScientific_def]
    split
    · norm_cast
      simp
    · norm_cast
