/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Instance `IsReduced R[X]`
A polynomial `p : R[X]` over a commutative ring `R` is reduced if `R` is reduced.
-/

open Polynomial

public instance {R : Type*} [CommRing R] [IsReduced R] : IsReduced R[X] := by
  rw [isReduced_iff]
  intro p hp
  ext i
  rw [Polynomial.isNilpotent_iff] at hp
  simpa using hp i
