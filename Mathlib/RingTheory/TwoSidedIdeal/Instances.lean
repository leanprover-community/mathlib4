/-
Copyright (c) 2024 euprunin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: euprunin
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Additional instances for two-sided ideals.
-/

@[expose] public section
instance {R} [NonUnitalNonAssocRing R] : NonUnitalSubringClass (TwoSidedIdeal R) R where
  mul_mem _ hb := TwoSidedIdeal.mul_mem_left _ _ _ hb
