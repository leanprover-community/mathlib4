/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: euprunin
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Additional instances for two-sided ideals.
-/
instance {R} [NonUnitalNonAssocRing R] : NonUnitalSubringClass (TwoSidedIdeal R) R where
  mul_mem _ hb := TwoSidedIdeal.mul_mem_left _ _ _ hb
