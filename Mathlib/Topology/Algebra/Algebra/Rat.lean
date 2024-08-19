/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Topology.Algebra.Monoid

/-!
# Topological (sub)algebras over `Rat`

## Results

This is just a minimal stub for now!

-/

section DivisionRing

/-- The action induced by `algebraRat` is continuous. -/
instance DivisionRing.continuousConstSMul_rat {A} [DivisionRing A] [TopologicalSpace A]
    [ContinuousMul A] [CharZero A] : ContinuousConstSMul ℚ A :=
  ⟨fun r => by simpa only [Algebra.smul_def] using continuous_const.mul continuous_id⟩

end DivisionRing
