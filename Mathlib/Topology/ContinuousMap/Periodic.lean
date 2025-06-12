/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Sums of translates of a continuous function is a period continuous function.

-/
assert_not_exists StoneCech StarModule

namespace ContinuousMap

section Periodicity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Summing translates of a function -/

/-- Summing the translates of `f` by `ℤ • p` gives a map which is periodic with period `p`.
(This is true without any convergence conditions, since if the sum doesn't converge it is taken to
be the zero map, which is periodic.) -/
theorem periodic_tsum_comp_add_zsmul [AddCommGroup X] [ContinuousAdd X] [AddCommMonoid Y]
    [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) :
    Function.Periodic (⇑(∑' n : ℤ, f.comp (ContinuousMap.addRight (n • p)))) p := by
  intro x
  by_cases h : Summable fun n : ℤ => f.comp (ContinuousMap.addRight (n • p))
  · convert congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : ℤ)).tsum_eq _) using 1
    -- Porting note: in mathlib3 the proof from here was:
    -- simp_rw [← tsum_apply h, ← tsum_apply ((equiv.add_right (1 : ℤ)).summable_iff.mpr h),
    --   equiv.coe_add_right, comp_apply, coe_add_right, add_one_zsmul, add_comm (_ • p) p,
    --   ← add_assoc]
    -- However now the second `← tsum_apply` doesn't fire unless we use `erw`.
    simp_rw [← tsum_apply h]
    erw [← tsum_apply ((Equiv.addRight (1 : ℤ)).summable_iff.mpr h)]
    simp [coe_addRight, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]

end Periodicity

end ContinuousMap
