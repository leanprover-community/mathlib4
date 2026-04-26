/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas


@[expose] public section

theorem den_sum_dvd_lcm_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ s.lcm (fun i ↦ (f i).den) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    rw [Finset.sum_insert has, Finset.lcm_insert]
    exact (Rat.add_den_dvd_lcm _ _).trans (lcm_dvd_lcm dvd_rfl ih)

theorem den_sum_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den :=
  dvd_trans (den_sum_dvd_lcm_den s f) (s.lcm_dvd_prod (fun i ↦ (f i).den))
