/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Sign
import Mathlib.Topology.Order.Basic

/-!
# Topology on `SignType`

This file gives `SignType` the discrete topology, and proves continuity results for `SignType.sign`
in an `OrderTopology`.

## TODO

- Prove `OrderTopology SignType`.
-/


instance : TopologicalSpace SignType := ⊥
instance : DiscreteTopology SignType := ⟨rfl⟩

variable {α : Type*} [Zero α] [TopologicalSpace α] [LinearOrder α] [OrderTopology α] {a : α}

@[fun_prop]
theorem continuousAt_sign (h : a ≠ 0) : ContinuousAt SignType.sign a := by
  rcases h.lt_or_lt with h_neg | h_pos
  · refine (continuousAt_const (y := -1)).congr ?_
    exact (eventually_lt_nhds h_neg).mono fun x hx ↦ (sign_neg hx).symm
  · refine (continuousAt_const (y := 1)).congr ?_
    exact (eventually_gt_nhds h_pos).mono fun x hx ↦ (sign_pos hx).symm

@[deprecated continuousAt_sign (since := "2024-11-09")]
theorem continuousAt_sign_of_pos (h : 0 < a) : ContinuousAt SignType.sign a :=
  continuousAt_sign h.ne'

@[deprecated continuousAt_sign (since := "2024-11-09")]
theorem continuousAt_sign_of_neg (h : a < 0) : ContinuousAt SignType.sign a :=
  continuousAt_sign h.ne

@[deprecated (since := "2024-11-09")] alias continuousAt_sign_of_ne_zero := continuousAt_sign
