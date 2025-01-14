/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Infinite sums of ENNReal and Set.encard

This file provides lemmas relating sums of constants to the cardinality of the domain of these sums.

## TODO

+ Once we have a topology on `ENat`, provide an `ENat` valued version
+ Once we replace `PartENat` entirely with `ENat` (and replace `PartENat.card` with a `ENat.card`),
  provide versions which sum over the whole type.
-/

open Set Function

variable {α : Type*} (s : Set α)

namespace ENNReal

@[simp]
lemma tsum_set_one_eq : ∑' (_ : s), (1 : ℝ≥0∞) = s.encard := by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero, encard_eq_top hinf, ENat.toENNReal_top]

@[simp]
lemma tsum_set_const_eq (c : ℝ≥0∞) : ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
  nth_rw 1 [← one_mul c]
  rw [ENNReal.tsum_mul_right,tsum_set_one_eq]

end ENNReal
