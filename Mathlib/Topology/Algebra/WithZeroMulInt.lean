/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# Topology on `ℤₘ₀`

We show that the map `ℤₘ₀ →*₀ ℝ≥0`, `n ↦ e ^ n` is continuous when `1 < e`.

-/

open Multiplicative Filter NNReal WithZeroTopology

lemma WithZeroMulInt.continuous_toNNReal {e : ℝ≥0} (he : 1 < e) :
    Continuous (toNNReal (ne_zero_of_lt he)) := by
  apply WithZeroTopology.continuous
  rw [map_zero, ← OrderMonoidIso.unitsWithZero.toOrderIso.symm.map_atBot,
    (show atBot = atBot.map ofAdd from rfl), ← Filter.map_neg_atTop, ← Nat.map_cast_int_atTop]
  simp_rw [Filter.tendsto_map'_iff]
  convert (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (inv_lt_one_iff₀.mpr (.inr he)))
  ext
  simp [toNNReal]
