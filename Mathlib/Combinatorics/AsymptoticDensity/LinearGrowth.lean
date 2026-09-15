/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.Asymptotics.LinearGrowth
public import Mathlib.Combinatorics.AsymptoticDensity

/-!
# Asymptotic density and linear growth

For a set of natural numbers, its lower and upper natural densities are the lower and upper linear
growth of its counting function. This module provides the exact bridge while keeping the
extended-real growth API out of the core asymptotic-density module's imports.

The exponential-growth API in `Mathlib.Analysis.Asymptotics.ExpGrowth` instead studies the
normalization `log (u n) / n`, so it is related infrastructure but does not directly express natural
density.

## Main results

* `Set.lowerDensity_eq_linearGrowthInf` identifies lower natural density with lower linear growth.
* `Set.upperDensity_eq_linearGrowthSup` identifies upper natural density with upper linear growth.
-/

@[expose] public section

open Finset

namespace Set

open scoped Classical in
/-- Lower natural density is the lower linear growth of the counting function. -/
theorem lowerDensity_eq_linearGrowthInf (S : Set ℕ) :
    S.lowerDensity =
      LinearGrowth.linearGrowthInf (fun n : ℕ ↦ (#{x ∈ Finset.range n | x ∈ S} : ℝ)) := by
  rw [lowerDensity, LinearGrowth.linearGrowthInf]
  congr 1
  funext n
  rw [partialDensity_nat_univ]

open scoped Classical in
/-- Upper natural density is the upper linear growth of the counting function. -/
theorem upperDensity_eq_linearGrowthSup (S : Set ℕ) :
    S.upperDensity =
      LinearGrowth.linearGrowthSup (fun n : ℕ ↦ (#{x ∈ Finset.range n | x ∈ S} : ℝ)) := by
  rw [upperDensity, LinearGrowth.linearGrowthSup]
  congr 1
  funext n
  rw [partialDensity_nat_univ]

end Set
