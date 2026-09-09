/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.Topology.Algebra.ValuativeRel.LinearTopology

/-!
# The topologies on `ℚ_[p]` and `ℤ_[p]` are `ℤ_[p]`-linear

The topology on `ℚ_[p]` comes from its valuative relation (see
`Mathlib/NumberTheory/Padics/ValuativeRel.lean`), and `ℤ_[p]` is its ring of integers, so the
balls `{x | v x < γ}` are `ℤ_[p]`-submodules forming a basis of neighborhoods of zero. The same
balls, intersected with `ℤ_[p]`, are ideals of `ℤ_[p]` forming a basis of neighborhoods of zero
of `ℤ_[p]`, which carries the topology induced from `ℚ_[p]`.

## Main results

* `IsLinearTopology ℤ_[p] ℚ_[p]`: the topology on `ℚ_[p]` is `ℤ_[p]`-linear.
* `IsLinearTopology ℤ_[p] ℤ_[p]`: the topology on `ℤ_[p]` is `ℤ_[p]`-linear, i.e. `ℤ_[p]` is a
  linearly topologized ring.

## Tags

p-adic, p adic, padic, valuation, linear topology, linearly topologized
-/

@[expose] public section

open ValuativeRel

variable {p : ℕ} [Fact p.Prime]

instance : IsIntegerSMul ℤ_[p] ℚ_[p] := sorry

-- instance : IsIntegerSMul ℤ_[p] ℤ_[p] := sorry


instance : IsLinearTopology ℤ_[p] ℤ_[p] := sorry

instance : IsLinearTopology ℤ_[p] ℚ_[p] := sorry
