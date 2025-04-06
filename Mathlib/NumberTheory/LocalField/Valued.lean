/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-! # Valued Local Fields

In this file we define the class `ValuedLocalField` on a valued field `K`, requiring that it is
* complete (with respect to the uniform structure induced by the valuation);
* that the valuation is discrete (so, in particular, it takes values in a linearly ordered
  commutative group with zero `Γ` such that `Γˣ` is cyclic and non-trivial); and
* that the residue field of its unit ball is finite.

## ToDo
* Once a more general definition of `LocalField` enters mathlib, provide instances of `LocalField`
  for every `ValuedLocalField`
* Show that valued local fields are the same thing as nonarchimedean local fields, the latter being
  probably defined as non-trivially normed, locally compact fields whose norm is non-archimedean.
* Study extensions of `ValuedLocalFields` and show that every finite extension of a
  `ValuedLocalField` is again a `ValuedLocalField`.

## Implementation details

### Remark:
For discussions about this design, see
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Finite.20extensions.20of.20Q_p

## tags:
local fields, nonarchimedean valuation

-/

open Valuation

variable (Γ : Type*) [LinearOrderedCommGroupWithZero Γ] [IsCyclic Γˣ] [Nontrivial Γˣ]


class ValuedLocalField (K : Type*) [Field K] extends Valued K Γ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete <| Valued.v (R := K)
  finiteResidueField : Finite <| IsLocalRing.ResidueField (Valued.v (R := K)).valuationSubring
