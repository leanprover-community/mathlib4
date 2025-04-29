/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-! # (Nonarchimedean) Local Fields

In this file we define the class `NALocalField` on a field `K`, by extending `Valued K Γ` (for a
linearly ordered commutative group `Γ`), by requiring that it is
* complete (with respect to the uniform structure induced by the valuation);
* that the valuation is discrete (so, in particular, `Γˣ` is cyclic and non-trivial); and
* that the residue field of its unit ball is finite.
It corresponds to the classical notion of (nonarchimedean) local field as developed, for instance,
in Serre's book [serre1968] or in the article [serre1967].

## ToDo
* Show that a topological field is a nonarchimedean local fields if and only if it is complete,
  locally compact and endowed with a non-archimedean norm.
* Study extensions of `NALocalFields` and show that every finite extension of a
  `NALocalField` is again a `NALocalField`.

## Implementation details
* The instance of `NALocalField` on any finite extensions of a local field cannot be
  synthesized, because the base field cannot be found by type-class inference. On the other hand,
  it is possible to define such an instance on every (finite) intermediate extension inside `L/K`
  under the assumption that `K` be a valued local field and `L/K` be separable.

### Remark:
For discussions about this design, see
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Finite.20extensions.20of.20Q_p

## tags:
local fields, nonarchimedean valuation

-/

open Valuation

variable (Γ : outParam Type*) [LinearOrderedCommGroupWithZero Γ] [IsCyclic Γˣ] [Nontrivial Γˣ]

/-- A `NALocalField` is a complete, discretely-valued field with finite residue field. It
corresponds to the classical notion of nonarchimedean local field as developed, for instance, in
Serre's book [serre1968] or in [serre1967]. -/
class NALocalField (K : Type*) [Field K] extends Valued K Γ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete <| Valued.v (R := K)
  finiteResidueField : Finite <| IsLocalRing.ResidueField (Valued.v (R := K)).valuationSubring

variable (K : Type*) [Field K] [NALocalField Γ K]

instance : IsDiscrete <| Valued.v (R := K) := NALocalField.isDiscrete

instance : CompleteSpace K := NALocalField.complete

instance : Finite <| IsLocalRing.ResidueField (Valued.v (R := K)).valuationSubring :=
  NALocalField.finiteResidueField
