/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-! # (Nonarchimedean) Local Fields

In this file we define the class `Valued.LocalField`, by extending `Valued K Γ`
(for a linearly ordered commutative group `Γ`), by requiring that it is
* complete (with respect to the uniform structure induced by the valuation);
* that the valuation `v` attached to the valued structure is discrete (so, in particular, the range
of `v` is cyclic and non-trivial); and
* that the residue field of the unit ball is finite.
It corresponds to the classical notion of (nonarchimedean) local field as developed, for instance,
in Serre's book [serre1968] or in the article [serre1967].

## ToDo
* Show that a topological field is a nonarchimedean local fields if and only if it is complete,
  locally compact and endowed with a non-archimedean norm.
* Study extensions of `Valued.LocalFields` and show that every finite extension of a
  `NALocalField` is again a `NALocalField`.

## Implementation details
* The reason for chosing to extend `Valued` is to ensure that the valuation is *unique* and is
  compatible with the topology. This could be unbundled to separate the valuation and its
  compatibility with the topology, but at the time of first providing the defintion of local fields
  this approach is not well developed in mathlib.
* The instance of `Valued.LocalField` on any finite extensions of a local field cannot be
  synthesized, because the base field cannot be found by type-class inference. On the other hand,
  it is possible to define such an instance on every (finite) intermediate extension inside `L/K`
  under the assumption that `K` be a valued local field and `L/K` be separable.

### Remarks:
* For discussions about this design, see
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Finite.20extensions.20of.20Q_p
* Part of the above ToDo's are contained in the authors' work
https://github.com/mariainesdff/LocalClassFieldTheory
* Implementing the purely topological, equivalent definition should be accessible by relying on
  #25829

## tags:
local fields, nonarchimedean valuation

-/

namespace Valued

open Valuation MonoidHomWithZero

variable (K : Type*) [Field K] (Γ : outParam Type*) [LinearOrderedCommGroupWithZero Γ]

/-- A `Valued.LocalField` is a complete, discretely-valued field with finite residue field. It
corresponds to the classical notion of nonarchimedean local field as developed, for instance, in
Serre's book [serre1968] or in [serre1967]. -/
class LocalField extends Valued K Γ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete <| Valued.v (R := K)
  finiteResidueField : Finite <| IsLocalRing.ResidueField (Valued.v (R := K)).valuationSubring

variable [LocalField K Γ]

instance : IsDiscrete <| Valued.v (R := K) := LocalField.isDiscrete

instance : CompleteSpace K := LocalField.complete

instance : Finite <| IsLocalRing.ResidueField (Valued.v (R := K)).valuationSubring :=
  LocalField.finiteResidueField

instance : IsCyclic (valueGroup (Valued.v (R := K))) := inferInstance

instance : Nontrivial (valueGroup (Valued.v (R := K))) := inferInstance


end Valued
