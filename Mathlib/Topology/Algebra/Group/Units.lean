/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, David Ledvinka
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Monoid

/-!
# Topological properties of units

This file contains lemmas about the topology of units in topological monoids,
including results about submonoid units and units of product spaces.
-/

@[expose] public section

open Units

/-- If a submonoid is open in a topological monoid, then its units form an open subset
of the units of the monoid. -/
@[to_additive /-- If a submonoid is open in a topological additive monoid,
then its additive units form an open subset of the additive units of the monoid. -/]
lemma Submonoid.isOpen_units {M : Type*} [TopologicalSpace M] [Monoid M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

/-- The isomorphism of topological groups between the units of a product and
the product of the units. -/
@[to_additive /-- The isomorphism of topological additive groups between the additive units of a
product and the product of the additive units. -/]
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := continuous_pi fun _ ↦ Units.continuous_iff.mpr
    ⟨continuous_apply _ |>.comp Units.continuous_val,
      continuous_apply _ |>.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr
    ⟨continuous_pi fun _ ↦ Units.continuous_val.comp <| continuous_apply _,
      continuous_pi fun _ ↦ Units.continuous_coe_inv.comp <| continuous_apply _⟩

namespace Units

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Monoid M] [Monoid N]

/-- Any `ContinuousMulEquiv` induces a `ContinuousMulEquiv` on units. -/
@[simps! apply]
def mapContinuousMulEquiv (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  { __ := Units.mapEquiv f
    continuous_toFun := f.continuous.units_map _
    continuous_invFun := f.symm.continuous.units_map _ }

@[simp]
theorem symm_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f).symm = mapContinuousMulEquiv f.symm := rfl

@[simp]
theorem toMulEquiv_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f : Mˣ ≃* Nˣ) = mapEquiv f := rfl

end Units
