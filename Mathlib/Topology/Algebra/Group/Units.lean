/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, David Ledvinka
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Topological properties of units

This file contains lemmas about the topology of units in topological monoids,
including results about submonoid units and units of product spaces.
-/

open Units

/-- If a submonoid is open in a topological monoid, then its units form an open subset
of the units of the monoid. -/
@[to_additive]
lemma Submonoid.isOpen_units {M : Type*} [TopologicalSpace M] [Monoid M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

/-- The monoid homeomorphism between the units of a product of topological monoids
and the product of the units of the monoids. -/
@[to_additive /-- The additive monoid homeomorphism between the additive units of a product of
topological additive monoids and the product of the additive units of the monoids. -/]
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
    refine continuous_pi (fun i => ?_)
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · simp only [Function.comp_def, MulEquiv.val_piUnits_apply]
      exact (continuous_apply i).comp' Units.continuous_val
    · simp only [MulEquiv.val_inv_piUnits_apply, Units.inv_eq_val_inv]
      exact (continuous_apply i).comp' Units.continuous_coe_inv
  continuous_invFun := by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm]
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_pi (fun i => ?_)
      simp only [Function.comp_def, MulEquiv.val_piUnits_symm_apply]
      exact Units.continuous_val.comp' (continuous_apply i)
    · refine continuous_pi (fun i => ?_)
      simp only [MulEquiv.val_inv_piUnits_symm_apply, Units.inv_eq_val_inv]
      exact Units.continuous_coe_inv.comp' (continuous_apply i)
