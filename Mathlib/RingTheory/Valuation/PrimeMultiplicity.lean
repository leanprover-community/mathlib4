/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes
-/
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Valuation.Basic

/-!
# `multiplicity` of a prime in an integral domain as an additive valuation
-/

variable {R : Type*} [CommRing R] [IsDomain R] {p : R} [DecidableRel (Dvd.dvd : R → R → Prop)]

/-- `multiplicity` of a prime in an integral domain as an additive valuation to `PartENat`. -/
noncomputable def multiplicity.addValuation (hp : Prime p) : AddValuation R PartENat :=
  AddValuation.of (multiplicity p) (multiplicity.zero _) (one_right hp.not_unit)
    (fun _ _ => min_le_multiplicity_add) fun _ _ => multiplicity.mul hp
#align multiplicity.add_valuation multiplicity.addValuation

@[simp]
theorem multiplicity.addValuation_apply {hp : Prime p} {r : R} :
    addValuation hp r = multiplicity p r :=
  rfl
#align multiplicity.add_valuation_apply multiplicity.addValuation_apply
