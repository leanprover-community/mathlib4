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

variable {R : Type*} [CommRing R] [IsDomain R] {p : R}

/-- `multiplicity` of a prime in an integral domain as an additive valuation to `ℕ∞`. -/
noncomputable def multiplicity_addValuation (hp : Prime p) : AddValuation R ℕ∞ :=
  AddValuation.of (emultiplicity p) (emultiplicity_zero _) (emultiplicity_of_one_right hp.not_unit)
    (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[simp]
theorem multiplicity_addValuation_apply {hp : Prime p} {r : R} :
    multiplicity_addValuation hp r = emultiplicity p r :=
  rfl
