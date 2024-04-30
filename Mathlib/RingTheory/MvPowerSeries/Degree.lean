/-
Copyright (c) 2024 Alessandro Iraci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, Alessandro Iraci
-/
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Degree on MvPowerSeries

This file defines a degree on MvPowerSeries, with values in WithTop WithBot ℕ.

## Main declarations

* `MvPowerSeries.degree`

-/

open Classical

section Degree

namespace MvPowerSeries


variable {σ R : Type*} [CommSemiring R] [DecidableEq (MvPowerSeries σ R)]

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasDegreeBound (n : WithBot (WithTop ℕ)) : MvPowerSeries σ R → Prop :=
  fun φ ↦ (∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n)

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
  ∃ n, HasDegreeBound n φ

noncomputable def degree (φ : MvPowerSeries σ R) : WithBot (WithTop ℕ) :=
  sInf { n | HasDegreeBound n φ }

end MvPowerSeries

end Degree
