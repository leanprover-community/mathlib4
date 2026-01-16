/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# The `ContinuumHypothesis` typeclass

We make this a typeclass rather than an axiom so that it is immediately obvious when a theorem
assumes this hypothesis.

In mathlib, we show consequences of the continuum hpyothesis with `[ContinuumHypothesis]` in
assumptions.
If in downstream projects you want to assume this as an axiom, you can write
```
@[instance] axiom continuumHypothesis : ContinuumHypothesis
```
-/

open scoped Cardinal

/-- The statement that the continuum hypothesis holds.

To avoid a universe parameter, we only state that this holds in universe `0`, since it can be lifted
to other universes with subsequent theorems.

See `ContinuumHypothesis.iff_aleph0_covby_continuum` and
`ContinuumHypothesis.iff_continuum_eq_aleph_one` for typical characterizations.
-/
class ContinuumHypothesis where
  /-- See `ContinuumHypothesis.of_continuum_eq_aleph_one'` for the universe-generic version. -/
  of_continuum_eq_aleph_one' ::
    /-- See `ContinuumHypothesis.continuum_eq_aleph_one` for the universe-generic version. -/
    continuum_eq_aleph_one' : (𝔠 : Cardinal.{0}) = ℵ₁

namespace ContinuumHypothesis

/-- See `ContinuumHypothesis.iff_continuum_eq_aleph_one` for the universe-generic version. -/
theorem iff_continuum_eq_aleph_one' : ContinuumHypothesis ↔ (𝔠 : Cardinal.{0}) = ℵ₁ :=
  ⟨(·.continuum_eq_aleph_one'), .of_continuum_eq_aleph_one'⟩

section basic_constructors

theorem iff_continuum_eq_aleph_one.{u} : ContinuumHypothesis ↔ (𝔠 : Cardinal.{u}) = ℵ₁ := by
  rw [iff_continuum_eq_aleph_one', ← Cardinal.lift_continuum.{u, 0}, Cardinal.lift_eq_aleph_one]

theorem continuum_eq_aleph_one.{u} [ContinuumHypothesis] : (𝔠 : Cardinal.{u}) = ℵ₁ :=
  iff_continuum_eq_aleph_one.1 ‹_›

alias ⟨_, of_continuum_eq_aleph_one⟩ := iff_continuum_eq_aleph_one

theorem iff_aleph0_covby_continuum : ContinuumHypothesis ↔ ℵ₀ ⋖ 𝔠 := by
  rw [← Order.succ_eq_iff_covBy, Cardinal.succ_aleph0, eq_comm, iff_continuum_eq_aleph_one]

theorem aleph0_covby_continuum.{u} [ContinuumHypothesis] : ℵ₀ ⋖ (𝔠 : Cardinal.{u}) :=
  iff_aleph0_covby_continuum.1 ‹_›

alias ⟨_, of_aleph0_covby_continuum⟩ := iff_aleph0_covby_continuum

end basic_constructors

end ContinuumHypothesis
