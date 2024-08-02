/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Topology on power series

In this file we define the possible topologies on the ring of power series.

-/

namespace PowerSeries

open Filter Function

variable (R : Type*)

section Topological

variable [TopologicalSpace R]

namespace WithPiTopology

/-- The pointwise topology on `PowerSeries`. -/
scoped instance : TopologicalSpace (PowerSeries R) := Pi.topologicalSpace

variable [Semiring R]

/-- `coeff` are continuous. -/
theorem continuous_coeff (d : ℕ) : Continuous (PowerSeries.coeff R d) :=
  continuous_pi_iff.mp continuous_id (Finsupp.single () d)

/-- `constant_coeff` is continuous. -/
theorem continuous_constantCoeff : Continuous (constantCoeff R) :=
  coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0

/-- A family of power series converges iff it converges coefficientwise. -/
theorem tendsto_iff_coeff_tendsto {ι : Type*} (f : ι → PowerSeries R) (u : Filter ι)
    (g : PowerSeries R) : Tendsto f u (nhds g) ↔
    ∀ d : ℕ, Tendsto (fun i => coeff R d (f i)) u (nhds (coeff R d g)) := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.LinearEquiv.finsuppUnique_apply,
    PUnit.default_eq_unit, coeff]
  apply iff_of_eq
  congr; ext i; congr;
  all_goals { ext; simp }

/-- The semiring topology on `PowerSeries` of a topological semiring. -/
@[scoped instance]
theorem instTopologicalSemiring [Semiring R] [TopologicalSemiring R] :
    TopologicalSemiring (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instTopologicalSemiring Unit R

/-- The ring topology on `PowerSeries` of a topological ring. -/
@[scoped instance]
theorem instTopologicalRing [Ring R] [TopologicalRing R] :
    TopologicalRing (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instTopologicalRing Unit R

/-- `PowerSeries` on a `T2Space` form a `T2Space`. -/
@[scoped instance]
theorem instT2Space [T2Space R] : T2Space (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instT2Space Unit R

end WithPiTopology

end Topological

section Uniform

namespace WithPiUniformity

open WithPiTopology

variable [UniformSpace R]

/-- The componentwise uniformity on `PowerSeries`. -/
scoped instance : UniformSpace (PowerSeries R) :=
  MvPowerSeries.WithPiUniformity.instUniformSpace Unit R

/-- Coefficients are uniformly continuous. -/
theorem uniformContinuous_coeff [Semiring R] (d : ℕ) :
    UniformContinuous fun f : PowerSeries R ↦ coeff R d f :=
  uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)

variable [Ring R]

/-- The `UniformAddGroup` structure on `PowerSeries` of a `UniformAddGroup`. -/
@[scoped instance]
theorem instUniformAddGroup [UniformAddGroup R] :
    UniformAddGroup (PowerSeries R) :=
  MvPowerSeries.WithPiUniformity.instUniformAddGroup Unit R

/-- Completeness of the uniform structure on `PowerSeries`. -/
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (PowerSeries R) :=
  MvPowerSeries.WithPiUniformity.instCompleteSpace Unit R

/-- Separation of the uniform structure on `PowerSeries`. -/
@[scoped instance]
theorem instT0Space [T0Space R] : T0Space (PowerSeries R) :=
  MvPowerSeries.WithPiUniformity.instT0Space Unit R

/-- The topological ring structure on `PowerSeries`. -/
@[scoped instance]
theorem instTopologicalRing [UniformAddGroup R] [TopologicalRing R] :
    TopologicalRing (PowerSeries R) :=
  MvPowerSeries.WithPiUniformity.instTopologicalRing Unit R

end WithPiUniformity

end Uniform

section

variable {R}

variable [TopologicalSpace R]

open WithPiTopology WithPiUniformity

theorem continuous_C [Ring R] [TopologicalRing R] : Continuous (C R) := MvPowerSeries.continuous_C

theorem tendsto_pow_zero_of_constantCoeff_nilpotent [CommSemiring R]
    {f : PowerSeries R} (hf : IsNilpotent (constantCoeff R f)) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.tendsto_pow_zero_of_constantCoeff_nilpotent hf

theorem tendsto_pow_zero_of_constantCoeff_zero [CommSemiring R]
    {f : PowerSeries R} (hf : constantCoeff R f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.tendsto_pow_zero_of_constantCoeff_zero hf

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [CommRing R] [DiscreteTopology R]
    (f : PowerSeries R) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff R f) :=
  MvPowerSeries.tendsto_pow_of_constantCoeff_nilpotent_iff f

end

section Summable

variable [Semiring R] [TopologicalSpace R]

open WithPiTopology MvPowerSeries.WithPiTopology

variable {R}

-- NOTE : one needs an API to apply `Finsupp.LinearEquiv.finsuppUnique`
/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : PowerSeries R) :
    HasSum (fun d : ℕ => monomial R d (coeff R d f)) f := by
  rw [← (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.hasSum_iff]
  convert MvPowerSeries.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff,
    Finsupp.LinearEquiv.finsuppUnique_apply, PUnit.default_eq_unit]
  congr
  all_goals { ext; simp }

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space R] (f : PowerSeries R) :
    f = tsum fun d : ℕ => monomial R d (coeff R d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm

end Summable

end PowerSeries
