/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Topology

/-! # Evaluation of power series

-/
namespace PowerSeries

variable {R : Type*} [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S][TopologicalRing S]
  [T2Space S] [CompleteSpace S]

/-- Families at which power series can be evaluated -/
structure EvalDomain (a : S) : Prop where
  hpow : IsTopologicallyNilpotent a

open WithPiUniformity

/-- The domain of evaluation of `PowerSeries`, as an ideal -/
def EvalDomain.ideal [LinearTopology S] : Ideal S where
  carrier   := setOf IsTopologicallyNilpotent
  add_mem'  := IsTopologicallyNilpotent.add
  zero_mem' := IsTopologicallyNilpotent.zero
  smul_mem' := IsTopologicallyNilpotent.mul_left

variable {φ : R →+* S} (hφ : Continuous φ) (a : S)

/-- Evaluation of power series at adequate elements -/
noncomputable def eval₂ : PowerSeries R → S :=
  MvPowerSeries.eval₂ φ (fun _ ↦ a)

variable [hS : LinearTopology S] {a : S} (ha : EvalDomain a)

theorem EvalDomain.const : MvPowerSeries.EvalDomain (fun (_ : Unit) ↦ a) where
  hpow := fun _ ↦ ha.hpow
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- For `EvalDomain a`, the evaluation homomorphism at `a` on `PowerSeries` -/
noncomputable def eval₂Hom : PowerSeries R →+* S :=
  MvPowerSeries.eval₂Hom hφ ha.const

variable [Algebra R S] [ContinuousSMul R S]

/-- For `EvalDomain a`, the evaluation homomorphism at `a` on `PowerSeries`,
as an `AlgHom` -/
noncomputable def aeval : PowerSeries R →ₐ[R] S :=
  MvPowerSeries.aeval ha.const

end PowerSeries
