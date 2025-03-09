/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.PiTopology

/-! # Evaluation of power series

We adapt evaluation of mv power series to the case of power series.

TODO. Unify more precisely; add documentation.

-/
namespace PowerSeries

open WithPiTopology

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

/-- Families at which power series can be evaluated. -/
structure EvalDomain [TopologicalSpace S] (a : S) : Prop where
  hpow : IsTopologicallyNilpotent a

/-- The domain of evaluation of `PowerSeries`, as an ideal. -/
def EvalDomain.ideal [TopologicalSpace S] [IsLinearTopology S S] : Ideal S where
  carrier   := {a | IsTopologicallyNilpotent a}
  add_mem'  := IsTopologicallyNilpotent.add
  zero_mem' := IsTopologicallyNilpotent.zero
  smul_mem' := IsTopologicallyNilpotent.mul_left

variable [UniformSpace R] [UniformSpace S]

variable (φ : R →+* S) (a : S)

/-- Evaluation of power series at adequate elements. -/
noncomputable def eval₂ : PowerSeries R → S :=
  MvPowerSeries.eval₂ φ (fun _ ↦ a)

variable {a}

theorem EvalDomain.const (ha : EvalDomain a) :
    MvPowerSeries.EvalDomain (fun (_ : Unit) ↦ a) where
  hpow := fun _ ↦ ha.hpow
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

variable [IsTopologicalSemiring R] [UniformAddGroup R]
    [UniformAddGroup S] [T2Space S] [CompleteSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]

/-- For `EvalDomain a`, the evaluation homomorphism at `a` on `PowerSeries`. -/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : EvalDomain a) :
    PowerSeries R →+* S :=
  MvPowerSeries.eval₂Hom hφ ha.const

variable [Algebra R S] [ContinuousSMul R S]

/-- For `EvalDomain a`, the evaluation homomorphism at `a` on `PowerSeries`, as an `AlgHom`. -/
noncomputable def aeval (ha : EvalDomain a) :
    PowerSeries R →ₐ[R] S :=
  MvPowerSeries.aeval ha.const

end PowerSeries
