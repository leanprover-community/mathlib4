/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Lua Viana Reis
-/
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Birkhoff sum and average for quasi-measure-preserving maps

Given a map `f` and measure `μ`, under the assumption of `QuasiMeasurePreserving f μ μ` we prove:

- `birkhoffSum_ae_eq_of_ae_eq`: if observables  `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffSum f` are `μ`-a.e. equal.

- `birkhoffAverage_ae_eq_of_ae_eq`: if observables `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffAverage R f` are `μ`-a.e. equal.

-/

namespace MeasureTheory.Measure.QuasiMeasurePreserving

open Filter

variable {α M : Type*} [MeasurableSpace α] [AddCommMonoid M]
variable {f : α → α} {μ : Measure α} {φ ψ : α → M}

/-- If observables  `φ` and `ψ` are `μ`-a.e. equal then the corresponding `birkhoffSum` are
`μ`-a.e. equal. -/
theorem birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n :
    birkhoffSum f φ n =ᵐ[μ] birkhoffSum f ψ n := by
  apply Eventually.mono _ (fun _ => Finset.sum_congr rfl)
  apply ae_all_iff.mpr (fun i => ?_)
  exact (hf.iterate i).ae (hφ.mono (fun _ h _ => h))

/-- If observables `φ` and `ψ` are `μ`-a.e. equal then the corresponding `birkhoffAverage` are
 `μ`-a.e. equal. -/
theorem birkhoffAverage_ae_eq_of_ae_eq (R : Type*) [DivisionSemiring R] [Module R M]
    (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n :
    birkhoffAverage R f φ n =ᵐ[μ] birkhoffAverage R f ψ n :=
  EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

end MeasureTheory.Measure.QuasiMeasurePreserving
