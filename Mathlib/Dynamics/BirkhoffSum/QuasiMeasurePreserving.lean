/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Birkhoff sum and average for quasi-measure-preserving maps

Given a map `f` and measure `μ`, under the assumption of `QuasiMeasurePreserving f μ μ` we prove:

- `birkhoffSum_ae_eq_of_ae_eq`: if observables  `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffSum f` are `μ`-a.e. equal.

- `birkhoffAverage_ae_eq_of_ae_eq`: if observables `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffAverage R f` are `μ`-a.e. equal.

-/

public section

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
