/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Transfer metric space structures across `Equiv`s

In this file, we transfer a distance and (pseudo-)metric space structure across an equivalence.

-/

@[expose] public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `Dist` across an `Equiv` -/
protected abbrev dist (e : α ≃ β) [Dist β] : Dist α := ⟨fun x y ↦ dist (e x) (e y)⟩

/-- Transfer a `PseudoMetricSpace` across an `Equiv` -/
protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ β) : PseudoMetricSpace α :=
  .induced e ‹_›

/-- Transfer a `MetricSpace` across an `Equiv` -/
protected abbrev metricSpace [MetricSpace β] (e : α ≃ β) : MetricSpace α :=
  .induced e e.injective ‹_›

end Equiv
