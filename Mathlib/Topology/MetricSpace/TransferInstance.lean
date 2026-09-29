/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Homeomorph.TransferInstance

/-!
# Transfer metric space structures across `Equiv`s

In this file, we transfer a distance and (pseudo-)metric space structure across an equivalence.

-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer a `Dist` across an `Equiv` -/
protected abbrev dist (e : α ≃ β) [Dist β] : Dist α := ⟨fun x y ↦ dist (e.toFun x) (e.toFun y)⟩

/-- Transfer a `PseudoMetricSpace` across an `Equiv` -/
protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ β) : PseudoMetricSpace α :=
  letI := e.topologicalSpace
  (PseudoMetricSpace.induced e.toFun ‹_›).replaceTopology
    (by exact congrFun e.coinduced_symm inferInstance)

/-- Transfer a `MetricSpace` across an `Equiv` -/
protected abbrev metricSpace [MetricSpace β] (e : α ≃ β) : MetricSpace α :=
  letI := e.topologicalSpace
  (MetricSpace.induced e.toFun e.injective ‹_›).replaceTopology
    (by exact congrFun e.coinduced_symm inferInstance)

end Equiv
