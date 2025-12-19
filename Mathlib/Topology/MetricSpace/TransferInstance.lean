/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Transfer metric space structures across `Equiv`s, `Homeomorph`s and `UniformEquiv`s

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

namespace Homeomorph

variable [TopologicalSpace α]

/-- Transfer a `PseudoMetricSpace` across a `Homeomorph`, keeping the existing topology. -/
protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ₜ β) : PseudoMetricSpace α :=
  .replaceTopology (.induced e ‹_›) e.induced_eq.symm

/-- Transfer a `MetricSpace` across a `Homeomorph`, keeping the existing topology. -/
protected abbrev metricSpace [MetricSpace β] (e : α ≃ₜ β) : MetricSpace α :=
  .replaceTopology (.induced e e.injective ‹_›) e.induced_eq.symm

end Homeomorph

namespace UniformEquiv

variable [UniformSpace α]

/-- Transfer a `PseudoMetricSpace` across a `UniformEquiv`, keeping the existing uniformity. -/
protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ᵤ β) : PseudoMetricSpace α :=
  .replaceUniformity (.induced e ‹_›) (congrArg _ e.comap_eq.symm)

/-- Transfer a `MetricSpace` across a `UniformEquiv`, keeping the existing uniformity. -/
protected abbrev metricSpace [MetricSpace β] (e : α ≃ᵤ β) : MetricSpace α :=
  .replaceUniformity (.induced e e.injective ‹_›) (congrArg _ e.comap_eq.symm)

end UniformEquiv
