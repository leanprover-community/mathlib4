/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Topologies on spaces of measures

We define the weak and strong topologies on `D(X, E)`.
-/

@[expose] public section

open ContinuousMap Topology

variable {X R E : Type*} [TopologicalSpace X]

namespace AbstractMeasure

section Topology

section Weak

variable [NormedAddCommGroup E] [CommRing R] [Module R E] [TopologicalSpace R]
  [IsTopologicalRing R] [ContinuousSMul R E]

/--
The weak topology on `AbstractMeasure G R E` (the weakest topology such that `μ ↦ μ f` is
continuous for all `f`).
-/
@[reducible] def WeakTopology : TopologicalSpace (AbstractMeasure X R E) :=
  .induced (fun μ f ↦ μ f) inferInstance

scoped [AbstractMeasure.WeakTopology] attribute [instance] WeakTopology

end Weak

variable [CompactSpace X] [NontriviallyNormedField R] [NormedAddCommGroup E] [NormedSpace R E]

noncomputable instance : Norm (AbstractMeasure X R E) :=
  inferInstanceAs (Norm (C(X, R) →L[R] E))

/-- The strong topology on `AbstractMeasure G R E` (the topology induced by the norm). -/
@[reducible] def StrongTopology : TopologicalSpace (AbstractMeasure X R E) :=
  inferInstanceAs (TopologicalSpace (C(X, R) →L[R] E))

scoped [AbstractMeasure.StrongTopology] attribute [instance] StrongTopology

end Topology

end AbstractMeasure

end
