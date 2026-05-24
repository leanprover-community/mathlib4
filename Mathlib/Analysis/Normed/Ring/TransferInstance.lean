/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed ring structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

/-- Transfer a `IsNormedRing` across an `Equiv` -/
protected abbrev isNormedRing [NormPseudoMetric β] [Ring β] [IsNormedRing β] (e : α ≃ β) :
    letI := e.ring
    letI := NormPseudoMetric.induced _ _ e
    IsNormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv

end Equiv
