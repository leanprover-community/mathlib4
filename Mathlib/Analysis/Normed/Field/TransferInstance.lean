/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a normed field structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {α β : Type*}

namespace Equiv

/-- Transfer a `NormedField` across an `Equiv` -/
protected abbrev normedField [NormedField β] (e : α ≃ β) : NormedField α :=
  letI := e.field
  .induced α β e.ringEquiv e.injective

end Equiv
