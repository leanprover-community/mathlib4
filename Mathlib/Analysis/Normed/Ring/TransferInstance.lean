/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Topology.MetricSpace.TransferInstance

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed ring structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β) [NormedCommGroup β]

/-- Transfer a `SeminormedRing` across an `Equiv` -/
protected abbrev seminormedRing [SeminormedRing β] (e : α ≃ β) :
    SeminormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv

/-- Transfer a `NormedRing` across an `Equiv` -/
protected abbrev normedRing [NormedRing β] (e : α ≃ β) : NormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv e.injective

end Equiv
