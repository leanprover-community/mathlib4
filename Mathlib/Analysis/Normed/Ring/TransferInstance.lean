/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed ring structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

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
