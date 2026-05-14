/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta, Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Compact operators and finite dimensional spaces

This file contains results linking `IsCompactOperator` with `FiniteDimensional`.

The motivation for not including this in the same file as the definition of compact operators
is that `Mathlib.Topology.Algebra.Module.FiniteDimension` is quite a heavy import to add there.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

theorem isCompactOperator_id_iff_finiteDimensional [LocallyCompactSpace 𝕜] :
    IsCompactOperator (_root_.id : E → E) ↔ FiniteDimensional 𝕜 E :=
  isCompactOperator_id_iff_locallyCompactSpace.trans
    ⟨fun _ ↦ .of_locallyCompactSpace 𝕜, fun _ ↦ .of_finiteDimensional_of_complete 𝕜 E⟩

/-- If the identity operator of a Banach space over a nontrivially normed field is compact,
then the space is finite dimensional. -/
lemma FiniteDimensional.of_isCompactOperator_id (h : IsCompactOperator (id : E → E)) :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_isCompactOperator_id h
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

@[deprecated (since := "2026-03-05")] alias IsCompactOperator.finiteDimensional :=
  FiniteDimensional.of_isCompactOperator_id
