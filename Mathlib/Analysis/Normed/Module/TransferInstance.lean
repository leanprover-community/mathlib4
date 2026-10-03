/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Topology.MetricSpace.TransferInstance

/-!
# Transfer normed algebraic structures across `Equiv`s or `AddEquiv`s

In this file, we transfer a (semi-)normed (additive) commutative group and normed space structures
across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `SeminormedCommGroup` across an `Equiv`. Under the unbundling this is the
`SeminormedGroup` half; the commutativity half is `Equiv.commGroup`. -/
@[to_additive /-- Transfer a `SeminormedAddCommGroup` across an `Equiv`. Under the unbundling
this is the `SeminormedAddGroup` half; the commutativity half is `Equiv.addCommGroup`. -/]
protected abbrev seminormedCommGroup [SeminormedGroup β] [IsMulCommutative β] (e : α ≃ β) :
    SeminormedGroup α :=
  letI := e.group
  letI := e.commGroup
  { SeminormedCommGroup.induced _ _ e.mulEquiv with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer a `NormedCommGroup` across an `Equiv`. Under the unbundling this is the
`NormedGroup` half; the commutativity half is `Equiv.commGroup`. -/
@[to_additive /-- Transfer a `NormedAddCommGroup` across an `Equiv`. Under the unbundling this
is the `NormedAddGroup` half; the commutativity half is `Equiv.addCommGroup`. -/]
protected abbrev normedCommGroup [NormedGroup β] [IsMulCommutative β] (e : α ≃ β) :
    NormedGroup α :=
  letI := e.group
  letI := e.commGroup
  { NormedCommGroup.induced _ _ e.mulEquiv e.injective
    with toPseudoMetricSpace := e.pseudometricSpace }

end Equiv

/-- Transfer `NormedSpace` across an `AddEquiv` -/
protected abbrev AddEquiv.normedSpace (𝕜 : Type*) [NormedField 𝕜]
    [AddGroup α] [IsAddCommutative α] [SeminormedAddGroup β] [IsAddCommutative β] [NormedSpace 𝕜 β]
    (e : α ≃+ β) :
    letI : SeminormedAddGroup α := SeminormedAddCommGroup.induced _ _ e
    NormedSpace 𝕜 α :=
  letI := e.module 𝕜
  .induced _ _ _ (e.linearEquiv _)

@[deprecated (since := "2026-07-30")] alias Equiv.normedSpace := AddEquiv.normedSpace
