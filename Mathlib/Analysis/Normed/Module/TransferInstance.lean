/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Topology.MetricSpace.TransferInstance

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed (additive) commutative group and normed space structures
across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `NormPseudoMetric` across an `Equiv` -/
protected abbrev normPseudoMetric [NormPseudoMetric β] (e : α ≃ β) :
    NormPseudoMetric α :=
  { NormPseudoMetric.induced _ _ e with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer a `NormMetric` across an `Equiv` -/
protected abbrev normMetric [NormMetric β] (e : α ≃ β) :
    NormMetric α :=
  { NormMetric.induced _ _ e e.injective with toMetricSpace := e.metricSpace }

/-- Transfer a `IsNormedGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `IsNormedAddGroup` across an `Equiv` -/]
protected lemma isNormedGroup [NormPseudoMetric β] [CommGroup β] [IsNormedGroup β] (e : α ≃ β) :
    letI := e.normPseudoMetric
    letI := e.commGroup
    IsNormedGroup α :=
  letI := e.normPseudoMetric
  letI := e.commGroup
  .induced _ _ e.mulEquiv

set_option linter.deprecated false in
/-- Transfer a `SeminormedCommGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `SeminormedCommGroup` across an `Equiv` -/]
protected abbrev seminormedCommGroup [NormPseudoMetric β] [CommGroup β] [IsNormedGroup β] (e : α ≃ β) :
    SeminormedCommGroup α where
  __ := e.normPseudoMetric
  __ := e.commGroup
  toIsNormedGroup := e.isNormedGroup

set_option linter.deprecated false in
/-- Transfer a `NormedCommGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `NormedCommGroup` across an `Equiv` -/]
protected abbrev normedCommGroup [NormMetric β] [CommGroup β] [IsNormedGroup β] (e : α ≃ β) :
    NormedCommGroup α where
  __ := e.normMetric
  __ := e.commGroup
  toIsNormedGroup := .induced _ _ e.mulEquiv

attribute [deprecated Equiv.isNormedGroup (since := "2026-05-17")]
  Equiv.seminormedCommGroup Equiv.normedCommGroup
attribute [deprecated Equiv.isNormedAddGroup (since := "2026-05-17")]
  Equiv.seminormedAddCommGroup Equiv.normedAddCommGroup

/-- Transfer `NormedSpace` across an `Equiv` -/
protected abbrev normedSpace (𝕜 : Type*) [NormMetric 𝕜] [Field 𝕜] [IsNormedField 𝕜]
    [NormPseudoMetric β] [AddCommGroup β] [IsNormedAddGroup β] [NormedSpace 𝕜 β] (e : α ≃ β) :
    letI := e.normPseudoMetric
    letI := e.addCommGroup
    letI := e.isNormedAddGroup
    NormedSpace 𝕜 α :=
  letI := e.normPseudoMetric
  letI := e.addCommGroup
  letI := e.isNormedAddGroup
  letI := e.module 𝕜
  .induced _ _ _ (e.linearEquiv _)

end Equiv
