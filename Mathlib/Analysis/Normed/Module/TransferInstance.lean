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
# Transfer algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed additive commutative group and normed space structures
across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `SeminormedAddCommGroup` across an `Equiv` -/
protected abbrev seminormedAddCommGroup [SeminormedAddCommGroup β] (e : α ≃ β) :
    SeminormedAddCommGroup α :=
  letI := e.addCommGroup
  { SeminormedAddCommGroup.induced _ _ e.addEquiv with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer a `NormedAddCommGroup` across an `Equiv` -/
protected abbrev normedAddCommGroup [NormedAddCommGroup β] (e : α ≃ β) : NormedAddCommGroup α :=
  letI := e.addCommGroup
  { NormedAddCommGroup.induced _ _ e.addEquiv e.injective
    with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer `NormedSpace` across an `Equiv` -/
protected abbrev normedSpace (𝕜 : Type*) [NormedField 𝕜]
    [SeminormedAddCommGroup β] [NormedSpace 𝕜 β] (e : α ≃ β) :
    letI := Equiv.seminormedAddCommGroup e
    NormedSpace 𝕜 α :=
  letI := e.seminormedAddCommGroup
  letI := e.module 𝕜
  .induced _ _ _ (e.linearEquiv _)

end Equiv
