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
# Transfer normed algebraic structures across `Equiv`s or `AddEquiv`s

In this file, we transfer a (semi-)normed (additive) commutative group and normed space structures
across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `SeminormedCommGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `SeminormedAddCommGroup` across an `Equiv` -/]
protected abbrev seminormedCommGroup [SeminormedCommGroup β] (e : α ≃ β) :
    SeminormedCommGroup α :=
  letI := e.commGroup
  { SeminormedCommGroup.induced _ _ e.mulEquiv with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer a `NormedCommGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `NormedAddCommGroup` across an `Equiv` -/]
protected abbrev normedCommGroup [NormedCommGroup β] (e : α ≃ β) : NormedCommGroup α :=
  letI := e.commGroup
  { NormedCommGroup.induced _ _ e.mulEquiv e.injective
    with toPseudoMetricSpace := e.pseudometricSpace }

end Equiv

/-- Transfer `NormedSpace` across an `AddEquiv` -/
protected abbrev AddEquiv.normedSpace (𝕜 : Type*) [NormedField 𝕜]
    [AddCommGroup α] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β] (e : α ≃+ β) :
    letI : SeminormedAddCommGroup α :=
      letI := e.pseudometricSpace
      fast_instance%
      { SeminormedAddCommGroup.induced α β e with
        toPseudoMetricSpace := e.pseudometricSpace }
    NormedSpace 𝕜 α :=
  letI : SeminormedAddCommGroup α :=
    letI := e.pseudometricSpace
    fast_instance%
    { SeminormedAddCommGroup.induced α β e with
      toPseudoMetricSpace := e.pseudometricSpace }
  letI := e.module 𝕜
  { norm_smul_le a b := by
      change norm (e (a • b)) ≤ norm a * norm (e b)
      rw [← norm_smul, ← e.linearEquiv_apply (R := 𝕜),
        ← e.linearEquiv_apply (R := 𝕜), map_smul] }

@[deprecated (since := "2026-07-30")] alias Equiv.normedSpace := AddEquiv.normedSpace
