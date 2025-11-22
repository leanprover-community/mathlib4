/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

In this file, we transfer a (pseudo-)metric space, (semi-)normed additive commutive group
and normed space structures across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `Dist` across an `Equiv` -/
protected abbrev dist (e : α ≃ β) : ∀ [Dist β], Dist α := ⟨fun x y ↦ dist (e x) (e y)⟩

/-- Transfer a `PseudoMetricSpace` across an `Equiv` -/
protected abbrev pseudometricSpace (e : α ≃ β) : ∀ [PseudoMetricSpace β], PseudoMetricSpace α :=
  .induced e ‹_›

/-- Transfer a `MetricSpace` across an `Equiv` -/
protected abbrev metricSpace (e : α ≃ β) : ∀ [MetricSpace β], MetricSpace α :=
  .induced e e.injective ‹_›

/-- Transfer a `SeminormedAddCommGroup` across an `Equiv` -/
protected abbrev seminormedAddCommGroup (e : α ≃ β) :
    ∀ [SeminormedAddCommGroup β], SeminormedAddCommGroup α :=
  letI := e.addCommGroup
  { SeminormedAddCommGroup.induced _ _ e.addEquiv with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer a `NormedAddCommGroup` across an `Equiv` -/
protected abbrev normedAddCommGroup (e : α ≃ β) :
    ∀ [NormedAddCommGroup β], NormedAddCommGroup α :=
  letI := e.addCommGroup
  { NormedAddCommGroup.induced _ _ e.addEquiv e.injective
    with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer `NormedSpace` across an `Equiv` -/
protected abbrev normedSpace (𝕜 : Type*) [NormedField 𝕜] (e : α ≃ β) [SeminormedAddCommGroup β] :
    let _ := Equiv.seminormedAddCommGroup e
    ∀ [NormedSpace 𝕜 β], NormedSpace 𝕜 α :=
  letI := e.seminormedAddCommGroup
  letI := e.module 𝕜
  .induced _ _ _ (e.linearEquiv _)

end Equiv
