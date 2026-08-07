/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The Heine–Cantor theorem in emetric ε-δ form

A function continuous on a compact set of a pseudoemetric space is uniformly continuous there.
This file records the emetric ε-δ consequences of the uniform-space level
`IsCompact.uniformContinuousOn_of_continuous` and its siblings.

See `Mathlib/Topology/MetricSpace/HeineCantor.lean` for the versions phrased in terms of `dist`
and a real ε.
-/

public section

open EMetric ENNReal CompactSpace

variable {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] {s : Set α} {f : α → β}

/-- **Heine–Cantor** in emetric ε-δ form: a function `f` continuous on a compact set `s` is
uniformly continuous there, so for every `ε > 0` there is a `δ > 0` such that points of `s`
within `δ` are mapped within `ε`. -/
theorem ContinuousOn.exists_forall_edist_lt_of_isCompact (hs : IsCompact s) (hf : ContinuousOn f s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, edist x y < δ → edist (f x) (f y) < ε :=
  uniformContinuousOn_iff.mp (hs.uniformContinuousOn_of_continuous hf) ε hε

/-- Version of `ContinuousOn.exists_forall_edist_lt_of_isCompact` with non-strict inequalities. -/
theorem ContinuousOn.exists_forall_edist_le_of_isCompact (hs : IsCompact s) (hf : ContinuousOn f s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ δ → edist (f x) (f y) ≤ ε :=
  uniformContinuousOn_iff_le.mp (hs.uniformContinuousOn_of_continuous hf) ε hε

/-- **Heine–Cantor** on a compact space, in emetric ε-δ form: a continuous function on a compact
pseudoemetric space is uniformly continuous, so for every `ε > 0` there is a `δ > 0` such that any
two points within `δ` are mapped within `ε`. -/
theorem Continuous.exists_forall_edist_lt_of_compactSpace [CompactSpace α] (hf : Continuous f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : α, edist x y < δ → edist (f x) (f y) < ε :=
  uniformContinuous_iff.mp (uniformContinuous_of_continuous hf) ε hε

/-- Version of `Continuous.exists_forall_edist_lt_of_compactSpace` with non-strict inequalities. -/
theorem Continuous.exists_forall_edist_le_of_compactSpace [CompactSpace α] (hf : Continuous f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : α, edist x y ≤ δ → edist (f x) (f y) ≤ ε :=
  uniformContinuous_iff_le.mp (uniformContinuous_of_continuous hf) ε hε

/-- Emetric ε-δ form of `IsCompact.uniformContinuousAt_of_continuousAt`: if `f` is continuous at
each point of a compact set `s`, then for every `ε > 0` there is a `δ > 0` such that `f x` and
`f y` are within `ε` whenever `x ∈ s` and `y` is within `δ` of `x`. Unlike
`ContinuousOn.exists_forall_edist_lt_of_isCompact`, the point `y` need not lie in `s`. -/
theorem IsCompact.exists_forall_edist_lt_of_continuousAt (hs : IsCompact s)
    (hf : ∀ a ∈ s, ContinuousAt f a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, edist x y < δ → edist (f x) (f y) < ε :=
  let ⟨δ, hδ, H⟩ := uniformity_basis_edist.mem_iff.1
    (hs.uniformContinuousAt_of_continuousAt f hf (uniformity_basis_edist.mem_of_mem hε))
  ⟨δ, hδ, fun x hx y hxy ↦ H (a := (x, y)) hxy hx⟩

/-- Version of `IsCompact.exists_forall_edist_lt_of_continuousAt` with non-strict inequalities. -/
theorem IsCompact.exists_forall_edist_le_of_continuousAt (hs : IsCompact s)
    (hf : ∀ a ∈ s, ContinuousAt f a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, edist x y ≤ δ → edist (f x) (f y) ≤ ε :=
  let ⟨δ, hδ, H⟩ := uniformity_basis_edist_le.mem_iff.1
    (hs.uniformContinuousAt_of_continuousAt f hf (uniformity_basis_edist_le.mem_of_mem hε))
  ⟨δ, hδ, fun x hx y hxy ↦ H (a := (x, y)) hxy hx⟩
