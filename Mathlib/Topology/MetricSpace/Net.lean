/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Nets

This file defines nets, which are a quantitative notion of compactness in a metric space.

A `ε`-net of a set `s` is a set `N` such that every element of `s` is at distance at most `ε` to
some element of `N`.

In a proper metric space, sets admitting a finite net are precisely the relatively compact sets.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

open Set
open scoped NNReal

namespace Metric
variable {X : Type*}

section PseudoEMetricSpace
variable [PseudoEMetricSpace X] {ε : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

/-- A set `N` is an *`ε`-net* of a set `s` if every point of `s` lies at distance at most `ε` of
some point of `N`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
def IsNet (ε : ℝ≥0) (s N : Set X) : Prop := ∀ ⦃x⦄, x ∈ s → ∃ y ∈ N, edist x y ≤ ε

@[simp] lemma IsNet.empty : IsNet ε ∅ N := by simp [IsNet]

lemma IsNet.mono (hN : N₁ ⊆ N₂) (h₁ : IsNet ε s N₁) : IsNet ε s N₂ :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩

lemma IsNet.anti (hst : s ⊆ t) (ht : IsNet ε t N) : IsNet ε s N := fun _x hx ↦ ht <| hst hx

lemma isNet_iff_subset_iUnion_emetricClosedBall :
    IsNet ε s N ↔ s ⊆ ⋃ y ∈ N, EMetric.closedBall y ε := by simp [IsNet, subset_def]

/-- A maximal `ε`-separated subset of a set `s` is an `ε`-net of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
lemma IsNet.of_maximal_isSeparated (hN : Maximal (fun N ↦ N ⊆ s ∧ IsSeparated ε N) N) :
    IsNet ε s N := by
  rintro x hx
  by_contra! h
  simpa using h _ <| hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert fun y hy _ ↦ h y hy⟩ (subset_insert _ _) (mem_insert _ _)

end PseudoEMetricSpace

section PseudoMetricSpace
variable [PseudoMetricSpace X] {ε : ℝ≥0} {s N : Set X}

lemma isNet_iff_subset_iUnion_closedBall : IsNet ε s N ↔ s ⊆ ⋃ y ∈ N, closedBall y ε := by
  simp [IsNet, subset_def]

alias ⟨IsNet.subset_iUnion_closedBall, IsNet.of_subset_iUnion_closedBall⟩ :=
  isNet_iff_subset_iUnion_closedBall

/-- A relatively compact set admits a finite net. -/
lemma exists_finite_isNet_of_isCompact_closure (hε : ε ≠ 0) (hs : IsCompact (closure s)) :
    ∃ N ⊆ s, N.Finite ∧ IsNet ε s N := by
  obtain ⟨N, hNs, hN, hsN⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hs (ε := ε) (by positivity)
  refine ⟨N, hNs, hN, .of_subset_iUnion_closedBall <| hsN.trans ?_⟩
  gcongr
  exact ball_subset_closedBall

/-- A compact set admits a finite net. -/
lemma exists_finite_isNet_of_isCompact (hε : ε ≠ 0) (hs : IsCompact s) :
    ∃ N ⊆ s, N.Finite ∧ IsNet ε s N := by
  obtain ⟨N, hNs, hN, hsN⟩ := hs.finite_cover_balls (e := ε) (by positivity)
  refine ⟨N, hNs, hN, .of_subset_iUnion_closedBall <| hsN.trans ?_⟩
  gcongr
  exact ball_subset_closedBall

variable [ProperSpace X]

lemma isNet_iff_subset_cthickening (hN : IsClosed N) : IsNet ε s N ↔ s ⊆ cthickening ε N := by
  rw [isNet_iff_subset_iUnion_closedBall, hN.cthickening_eq_biUnion_closedBall ε.zero_le_coe]

alias ⟨IsNet.subset_cthickening, IsNet.of_subset_cthickening⟩ := isNet_iff_subset_cthickening

@[simp] lemma isNet_closure (hN : IsClosed N) : IsNet ε (closure s) N ↔ IsNet ε s N := by
  simpa [isNet_iff_subset_cthickening hN] using (isClosed_cthickening (E := N)).closure_subset_iff

protected alias ⟨_, IsNet.closure⟩ := isNet_closure

end PseudoMetricSpace

section EMetricSpace
variable [EMetricSpace X] {ε : ℝ≥0} {s N : Set X} {x : X}

@[simp] lemma isNet_zero : IsNet 0 s N ↔ s ⊆ N := by
  simp [isNet_iff_subset_iUnion_emetricClosedBall]

end EMetricSpace

section MetricSpace
variable [MetricSpace X] [ProperSpace X] {ε : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

/-- A closed set in a proper metric space which admits a compact net is compact. -/
lemma IsNet.isCompact (hsN : IsNet ε s N) (hs : IsClosed s) (hN : IsCompact N) :
    IsCompact s := .of_isClosed_subset hN.cthickening hs <| hsN.subset_cthickening hN.isClosed

/-- A set in a proper metric space which admits a compact net is relatively compact. -/
lemma IsNet.isCompact_closure (hsN : IsNet ε s N) (hN : IsCompact N) :
    IsCompact (closure s) := (hsN.closure hN.isClosed).isCompact isClosed_closure hN

/-- A set in a proper metric space admits a finite net iff it is relatively compact.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.3. Note that the print
edition incorrectly claims that this holds without the `ProperSpace X` assumption. -/
lemma isCompact_closure_iff_exists_finite_isNet (hε : ε ≠ 0) :
    IsCompact (closure s) ↔ ∃ N ⊆ s, N.Finite ∧ IsNet ε s N where
  mp := exists_finite_isNet_of_isCompact_closure hε
  mpr := fun ⟨_N, _, hN, hsN⟩ ↦ hsN.isCompact_closure hN.isCompact

end MetricSpace
end Metric
