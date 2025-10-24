/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Rel.Cover
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Covers in a metric space

This file defines covers, aka nets, which are a quantitative notion of compactness in a metric
space.

A `ε`-cover of a set `s` is a set `N` such that every element of `s` is at distance at most `ε` to
some element of `N`.

In a proper metric space, sets admitting a finite cover are precisely the relatively compact sets.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

open Set
open scoped NNReal

namespace Metric
variable {X : Type*}

section PseudoEMetricSpace
variable [PseudoEMetricSpace X] {ε δ : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

/-- A set `N` is an *`ε`-cover* of a set `s` if every point of `s` lies at distance at most `ε` of
some point of `N`.

This is also called an *`ε`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
def IsCover (ε : ℝ≥0) (s N : Set X) : Prop := UniformSpace.IsCover {(x, y) | edist x y ≤ ε} s N

@[simp] protected nonrec lemma IsCover.empty : IsCover ε ∅ N := .empty

@[simp] protected nonrec lemma IsCover.nonempty (hsN : IsCover ε s N) (hs : s.Nonempty) :
    N.Nonempty := hsN.nonempty hs

nonrec lemma IsCover.mono (hN : N₁ ⊆ N₂) (h₁ : IsCover ε s N₁) : IsCover ε s N₂ := h₁.mono hN

nonrec lemma IsCover.anti (hst : s ⊆ t) (ht : IsCover ε t N) : IsCover ε s N := ht.anti hst

lemma IsCover.mono' (hεδ : ε ≤ δ) (hε : IsCover ε s N) : IsCover δ s N :=
  hε.mono_uniformity fun xy hxy ↦ by dsimp at *; exact le_trans hxy <| mod_cast hεδ

lemma isCover_iff_subset_iUnion_emetricClosedBall :
    IsCover ε s N ↔ s ⊆ ⋃ y ∈ N, EMetric.closedBall y ε := by
  simp [IsCover, UniformSpace.IsCover, subset_def]

/-- A maximal `ε`-separated subset of a set `s` is an `ε`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
nonrec lemma IsCover.of_maximal_isSeparated (hN : Maximal (fun N ↦ N ⊆ s ∧ IsSeparated ε N) N) :
    IsCover ε s N :=
  .of_maximal_isSeparated (by simp) (by simp [IsSymmetricRel, edist_comm]) <| by
    simpa [isSeparated_iff_uniformSpaceIsSeparated] using hN

end PseudoEMetricSpace

section PseudoMetricSpace
variable [PseudoMetricSpace X] {ε : ℝ≥0} {s N : Set X}

lemma isCover_iff_subset_iUnion_closedBall : IsCover ε s N ↔ s ⊆ ⋃ y ∈ N, closedBall y ε := by
  simp [IsCover, UniformSpace.IsCover, subset_def]

alias ⟨IsCover.subset_iUnion_closedBall, IsCover.of_subset_iUnion_closedBall⟩ :=
  isCover_iff_subset_iUnion_closedBall

/-- A relatively compact set admits a finite cover. -/
lemma exists_finite_isCover_of_isCompact_closure (hε : ε ≠ 0) (hs : IsCompact (closure s)) :
    ∃ N ⊆ s, N.Finite ∧ IsCover ε s N := by
  obtain ⟨N, hNs, hN, hsN⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hs (ε := ε) (by positivity)
  refine ⟨N, hNs, hN, .of_subset_iUnion_closedBall <| hsN.trans ?_⟩
  gcongr
  exact ball_subset_closedBall

/-- A compact set admits a finite cover. -/
lemma exists_finite_isCover_of_isCompact (hε : ε ≠ 0) (hs : IsCompact s) :
    ∃ N ⊆ s, N.Finite ∧ IsCover ε s N := by
  obtain ⟨N, hNs, hN, hsN⟩ := hs.finite_cover_balls (e := ε) (by positivity)
  refine ⟨N, hNs, hN, .of_subset_iUnion_closedBall <| hsN.trans ?_⟩
  gcongr
  exact ball_subset_closedBall

lemma IsCover.of_subset_cthickening_of_lt {δ : ℝ≥0} (hsN : s ⊆ cthickening ε N) (hεδ : ε < δ) :
    IsCover δ s N :=
  .of_subset_iUnion_closedBall <| hsN.trans (cthickening_subset_iUnion_closedBall_of_lt _
    (NNReal.zero_le_coe.trans_lt hεδ) hεδ)

variable [ProperSpace X]

lemma isCover_iff_subset_cthickening (hN : IsClosed N) : IsCover ε s N ↔ s ⊆ cthickening ε N := by
  rw [isCover_iff_subset_iUnion_closedBall, hN.cthickening_eq_biUnion_closedBall ε.zero_le_coe]

alias ⟨IsCover.subset_cthickening, IsCover.of_subset_cthickening⟩ := isCover_iff_subset_cthickening

@[simp] lemma isCover_closure (hN : IsClosed N) : IsCover ε (closure s) N ↔ IsCover ε s N := by
  simpa [isCover_iff_subset_cthickening hN] using (isClosed_cthickening (E := N)).closure_subset_iff

protected alias ⟨_, IsCover.closure⟩ := isCover_closure

end PseudoMetricSpace

section EMetricSpace
variable [EMetricSpace X] {ε : ℝ≥0} {s N : Set X} {x : X}

@[simp] lemma isCover_zero : IsCover 0 s N ↔ s ⊆ N := by
  simp [isCover_iff_subset_iUnion_emetricClosedBall]

end EMetricSpace

section MetricSpace
variable [MetricSpace X] [ProperSpace X] {ε : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

/-- A closed set in a proper metric space which admits a compact cover is compact. -/
lemma IsCover.isCompact (hsN : IsCover ε s N) (hs : IsClosed s) (hN : IsCompact N) :
    IsCompact s := .of_isClosed_subset hN.cthickening hs <| hsN.subset_cthickening hN.isClosed

/-- A set in a proper metric space which admits a compact cover is relatively compact. -/
lemma IsCover.isCompact_closure (hsN : IsCover ε s N) (hN : IsCompact N) :
    IsCompact (closure s) := (hsN.closure hN.isClosed).isCompact isClosed_closure hN

/-- A set in a proper metric space admits a finite cover iff it is relatively compact.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.3. Note that the print
edition incorrectly claims that this holds without the `ProperSpace X` assumption. -/
lemma isCompact_closure_iff_exists_finite_isCover (hε : ε ≠ 0) :
    IsCompact (closure s) ↔ ∃ N ⊆ s, N.Finite ∧ IsCover ε s N where
  mp := exists_finite_isCover_of_isCompact_closure hε
  mpr := fun ⟨_N, _, hN, hsN⟩ ↦ hsN.isCompact_closure hN.isCompact

end MetricSpace
end Metric
