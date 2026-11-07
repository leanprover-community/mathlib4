/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team, Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Thickness of a set in an affine space

For a set `s` in a metric affine space and a natural number `n`,
the `n`-th thickness of `s` measures how well `s` can be approximated
by an affine subspace of rank at most `n`:
it is the infimal radius `r` such that `s` is contained
in the closed `r`-thickening of some affine subspace of rank at most `n`.
The set is not assumed to be convex.

## Main definitions

* `Metric.ethickness 𝕜 s n`: the `ℝ≥0∞`-valued thickness of `s` at rank at most `n`.
* `Metric.thickness 𝕜 s n`: the `ℝ`-valued thickness of `s` at rank at most `n`.

## Main results

* `Metric.ethickness_antitone`, `Metric.ethickness_monotone`:
  `ethickness` decreases in the rank and increases in the set.
* `Metric.ethickness_eq_ofReal_thickness`, `Bornology.IsBounded.ethickness_eq_ofReal_thickness`:
  where `ethickness` is finite, in particular over a bounded set, the two variants agree.
* `Metric.ethickness_cthickening_le`:
  thickening a set by `r` increases its `ethickness` by at most `r`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Metric

variable (𝕜 : Type*) {V P : Type*}

section Ring

variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

section PseudoEMetricSpace

variable [PseudoEMetricSpace P]

-- TODO: consider defining this as `⨅ A (_ : rank ≤ n), ⨆ x ∈ s, infEDist x A`,
-- which avoids the `r.toReal` coercion (under which `r = ⊤` acts as radius `0`).
/--
The `ethickness` of a set `s` at rank `n`
is the infimal radius `r` such that `s` is contained in the `r`-thickening
of an affine subspace of rank at most `n`.
-/
noncomputable def ethickness (s : Set P) (n : ℕ) : ℝ≥0∞ :=
  sInf { r | ∃ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r.toReal A }

/-- The real-valued `n`-thickness of a set `s`:
the infimum of radii `r ≥ 0` for which `s` is contained
in the `r`-thickening of some affine subspace of rank at most `n`.
This is the `ℝ`-valued counterpart of `ethickness`, and is `0` when `ethickness` is infinite. -/
noncomputable def thickness (s : Set P) (n : ℕ) : ℝ :=
  (ethickness 𝕜 s n).toReal

variable {𝕜}

@[simp]
theorem toReal_ethickness (s : Set P) (n : ℕ) :
    (ethickness 𝕜 s n).toReal = thickness 𝕜 s n := rfl

@[simp]
theorem ethickness_empty [Nontrivial 𝕜] (n : ℕ) : ethickness 𝕜 (∅ : Set P) n = 0 :=
  nonpos_iff_eq_zero.1 <| sInf_le
    ⟨⊥, by grind [AffineSubspace.direction_bot, rank_bot, zero_le], by simp⟩

@[simp]
theorem thickness_empty [Nontrivial 𝕜] (n : ℕ) : thickness 𝕜 (∅ : Set P) n = 0 := by
  rw [← toReal_ethickness, ethickness_empty, ENNReal.toReal_zero]

theorem le_ethickness_iff (s : Set P) (n : ℕ) (r : ℝ≥0∞) : r ≤ ethickness 𝕜 s n ↔
    ∀ r' : ℝ≥0, ∀ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n → s ⊆ cthickening r' A
      → r ≤ r' := by
  rw [ethickness, le_sInf_iff]
  refine ⟨fun h r' A hA hs ↦ h r' ⟨A, hA, by simpa using hs⟩, fun h t ⟨A, hA, hs⟩ ↦ ?_⟩
  cases t with
  | top => exact le_top
  | coe t => exact h t A hA hs

/-- `ethickness 𝕜 s n` is decreasing in `n`. -/
theorem ethickness_antitone {s : Set P} : Antitone (ethickness 𝕜 s) := by
  intro m n hmn
  exact sInf_le_sInf fun _ ⟨A, hA, hs⟩ ↦ ⟨A, hA.trans (Nat.cast_le.mpr hmn), hs⟩

/-- `ethickness 𝕜 s n` is monotone in `s`. -/
theorem ethickness_monotone : Monotone (ethickness 𝕜 (P := P)) := by
  intro s t hst n
  exact sInf_le_sInf fun _ ⟨A, hA, ht⟩ ↦ ⟨A, hA, hst.trans ht⟩

/-- Taking the closure does not change `ethickness`, since each `cthickening` is closed. -/
@[simp]
theorem ethickness_closure (s : Set P) (n : ℕ) :
    ethickness 𝕜 (closure s) n = ethickness 𝕜 s n := by
  apply congrArg sInf
  ext r
  exact ⟨fun ⟨A, hA, h⟩ ↦ ⟨A, hA, subset_closure.trans h⟩,
    fun ⟨A, hA, h⟩ ↦ ⟨A, hA, closure_minimal h isClosed_cthickening⟩⟩

/-- Taking the closure does not change `thickness`. -/
@[simp]
theorem thickness_closure (s : Set P) (n : ℕ) :
    thickness 𝕜 (closure s) n = thickness 𝕜 s n := by
  rw [← toReal_ethickness, ethickness_closure, toReal_ethickness]

lemma thickness_nonneg (s : Set P) (n : ℕ) : 0 ≤ thickness 𝕜 s n :=
  ENNReal.toReal_nonneg

theorem ethickness_le_of_cthickening {s : Set P} {n : ℕ} (r : ℝ≥0)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n)
    (hs : s ⊆ cthickening r A) : ethickness 𝕜 s n ≤ r :=
  sInf_le ⟨A, hA, hs⟩

theorem thickness_le_of_cthickening {s : Set P} {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n)
    (hs : s ⊆ cthickening r A) : thickness 𝕜 s n ≤ r :=
  ENNReal.toReal_le_of_le_ofReal hr <| ethickness_le_of_cthickening r.toNNReal hA (by simpa [hr])

theorem ethickness_eq_zero_of_rank_le {s : Set P} {n : ℕ} (h : Module.rank 𝕜 V ≤ n) :
    ethickness 𝕜 s n = 0 :=
  nonpos_iff_eq_zero.1 <| ethickness_le_of_cthickening 0 (A := ⊤)
    (by grind [AffineSubspace.direction_top, rank_top]) (by simp)

theorem thickness_eq_zero_of_rank_le {s : Set P} {n : ℕ} (h : Module.rank 𝕜 V ≤ n) :
    thickness 𝕜 s n = 0 := by
  rw [← toReal_ethickness, ethickness_eq_zero_of_rank_le h, ENNReal.toReal_zero]

theorem exists_notMem_cthickening_of_lt_ethickness {s : Set P} {n : ℕ} {r : ℝ≥0∞}
    (hr : r < ethickness 𝕜 s n)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n) :
    ∃ x ∈ s, x ∉ cthickening r.toReal (A : Set P) := by
  by_contra! h
  exact hr.not_ge <| ENNReal.coe_toNNReal hr.ne_top ▸ ethickness_le_of_cthickening r.toNNReal hA h

/-- If `r : ℝ≥0` strictly exceeds `ethickness 𝕜 s n`,
then `s` is contained in the closed `r`-neighborhood
of some affine subspace of rank at most `n`. -/
theorem exists_cthickening_of_ethickness_lt {s : Set P} {n : ℕ} {r : ℝ≥0}
    (hr : ethickness 𝕜 s n < r) :
    ∃ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r A := by
  rw [← not_le, le_ethickness_iff] at hr
  push Not at hr
  obtain ⟨r', A, hA, hsA, hr'⟩ := hr
  exact ⟨A, hA, hsA.trans (cthickening_mono (mod_cast hr'.le) _)⟩

/-- `ethickness` and `thickness` coincide wherever `ethickness` is finite. -/
theorem ethickness_eq_ofReal_thickness {s : Set P} {n : ℕ} (h : ethickness 𝕜 s n ≠ ⊤) :
    ethickness 𝕜 s n = ENNReal.ofReal (thickness 𝕜 s n) :=
  (ENNReal.ofReal_toReal h).symm

theorem _root_.Set.Subsingleton.ethickness_eq_zero [Nontrivial 𝕜] {s : Set P}
    (hs : s.Subsingleton) (n : ℕ) : ethickness 𝕜 s n = 0 := by
  rcases hs.eq_empty_or_singleton with hs | ⟨x, hs⟩
  · simp [hs]
  · exact nonpos_iff_eq_zero.1 <| ethickness_le_of_cthickening 0 (A := affineSpan 𝕜 {x})
      (by grind [direction_affineSpan, vectorSpan_singleton, rank_bot, zero_le])
      (hs ▸ (subset_affineSpan 𝕜 _).trans (self_subset_cthickening _))

end PseudoEMetricSpace

section PseudoMetricSpace

variable {𝕜} [PseudoMetricSpace P]

/-- The `ethickness` at rank `n` of the `r`-thickening of a set
is bounded by the `ethickness` at rank `n` of the original set plus `r`. -/
theorem ethickness_cthickening_le {s : Set P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (cthickening r s) n ≤ ethickness 𝕜 s n + r := by
  rw [add_comm, ← tsub_le_iff_left, le_ethickness_iff]
  intro t A hA hsA
  rw [tsub_le_iff_left]
  exact ethickness_le_of_cthickening (r + t) hA <| (cthickening_subset_of_subset r hsA).trans
    (cthickening_cthickening_subset r.coe_nonneg t.coe_nonneg _)

variable [Nontrivial 𝕜]

theorem ethickness_closedBall_le {x : P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (closedBall x r) n ≤ r := by
  simpa [cthickening_singleton, Set.subsingleton_singleton.ethickness_eq_zero]
    using ethickness_cthickening_le (𝕜 := 𝕜) (s := {x}) r n

theorem thickness_closedBall_le {x : P} {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    thickness 𝕜 (closedBall x r) n ≤ r :=
  thickness_le_of_cthickening hr (A := affineSpan 𝕜 {x})
    (by grind [direction_affineSpan, vectorSpan_singleton, rank_bot, zero_le])
    (closedBall_subset_cthickening (by simp) _)

/-- If a set is contained in a ball of radius `r`,
then its `ethickness` is bounded by `r` at all ranks. -/
theorem ethickness_le_of_subset_closedBall {s : Set P} {x : P} (r : ℝ≥0)
    (h : s ⊆ closedBall x r) (n : ℕ) : ethickness 𝕜 s n ≤ r := by
  grw [ethickness_monotone h n, ethickness_closedBall_le]

/-- If a set is contained in a ball of radius `r ≥ 0`,
then its `thickness` is bounded by `r` at all ranks. -/
theorem thickness_le_of_subset_closedBall {s : Set P} {x : P} {r : ℝ} (hr : 0 ≤ r)
    (h : s ⊆ closedBall x r) (n : ℕ) : thickness 𝕜 s n ≤ r :=
  ENNReal.toReal_le_of_le_ofReal hr <|
    ethickness_le_of_subset_closedBall r.toNNReal (by simpa [hr]) n

/-- A variant of `Metric.thickness_le_of_subset_closedBall`
where nonnegativity of the radius follows from nonemptiness of the set. -/
theorem thickness_le_of_subset_closedBall_of_nonempty {s : Set P} {x : P} {r : ℝ}
    (hs : s.Nonempty) (h : s ⊆ closedBall x r) (n : ℕ) : thickness 𝕜 s n ≤ r :=
  thickness_le_of_subset_closedBall (nonempty_closedBall.1 (hs.mono h)) h n

/-- A bounded set has `ethickness` strictly less than `⊤` at every rank. -/
theorem _root_.Bornology.IsBounded.ethickness_lt_top {s : Set P} (h : Bornology.IsBounded s)
    (n : ℕ) : ethickness 𝕜 s n < ⊤ := by
  obtain ⟨x⟩ : Nonempty P := inferInstance
  obtain ⟨r, -, hs⟩ := h.subset_closedBall_lt 0 x
  exact (ethickness_le_of_subset_closedBall r.toNNReal
    (hs.trans (closedBall_subset_closedBall r.le_coe_toNNReal)) n).trans_lt ENNReal.coe_lt_top

/-- A bounded set has finite `ethickness` at every rank. -/
theorem _root_.Bornology.IsBounded.ethickness_ne_top {s : Set P} (h : Bornology.IsBounded s)
    (n : ℕ) : ethickness 𝕜 s n ≠ ⊤ :=
  (h.ethickness_lt_top n).ne

/-- `ethickness` and `thickness` coincide at every rank when the set is bounded. -/
theorem _root_.Bornology.IsBounded.ethickness_eq_ofReal_thickness {s : Set P}
    (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n = ENNReal.ofReal (thickness 𝕜 s n) :=
  Metric.ethickness_eq_ofReal_thickness (h.ethickness_ne_top n)

/-- `thickness 𝕜 s` is monotone in `s` over bounded sets. -/
theorem thickness_mono {s t : Set P} (ht : Bornology.IsBounded t) (h : s ⊆ t) :
    thickness 𝕜 s ≤ thickness 𝕜 t := fun n ↦
  ENNReal.toReal_mono (ht.ethickness_ne_top n) (ethickness_monotone h n)

/-- Provided that `s` is bounded, `thickness 𝕜 s n` is decreasing in `n`. -/
theorem thickness_antitone {s : Set P} (hs : Bornology.IsBounded s) :
    Antitone (thickness 𝕜 s) := fun m _ h ↦
  ENNReal.toReal_mono (hs.ethickness_ne_top m) (ethickness_antitone h)

end PseudoMetricSpace

end Ring

end Metric
