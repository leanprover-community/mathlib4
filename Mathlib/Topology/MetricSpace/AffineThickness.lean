/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team, Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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

* `Metric.ethickness 𝕜 s n`: the `ℝ≥0∞`-valued thickness of `s` at rank `n`.
* `Metric.thickness 𝕜 s n`: the `ℝ`-valued thickness of `s` at rank `n`.

## Main results

* `Metric.ethickness_antitone`, `Metric.ethickness_monotone`:
  `ethickness` decreases in the rank and increases in the set.
* `Metric.ethickness_thickness`: over a bounded set the two variants agree.
* `Metric.ethickness_cthickening_le`:
  thickening a set by `r` increases its `ethickness` by at most `r`.

## Implementation notes

`ethickness` is indexed by the rank of the approximating subspace,
so it is decreasing in the rank.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Metric

variable (𝕜 : Type*) {V P : Type*}

section Ring

variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

section PseudoEMetricSpace

variable [PseudoEMetricSpace P]

/--
The `ethickness` of a set `s` at rank `n`
is the infimal radius `r` such that `s` is contained in the `r`-thickening
of a rank `n` affine subspace.
-/
noncomputable def ethickness (s : Set P) (n : ℕ) : ℝ≥0∞ :=
  sInf { r | ∃ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r.toReal A }

/-- The real-valued `n`-thickness of a set `s`:
the infimum of radii `r ≥ 0` for which `s` is contained
in the `r`-thickening of some affine subspace of dimension at most `n`.
This is the `ℝ`-valued counterpart of `ethickness`. -/
noncomputable def thickness (s : Set P) (n : ℕ) : ℝ :=
  sInf { r | 0 ≤ r ∧ ∃ A : AffineSubspace 𝕜 P,
    Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r A }

variable {𝕜}

@[simp]
theorem ethickness_empty [Nontrivial 𝕜] (n : ℕ) : ethickness 𝕜 (∅ : Set P) n = 0 :=
  nonpos_iff_eq_zero.1 <| sInf_le
    ⟨⊥, by grind [AffineSubspace.direction_bot, rank_bot, zero_le], by simp⟩

theorem le_ethickness_iff (s : Set P) (n : ℕ) (r : ℝ≥0∞) : r ≤ ethickness 𝕜 s n ↔
    ∀ r' : ℝ≥0, ∀ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n → s ⊆ cthickening r' A
      → r ≤ r' := by
  rw [ethickness, le_sInf_iff]
  refine ⟨fun h r' A hA hs ↦ h r' ⟨A, hA, by simpa using hs⟩, fun h t ⟨A, hA, hs⟩ ↦ ?_⟩
  cases t with
  | top => exact le_top
  | coe t => exact h t A hA hs

theorem le_mul_ethickness_iff (s : Set P) (n : ℕ) (r : ℝ≥0∞) {C} (hC1 : C ≠ 0) (hC2 : C ≠ ⊤) :
    r ≤ C * ethickness 𝕜 s n ↔
    ∀ r' : ℝ≥0, ∀ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n → s ⊆ cthickening r' A
      → r ≤ C * r' := by
  simp [← ENNReal.inv_mul_le_iff hC1 hC2, le_ethickness_iff]

/-- `ethickness 𝕜 s n` is decreasing in `n` -/
theorem ethickness_antitone {s : Set P} : Antitone (ethickness 𝕜 s) := by
  intro m n hmn
  exact sInf_le_sInf fun _ ⟨A, hA, hs⟩ ↦ ⟨A, hA.trans (Nat.cast_le.mpr hmn), hs⟩

/-- `ethickness 𝕜 s n` is monotone in `s` -/
theorem ethickness_monotone : Monotone (ethickness 𝕜 (P := P)) := by
  intro s t hst n
  exact sInf_le_sInf fun _ ⟨A, hA, ht⟩ ↦ ⟨A, hA, hst.trans ht⟩

/-- Taking the closure does not change `ethickness`, since each `cthickening` is closed. -/
theorem ethickness_closure (s : Set P) (n : ℕ) :
    ethickness 𝕜 (closure s) n = ethickness 𝕜 s n := by
  apply congrArg sInf
  ext r
  exact ⟨fun ⟨A, hA, h⟩ ↦ ⟨A, hA, subset_closure.trans h⟩,
    fun ⟨A, hA, h⟩ ↦ ⟨A, hA, closure_minimal h isClosed_cthickening⟩⟩

lemma thickness_nonneg (s : Set P) (n : ℕ) : 0 ≤ thickness 𝕜 s n :=
  Real.sInf_nonneg fun _ ↦ And.left

theorem ethickness_le_of_cthickening {s : Set P} {n : ℕ} (r : ℝ≥0)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n)
    (hs : s ⊆ cthickening r A) : ethickness 𝕜 s n ≤ r :=
  sInf_le ⟨A, hA, hs⟩

theorem thickness_le_of_cthickening {s : Set P} {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n)
    (hs : s ⊆ cthickening r A) : thickness 𝕜 s n ≤ r :=
  csInf_le ⟨0, fun _ ↦ And.left⟩ ⟨hr, A, hA, hs⟩

/-- `thickness` is a lower bound for `ethickness`,
with equality on bounded sets (see `Metric.ethickness_thickness'`). -/
theorem ofReal_thickness_le_ethickness (s : Set P) (n : ℕ) :
    ENNReal.ofReal (thickness 𝕜 s n) ≤ ethickness 𝕜 s n :=
  (le_ethickness_iff ..).2 fun r _ hA hs ↦ by
    simpa using ENNReal.ofReal_le_ofReal (thickness_le_of_cthickening r.coe_nonneg hA hs)

theorem thickness_eq_zero_of_rank_le {s : Set P} {n : ℕ} (h : Module.rank 𝕜 V ≤ n) :
    thickness 𝕜 s n = 0 :=
  (thickness_nonneg ..).antisymm' <| thickness_le_of_cthickening le_rfl (A := ⊤)
    (by grind [AffineSubspace.direction_top, rank_top]) (by simp)

theorem thickness_empty [Nontrivial 𝕜] (n : ℕ) : thickness 𝕜 (∅ : Set P) n = 0 :=
  (thickness_nonneg ..).antisymm' <| thickness_le_of_cthickening le_rfl (A := ⊥)
    (by grind [AffineSubspace.direction_bot, rank_bot, zero_le]) (by simp)

theorem exists_not_mem_cthickening_of_lt_ethickness {s : Set P} {n : ℕ} {r : ℝ≥0∞}
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
    ethickness 𝕜 s n = ENNReal.ofReal (thickness 𝕜 s n) := by
  refine le_antisymm ?_ (ofReal_thickness_le_ethickness s n)
  obtain ⟨t, ht, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h.lt_top
  obtain ⟨A, hA, hs⟩ := exists_cthickening_of_ethickness_lt ht
  rw [← ENNReal.ofReal_toReal h]
  exact ENNReal.ofReal_le_ofReal <| le_csInf ⟨t, t.coe_nonneg, A, hA, hs⟩ fun r ⟨hr, A, hA, hs⟩ ↦
    ENNReal.toReal_le_of_le_ofReal hr <| ethickness_le_of_cthickening r.toNNReal hA (by simpa [hr])

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
is bounded by `r` plus the `ethickness` at rank `n` of the original set. -/
theorem ethickness_cthickening_le {s : Set P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (cthickening r s) n ≤ r + ethickness 𝕜 s n := by
  rw [← tsub_le_iff_left, le_ethickness_iff]
  intro t A hA hsA
  rw [tsub_le_iff_left]
  exact ethickness_le_of_cthickening (r + t) hA <| (cthickening_subset_of_subset r hsA).trans
    (cthickening_cthickening_subset r.coe_nonneg t.coe_nonneg _)

variable [Nontrivial 𝕜]

theorem ethickness_closedBall_le {x : P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (closedBall x r) n ≤ r := by
  simpa [cthickening_singleton, Set.subsingleton_singleton.ethickness_eq_zero]
    using ethickness_cthickening_le (𝕜 := 𝕜) (s := {x}) r n

/-- If a set is contained in a ball of radius `r`,
then its thickness is bounded by `r` at all ranks. -/
theorem ethickness_le_of_subset_closedBall {s : Set P} {x : P} (r : ℝ≥0)
    (h : s ⊆ closedBall x r) (n : ℕ) : ethickness 𝕜 s n ≤ r := by
  grw [ethickness_monotone h n, ethickness_closedBall_le]

/-- A bounded set has `ethickness` strictly less than `⊤` at every rank. -/
theorem ethickness_lt_top {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n < ⊤ := by
  obtain ⟨x⟩ : Nonempty P := inferInstance
  obtain ⟨r, -, hs⟩ := h.subset_closedBall_lt 0 x
  exact (ethickness_le_of_subset_closedBall r.toNNReal
    (hs.trans (closedBall_subset_closedBall r.le_coe_toNNReal)) n).trans_lt ENNReal.coe_lt_top

/-- A bounded set has finite `ethickness` at every rank. -/
theorem ethickness_ne_top {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n ≠ ⊤ := (ethickness_lt_top h n).ne

/-- `ethickness` and `thickness` coincide at every rank when the set is bounded. -/
theorem ethickness_thickness' {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n = ENNReal.ofReal (thickness 𝕜 s n) :=
  ethickness_eq_ofReal_thickness (ethickness_ne_top h n)

/-- `ethickness` and `thickness` coincide when the set is bounded. -/
theorem ethickness_thickness {s : Set P} (h : Bornology.IsBounded s) :
    ethickness 𝕜 s = ENNReal.ofReal ∘ thickness 𝕜 s :=
  funext (ethickness_thickness' h)

theorem toReal_ethickness {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ENNReal.toReal (ethickness 𝕜 s n) = thickness 𝕜 s n := by
  rw [ethickness_thickness' h, ENNReal.toReal_ofReal (thickness_nonneg _ _)]

/-- Taking the closure does not change `thickness` of a bounded set. -/
theorem thickness_closure {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    thickness 𝕜 (closure s) n = thickness 𝕜 s n := by
  rw [← toReal_ethickness h.closure, ← toReal_ethickness h, ethickness_closure]


/-- `thickness 𝕜 s` is monotone in `s` over bounded sets -/
theorem thickness_monotone {s t : Set P} (ht : Bornology.IsBounded t) (h : s ⊆ t) :
    thickness 𝕜 s ≤ thickness 𝕜 t := by
  intro n
  rw [← toReal_ethickness ht, ← toReal_ethickness (ht.subset h)]
  exact ENNReal.toReal_mono (ethickness_ne_top ht n) (ethickness_monotone h n)

/-- Provided that `s` is bounded, `thickness 𝕜 s n` is decreasing in `n` -/
theorem thickness_antitone {s : Set P} (hs : Bornology.IsBounded s) {m n : ℕ} (h : m ≤ n) :
    thickness 𝕜 s n ≤ thickness 𝕜 s m := by
  rw [← toReal_ethickness hs, ← toReal_ethickness hs]
  exact ENNReal.toReal_mono (ethickness_ne_top hs m) (ethickness_antitone h)

theorem thickness_closedBall_le {x : P} {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    thickness 𝕜 (closedBall x r) n ≤ r := by
  exact thickness_le_of_cthickening hr (A := affineSpan 𝕜 {x})
    (by grind [direction_affineSpan, vectorSpan_singleton, rank_bot, zero_le])
    (closedBall_subset_cthickening (by simp) _)

/-- If a set is contained in a ball of radius `r`,
then its thickness is bounded by `r` at all ranks. -/
theorem thickness_le_of_subset_closedBall {s : Set P} {x : P} {r : ℝ}
    (h : s ⊆ closedBall x r) (hr : 0 ≤ r) (n : ℕ) : thickness 𝕜 s n ≤ r := by
  grw [thickness_monotone isBounded_closedBall h n, thickness_closedBall_le hr]

/-- A variant of `thickness_le_of_subset_closedBall` -/
theorem thickness_le_of_subset_closedBall_of_nonempty {s : Set P} {x : P} {r : ℝ}
    (h : s ⊆ closedBall x r) (hs : s.Nonempty) : ∀ n : ℕ, thickness 𝕜 s n ≤ r :=
  thickness_le_of_subset_closedBall h (nonempty_closedBall.1 (hs.mono h))

end PseudoMetricSpace

end Ring

section DivisionRing

variable {𝕜} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [PseudoEMetricSpace P]

theorem ethickness_eq_zero_of_finrank_le [FiniteDimensional 𝕜 V] {s : Set P} {n : ℕ}
    (h : Module.finrank 𝕜 V ≤ n) :
    ethickness 𝕜 s n = 0 :=
  nonpos_iff_eq_zero.1 <| ethickness_le_of_cthickening 0 (A := ⊤)
    (by grind [AffineSubspace.direction_top, rank_top, Module.finrank_eq_rank', Nat.cast_le])
    (by simp)

end DivisionRing

end Metric
