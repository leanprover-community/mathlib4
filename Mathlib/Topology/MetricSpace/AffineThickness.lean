/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team, Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Thickness of a set in an affine space

For a set `s` in a metric affine space and a natural number `n`, the `n`-th thickness of `s`
measures how well `s` can be approximated by an affine subspace of rank at most `n`: it is the
infimal radius `r` such that `s` is contained in the closed `r`-thickening of some affine subspace
of rank at most `n`. The set is not assumed to be convex.

## Main definitions

* `Metric.ethickness 𝕜 s n`: the `ℝ≥0∞`-valued thickness of `s` at rank `n`.
* `Metric.thickness 𝕜 s n`: the `ℝ`-valued thickness of `s` at rank `n`.
* `Metric.ethickness.scale 𝕜 s`: the smallest of the `ethickness`es of `s` at the ranks
  `0, …, finrank 𝕜 V - 1`, i.e. the thickness of `s` at the largest relevant rank.

## Main results

* `Metric.ethickness_antitone`, `Metric.ethickness_monotone`: `ethickness` decreases in the rank
  and increases in the set.
* `Metric.ethickness_thickness`: over a bounded set the two variants agree.
* `Metric.ethickness_cthickening_le`: thickening a set by `r` increases its `ethickness`
  by at most `r`.
* `Metric.ethickness.exists_cthickening_of_scale_lt`: a set whose `scale` is less than `r` is
  contained in the closed `r`-thickening of an affine subspace of codimension `1`.

## Implementation notes

We deviate slightly from [GWZ]: `ethickness` is ordered decreasingly in the rank, as opposed to
[GWZ]. The smallest thickness of a set in a nontrivial space is
`Metric.ethickness ℝ s (Module.finrank ℝ E - 1)`, available as `Metric.ethickness.scale` for ease
of use.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Metric

/--
The `ethickness` of a set `s` at rank `n`
is the infimal radius `r` such that `s` is contained in the `r`-thickening
of a rank `n` affine subspace.

Thus, `ethickness` is decreasing in `n`.
-/
noncomputable def ethickness 𝕜 [Ring 𝕜] {V} [AddCommGroup V] [Module 𝕜 V]
    {P} [AddTorsor V P] [PseudoEMetricSpace P] (s : Set P) (n : ℕ) : ℝ≥0∞ :=
  sInf { r | ∃ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r.toReal A }

/-- The real-valued `n`-thickness of a set `s`: the infimum of radii `r ≥ 0` for which `s`
is contained in the `r`-thickening of some affine subspace of dimension at most `n`. This is
the `ℝ`-valued counterpart of `ethickness`. -/
noncomputable def thickness 𝕜 [Ring 𝕜] {V} [AddCommGroup V] [Module 𝕜 V]
    {P} [AddTorsor V P] [PseudoEMetricSpace P] (s : Set P) (n : ℕ) : ℝ :=
  sInf { r | 0 ≤ r ∧ ∃ A : AffineSubspace 𝕜 P,
    Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r A }

/-- `ethickness.scale 𝕜 s` in a finite-dimensional space is the smallest of the thicknesses
(`ethickness`) of `s`. -/
noncomputable abbrev ethickness.scale 𝕜 [DivisionRing 𝕜] {V} [AddCommGroup V] [Module 𝕜 V]
    {P} [AddTorsor V P] [PseudoEMetricSpace P] (s : Set P) : ℝ≥0∞ :=
  (Finset.range (Module.finrank 𝕜 V)).inf <| ethickness 𝕜 s

section
variable
  {𝕜} [Ring 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V]
  {P} [AddTorsor V P] [PseudoEMetricSpace P]

@[simp]
theorem ethickness_empty [Nontrivial 𝕜] (n : ℕ) : ethickness 𝕜 (∅ : Set P) n = 0 := by
  simp only [ethickness, Set.empty_subset, and_true]
  apply csInf_eq_bot_of_bot_mem
  simp only [bot_eq_zero', Set.mem_ofPred_eq]
  use ⊥
  rw [AffineSubspace.direction_bot, rank_bot]
  apply zero_le

theorem le_ethickness_iff (s : Set P) (n : ℕ) (r : ℝ≥0∞) : r ≤ ethickness 𝕜 s n ↔
    ∀ r' : ℝ≥0, ∀ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n → s ⊆ cthickening r' A
      → r ≤ r' := by
  rw [ethickness, le_sInf_iff]
  refine ⟨fun h r' A hA hs => h r' ⟨A, hA, by simpa using hs⟩, ?_⟩
  rintro h t ⟨A, hA, hs⟩
  rcases eq_or_ne t ⊤ with rfl | ht
  · exact le_top
  lift t to ℝ≥0 using ht with u
  exact h u A hA hs

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

lemma thickness_nonneg (s : Set P) (n : ℕ) :
    0 ≤ thickness 𝕜 s n := by
  exact Real.sInf_nonneg fun _ ↦ And.left

theorem thickness_eq_zero_of_rank_le {s : Set P} {n : ℕ} (h : Module.rank 𝕜 V ≤ n) :
    thickness 𝕜 s n = 0 := by
  refine le_antisymm ?_ (thickness_nonneg _ _)
  refine csInf_le ⟨0, fun _ ↦ And.left⟩ ⟨le_rfl, ⊤, ?_, by simp⟩
  rwa [AffineSubspace.direction_top, rank_top]

theorem thickness_empty [Nontrivial 𝕜] (n : ℕ) :
    thickness 𝕜 (∅ : Set P) n = 0 := by
  refine le_antisymm ?_ (thickness_nonneg _ _)
  refine csInf_le ⟨0, fun _ ↦ And.left⟩ ⟨le_rfl, ⊥, ?_, Set.empty_subset _⟩
  rw [AffineSubspace.direction_bot, rank_bot]; exact zero_le

theorem ethickness_le_of_cthickening {s : Set P} {n : ℕ} (r : ℝ≥0)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n)
    (hs : s ⊆ cthickening r A) : ethickness 𝕜 s n ≤ r :=
  sInf_le ⟨A, hA, hs⟩

theorem thickness_le_of_cthickening {s : Set P} {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n)
    (hs : s ⊆ cthickening r A) : thickness 𝕜 s n ≤ r :=
  csInf_le ⟨0, fun _ ↦ And.left⟩ ⟨hr, A, hA, hs⟩

theorem exists_not_mem_cthickening_of_lt_ethickness {s : Set P} {n : ℕ} {r : ℝ≥0∞}
    (hr : r < ethickness 𝕜 s n)
    {A : AffineSubspace 𝕜 P} (hA : Module.rank 𝕜 A.direction ≤ n) :
    ∃ x ∈ s, x ∉ cthickening r.toReal (A : Set P) := by_contra fun h ↦
  (not_lt.2 <| ENNReal.coe_toNNReal hr.ne_top ▸ ethickness_le_of_cthickening
    r.toNNReal hA (fun x hx ↦ not_not.mp fun hxc ↦ h ⟨x, hx, hxc⟩)) hr

/-- If `r : ℝ≥0` strictly exceeds `ethickness 𝕜 s n`, then `s` is contained in the
closed `r`-neighborhood of some affine subspace of rank at most `n`. -/
theorem exists_cthickening_of_ethickness_lt {s : Set P} {n : ℕ} {r : ℝ≥0}
    (hr : ethickness 𝕜 s n < r) :
    ∃ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r A := by
  rw [← not_le, le_ethickness_iff] at hr
  push Not at hr
  obtain ⟨r', A, hA, hsA, hr'⟩ := hr
  exact ⟨A, hA, hsA.trans (cthickening_mono (mod_cast hr'.le) _)⟩

end

section
variable
  {𝕜} [Ring 𝕜] [Nontrivial 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V]
  {P} [AddTorsor V P] [PseudoMetricSpace P]

theorem ethickness_closedBall_le {x : P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (closedBall x r) n ≤ r := by
  refine ethickness_le_of_cthickening r (A := affineSpan 𝕜 {x}) ?_
    (closedBall_subset_cthickening (by simp) _)
  rw [direction_affineSpan, vectorSpan_singleton, rank_bot]; exact zero_le

/-- If a set is contained in a ball of radius `r`,
then its thickness is bounded by `r` at all ranks. -/
theorem ethickness_le_of_subset_closedBall {s : Set P} {x : P} (r : ℝ≥0)
    (h : s ⊆ closedBall x r) (n : ℕ) : ethickness 𝕜 s n ≤ r := by
  grw [ethickness_monotone h n, ethickness_closedBall_le]

omit [Nontrivial 𝕜] in
/-- The `ethickness` at rank `n` of the `r`-thickening of a set is bounded by `r` plus the
`ethickness` at rank `n` of the original set.

Proof idea: if `s ⊆ cthickening δ A` for an affine subspace `A` of rank ≤ `n`, then
`cthickening r s ⊆ cthickening r (cthickening δ A) ⊆ cthickening (r + δ) A` by
`Metric.cthickening_cthickening_subset`. Hence `ethickness 𝕜 (cthickening r s) n ≤ r + δ`
for any such `δ`, giving the inequality after taking the infimum over `δ`. -/
theorem ethickness_cthickening_le {s : Set P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (cthickening r s) n ≤ r + ethickness 𝕜 s n := by
  rw [show ethickness 𝕜 s n = sInf _ from rfl, ENNReal.add_sInf]
  apply le_iInf₂
  rintro t ⟨A, hA, hsA⟩
  rcases eq_or_ne t ⊤ with rfl | ht_top
  · simp
  lift t to ℝ≥0 using ht_top with δ
  exact ethickness_le_of_cthickening (r + δ) hA <| (cthickening_subset_of_subset r hsA).trans
    (cthickening_cthickening_subset r.coe_nonneg δ.coe_nonneg _)

/-- `ethickness` and `thickness` coincide when the set is bounded. -/
theorem ethickness_thickness {s : Set P} (h : Bornology.IsBounded s) :
    (ethickness 𝕜 s) = ENNReal.ofReal ∘ (thickness 𝕜 s) := by
  funext n
  unfold thickness ethickness
  simp only [Function.comp_apply]
  set R := { r : ℝ | 0 ≤ r ∧ ∃ A : AffineSubspace 𝕜 P,
    Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r A }
  set eR := { r : ℝ≥0∞ | ∃ A : AffineSubspace 𝕜 P,
    Module.rank 𝕜 A.direction ≤ n ∧ s ⊆ cthickening r.toReal A }
  replace h : R.Nonempty := by
    obtain ⟨x⟩ : Nonempty P := inferInstance
    obtain ⟨r, hr, hs⟩ := h.subset_closedBall_lt 0 x
    refine ⟨r, hr.le, affineSpan 𝕜 {x}, ?_, hs.trans (closedBall_subset_cthickening (by simp) _)⟩
    rw [direction_affineSpan, vectorSpan_singleton, rank_bot]; exact zero_le
  have hbdd : BddBelow R := ⟨0, fun _ ↦ And.left⟩
  have h₂ : ENNReal.ofReal '' R ⊆ eR := by
    rintro _ ⟨r, ⟨hr, A, hA, hs⟩, rfl⟩
    exact ⟨A, hA, by simpa [hr]⟩
  refine le_antisymm ?_ (le_sInf fun t hr ↦ ?_)
  · convert sInf_le_sInf h₂
    exact ENNReal.ofReal_mono.map_csInf_of_continuousAt
      ENNReal.continuous_ofReal.continuousAt h hbdd
  · rcases eq_or_ne t ⊤ with rfl | ht
    · exact le_top
    lift t to ℝ≥0 using ht
    simpa using csInf_le hbdd ⟨t.coe_nonneg, hr⟩

theorem ethickness_thickness' {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n = ENNReal.ofReal (thickness 𝕜 s n) := by
  simp [ethickness_thickness h]

theorem toReal_ethickness {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ENNReal.toReal (ethickness 𝕜 s n) = thickness 𝕜 s n := by
  rw [ethickness_thickness' h, ENNReal.toReal_ofReal (thickness_nonneg _ _)]

/-- Taking the closure does not change `thickness` of a bounded set. -/
theorem thickness_closure {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    thickness 𝕜 (closure s) n = thickness 𝕜 s n := by
  rw [← toReal_ethickness h.closure, ← toReal_ethickness h, ethickness_closure]

/-- A bounded set has finite `ethickness` at every rank. -/
theorem ethickness_ne_top {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n ≠ ⊤ := by
  simp [ethickness_thickness' h]

/-- A bounded set has `ethickness` strictly less than `⊤` at every rank. -/
theorem ethickness_lt_top {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n < ⊤ := (ethickness_ne_top h n).lt_top

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
  refine thickness_le_of_cthickening hr (A := affineSpan 𝕜 {x}) ?_
    (closedBall_subset_cthickening (by simp) _)
  rw [direction_affineSpan, vectorSpan_singleton, rank_bot]; exact zero_le

/-- If a set is contained in a ball of radius `r`,
then its thickness is bounded by `r` at all ranks. -/
theorem thickness_le_of_subset_closedBall {s : Set P} {x : P} {r : ℝ}
    (h : s ⊆ closedBall x r) (hr : 0 ≤ r) (n : ℕ) : thickness 𝕜 s n ≤ r := by
  grw [thickness_monotone isBounded_closedBall h n, thickness_closedBall_le hr]

/-- A variant of `thickness_le_of_subset_closedBall` -/
theorem thickness_le_of_subset_closedBall_of_nonempty {s : Set P} {x : P} {r : ℝ}
    (h : s ⊆ closedBall x r) (hs : s.Nonempty) : ∀ n : ℕ, thickness 𝕜 s n ≤ r := by
  exact thickness_le_of_subset_closedBall h (nonempty_closedBall.1 (hs.mono h))

end

section FiniteDimensional
variable
  {𝕜} [DivisionRing 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  {P} [AddTorsor V P] [PseudoEMetricSpace P]

theorem ethickness_eq_zero_of_finrank_le {s : Set P} {n : ℕ} (h : Module.finrank 𝕜 V ≤ n) :
    ethickness 𝕜 s n = 0 := by
  refine nonpos_iff_eq_zero.1 <| ethickness_le_of_cthickening 0 (A := ⊤) ?_ (by simp)
  rw [AffineSubspace.direction_top, rank_top, ← Module.finrank_eq_rank']
  exact_mod_cast h

omit [FiniteDimensional 𝕜 V] in
theorem ethickness.scale_le {n} (s : Set P) (hn : n < Module.finrank 𝕜 V) :
    ethickness.scale 𝕜 s ≤ ethickness 𝕜 s n := Finset.inf_le (Finset.mem_range.mpr hn)

theorem ethickness.scale_eq [Nontrivial V] (s : Set P) :
    ethickness.scale 𝕜 s = ethickness 𝕜 s (Module.finrank 𝕜 V - 1) :=
  le_antisymm (Finset.inf_le <| Finset.mem_range.2 <| Nat.sub_one_lt
    (Module.finrank_pos_iff_of_free _ _|>.2 inferInstance).ne') <| Finset.le_inf fun _ hn ↦
    ethickness_antitone <| Nat.le_sub_one_of_lt (Finset.mem_range.1 hn)

omit [FiniteDimensional 𝕜 V] in
theorem ethickness.le_scale_iff (s : Set P) {δ : ℝ≥0} :
    δ ≤ ethickness.scale 𝕜 s ↔
      ∀ n : Fin (Module.finrank 𝕜 V), δ ≤ ethickness 𝕜 s n := by
  simp [Fin.forall_iff]

/-- If `r : ℝ≥0` strictly exceeds `ethickness.scale 𝕜 s`, then `s` is contained in the
closed `r`-neighborhood of some affine subspace of codimension `1` in `V`. -/
theorem ethickness.exists_cthickening_of_scale_lt [Nontrivial V] {s : Set P} {r : ℝ≥0}
    (hr : ethickness.scale 𝕜 s < r) :
    ∃ A : AffineSubspace 𝕜 P, Nonempty A ∧
      Module.finrank 𝕜 V = Module.finrank 𝕜 A.direction + 1 ∧ s ⊆ cthickening r A := by
  rw [scale_eq] at hr
  obtain ⟨A, hA, hsA⟩ := exists_cthickening_of_ethickness_lt hr
  obtain ⟨W, hAW, hW⟩ := A.direction.exists_le_finrank_eq
    (Module.finrank_le_of_rank_le hA) (Nat.sub_le _ _)
  obtain ⟨x, hx⟩ : ∃ x : P, s ⊆ cthickening r (AffineSubspace.mk' x W) := by
    rcases (A : Set P).eq_empty_or_nonempty with hAe | ⟨x, hxA⟩
    · exact ⟨Classical.arbitrary P, by simp_all⟩
    refine ⟨x, hsA.trans (cthickening_subset_of_subset _ fun p hp ↦ ?_)⟩
    rw [SetLike.mem_coe, AffineSubspace.mem_mk']
    exact hAW ((AffineSubspace.vsub_right_mem_direction_iff_mem hxA p).2 hp)
  have : 0 < Module.finrank 𝕜 V := Module.finrank_pos (R := 𝕜) (M := V)
  refine ⟨_, ⟨⟨x, AffineSubspace.self_mem_mk' x W⟩⟩, ?_, hx⟩
  rw [AffineSubspace.direction_mk', hW]
  omega

end FiniteDimensional

end Metric

theorem Set.Subsingleton.ethickness_eq_zero {𝕜} [Ring 𝕜] [Nontrivial 𝕜]
    {V} [AddCommGroup V] [Module 𝕜 V]
    {P} [AddTorsor V P] [PseudoEMetricSpace P]
    {s : Set P} (hs : s.Subsingleton) (n) :
    Metric.ethickness 𝕜 s n = 0 := by
  rcases hs.eq_empty_or_singleton with hs | ⟨x, hs⟩
  · simp [hs]
  · refine nonpos_iff_eq_zero.1 <|
      Metric.ethickness_le_of_cthickening 0 (A := .mk' x ⊥)
      (by rw [AffineSubspace.direction_mk', rank_bot]; exact zero_le) ?_
    rw [hs, Set.singleton_subset_iff]
    exact Metric.self_subset_cthickening _ (AffineSubspace.self_mem_mk' x _)

/-- A variant of `Metric.ethickness.exists_cthickening_of_scale_lt` -/
theorem Bornology.IsBounded.exists_cthickening_thickness {𝕜} [DivisionRing 𝕜]
    {V} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    {P} [AddTorsor V P] [PseudoMetricSpace P]
    {n} (hV : Module.finrank 𝕜 V = n + 1)
    {s : Set P} (h : IsBounded s) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : AffineSubspace 𝕜 P, Nonempty A ∧
      Module.finrank 𝕜 A.direction = n ∧
        s ⊆ Metric.cthickening (Metric.thickness 𝕜 s n + ε) A := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have hδ := add_nonneg (Metric.thickness_nonneg (𝕜 := 𝕜) s n) hε.le
  obtain ⟨A, hAne, hAfr, hsA⟩ := Metric.ethickness.exists_cthickening_of_scale_lt (𝕜 := 𝕜)
    (r := (Metric.thickness 𝕜 s n + ε).toNNReal) (s := s) <| by
    rw [Metric.ethickness.scale_eq, hV, Nat.add_sub_cancel, Metric.ethickness_thickness' h n]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Metric.thickness_nonneg _ _)).2 (by linarith)
  exact ⟨A, hAne, by omega, Real.coe_toNNReal _ hδ ▸ hsA⟩
