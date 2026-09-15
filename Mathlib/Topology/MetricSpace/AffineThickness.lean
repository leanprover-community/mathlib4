/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
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
  refine ⟨fun h r' A hA hs => ?_, ?_⟩
  · exact h r' ⟨A, hA, by simpa using hs⟩
  · rintro h t ⟨A, hA, hs⟩
    rcases eq_or_ne t ⊤ with rfl | ht
    · exact le_top
    · lift t to ℝ≥0 using ht with u
      exact h u A hA hs

theorem le_mul_ethickness_iff (s : Set P) (n : ℕ) (r : ℝ≥0∞) {C} (hC1 : C ≠ 0) (hC2 : C ≠ ⊤) :
    r ≤ C * ethickness 𝕜 s n ↔
    ∀ r' : ℝ≥0, ∀ A : AffineSubspace 𝕜 P, Module.rank 𝕜 A.direction ≤ n → s ⊆ cthickening r' A
      → r ≤ C * r' := by
  simp [← ENNReal.inv_mul_le_iff hC1 hC2, le_ethickness_iff]

/-- `ethickness 𝕜 s n` is decreasing in `n` -/
theorem ethickness_antitone {s : Set P} : Antitone (ethickness 𝕜 s) := by
  intro m n hmn
  exact sInf_le_sInf (fun r ⟨A, hA, hs⟩ => ⟨A, hA.trans (Nat.cast_le.mpr hmn), hs⟩)

/-- `ethickness 𝕜 s n` is monotone in `s` -/
theorem ethickness_monotone : Monotone (ethickness 𝕜 (P := P)) := by
  intro s t hst n
  exact sInf_le_sInf (fun r ⟨A, hA, ht⟩ => ⟨A, hA, hst.trans ht⟩)

/-- Taking the closure does not change `ethickness`, since each `cthickening` is closed. -/
theorem ethickness_closure (s : Set P) (n : ℕ) :
    ethickness 𝕜 (closure s) n = ethickness 𝕜 s n := by
  apply congrArg sInf
  ext r
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun ⟨A, hA, hsub⟩ => ⟨A, hA, subset_closure.trans hsub⟩,
    fun ⟨A, hA, hsub⟩ => ⟨A, hA, closure_minimal hsub isClosed_cthickening⟩⟩

lemma thickness_nonneg (s : Set P) (n : ℕ) :
    0 ≤ thickness 𝕜 s n := by
  unfold thickness
  apply Real.sInf_nonneg
  intro r ⟨hr, _⟩
  exact hr

theorem thickness_eq_zero_of_rank_le {s : Set P} {n : ℕ} (h : Module.rank 𝕜 V ≤ n) :
    thickness 𝕜 s n = 0 := by
  apply le_antisymm
  · apply csInf_le ⟨0, fun _ ↦ And.left⟩
    constructor
    · trivial
    · use ⊤
      constructor
      · rwa [AffineSubspace.direction_top, rank_top]
      · simp
  · apply thickness_nonneg

theorem thickness_empty [Nontrivial 𝕜] (n : ℕ) :
    thickness 𝕜 (∅ : Set P) n = 0 := by
  apply le_antisymm
  · apply csInf_le ⟨0, fun _ ↦ And.left⟩
    refine ⟨le_refl 0, ⊥, ?_, Set.empty_subset _⟩
    rw [AffineSubspace.direction_bot]
    calc Module.rank 𝕜 (⊥ : Submodule 𝕜 V)
        = 0 := by
          rw [rank_eq_zero_iff]
          intro x; use 1
          simp only [ne_eq, one_ne_zero, not_false_eq_true, one_smul, true_and]
          exact Submodule.eq_zero_of_bot_submodule x
      _ ≤ _ := by simp
  · exact thickness_nonneg _ _

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
  refine ⟨A, hA, hsA.trans (cthickening_mono ?_ _)⟩
  exact_mod_cast hr'.le

end

section
variable
  {𝕜} [Ring 𝕜] [Nontrivial 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V]
  {P} [AddTorsor V P] [PseudoMetricSpace P]

theorem ethickness_closedBall_le {x : P} (r : ℝ≥0) (n : ℕ) :
    ethickness 𝕜 (closedBall x r) n ≤ r := by
  apply sInf_le
  use affineSpan 𝕜 {x}
  constructor
  · rw [direction_affineSpan, vectorSpan_singleton]
    simp
  · apply closedBall_subset_cthickening
    simp

/-- If a set is contained in a ball of radius `r`,
then its thickness is bounded by `r` at all ranks. -/
theorem ethickness_le_of_subset_closedBall {s : Set P} {x : P} (r : ℝ≥0)
    (h : s ⊆ closedBall x r) (n : ℕ) : ethickness 𝕜 s n ≤ r := by
  trans ethickness 𝕜 (closedBall x r) n
  · apply ethickness_monotone h
  · apply ethickness_closedBall_le

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
  apply ethickness_le_of_cthickening (r + δ) hA
  apply (cthickening_subset_of_subset r hsA).trans
  rw [NNReal.coe_add, ENNReal.coe_toReal]
  apply cthickening_cthickening_subset r.coe_nonneg δ.coe_nonneg

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
    use r
    constructor
    · linarith
    · use affineSpan 𝕜 {x}
      constructor
      · rw [direction_affineSpan, vectorSpan_singleton]
        simp
      · apply hs.trans
        apply closedBall_subset_cthickening
        simp
  have hbdd : BddBelow R := by use 0; intro r hr; exact hr.1
  have h₂ : ENNReal.ofReal '' R ⊆ eR := by
    intro t ⟨r, hr, ht⟩
    obtain ⟨hr, A, hA⟩ := hr
    use A
    convert hA
    simpa [← ht]
  apply le_antisymm
  · convert sInf_le_sInf h₂
    apply ENNReal.ofReal_mono.map_csInf_of_continuousAt (A_nonemp := h) (A_bdd := hbdd)
    apply ENNReal.continuous_ofReal.continuousAt
  · apply le_sInf
    intro t hr
    by_cases ht : t = ⊤
    · simp [ht]
    · have ht' := ENNReal.ofReal_toReal ht
      rw [← ht']
      simp only [ENNReal.toReal_nonneg, ENNReal.ofReal_le_ofReal_iff]
      apply csInf_le hbdd
      constructor
      · positivity
      · exact hr

theorem ethickness_thickness' {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n = ENNReal.ofReal (thickness 𝕜 s n) := by
  rw [ethickness_thickness h]
  simp

theorem toReal_ethickness {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ENNReal.toReal (ethickness 𝕜 s n) = thickness 𝕜 s n := by
  rw [ethickness_thickness' h]
  rw [ENNReal.toReal_ofReal]
  exact thickness_nonneg _ _

/-- Taking the closure does not change `thickness` of a bounded set. -/
theorem thickness_closure {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    thickness 𝕜 (closure s) n = thickness 𝕜 s n := by
  have := ethickness_closure (𝕜 := 𝕜) s n
  rw [ethickness_thickness' h.closure, ethickness_thickness' h] at this
  exact (ENNReal.ofReal_le_ofReal_iff (thickness_nonneg s n)).mp this.le
    |>.antisymm <| (ENNReal.ofReal_le_ofReal_iff (thickness_nonneg _ n)).mp this.ge

/-- A bounded set has finite `ethickness` at every rank. -/
theorem ethickness_ne_top {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n ≠ ⊤ := by
  rw [ethickness_thickness' h]; exact ENNReal.ofReal_ne_top

/-- A bounded set has `ethickness` strictly less than `⊤` at every rank. -/
theorem ethickness_lt_top {s : Set P} (h : Bornology.IsBounded s) (n : ℕ) :
    ethickness 𝕜 s n < ⊤ := (ethickness_ne_top h n).lt_top

/-- `thickness 𝕜 s` is monotone in `s` over bounded sets -/
theorem thickness_monotone {s t : Set P} (ht : Bornology.IsBounded t) (h : s ⊆ t) :
    thickness 𝕜 s ≤ thickness 𝕜 t := by
  intro n
  rw [← ENNReal.ofReal_le_ofReal_iff]
  · rw [← ethickness_thickness' ht n]
    rw [← ethickness_thickness' (ht.subset h) n]
    apply ethickness_monotone h
  · apply thickness_nonneg

/-- Provided that `s` is bounded, `thickness 𝕜 s n` is decreasing in `n` -/
theorem thickness_antitone {s : Set P} (hs : Bornology.IsBounded s) {m n : ℕ} (h : m ≤ n) :
    thickness 𝕜 s n ≤ thickness 𝕜 s m := by
  rw [← ENNReal.ofReal_le_ofReal_iff]
  · repeat rw [← ethickness_thickness' hs]
    apply ethickness_antitone h
  · apply thickness_nonneg

theorem thickness_closedBall_le {x : P} {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    thickness 𝕜 (closedBall x r) n ≤ r := by
  set R := { ε : ℝ | 0 ≤ ε ∧ ∃ A : AffineSubspace 𝕜 P,
    Module.rank 𝕜 A.direction ≤ n ∧ (closedBall x r) ⊆ cthickening ε A }
  have hbdd : BddBelow R := ⟨0, fun _ ↦ And.left⟩
  apply csInf_le hbdd
  constructor
  · assumption
  · use affineSpan 𝕜 {x}
    constructor
    · rw [direction_affineSpan, vectorSpan_singleton]
      simp
    · apply closedBall_subset_cthickening
      simp

/-- If a set is contained in a ball of radius `r`,
then its thickness is bounded by `r` at all ranks. -/
theorem thickness_le_of_subset_closedBall {s : Set P} {x : P} {r : ℝ}
    (h : s ⊆ closedBall x r) (hr : 0 ≤ r) (n : ℕ) : thickness 𝕜 s n ≤ r := by
  trans thickness 𝕜 (closedBall x r) n
  · apply thickness_monotone isBounded_closedBall h
  · apply thickness_closedBall_le hr

/-- A variant of `thickness_le_of_subset_closedBall` -/
theorem thickness_le_of_subset_closedBall_of_nonempty {s : Set P} {x : P} {r : ℝ}
    (h : s ⊆ closedBall x r) (hs : s.Nonempty) : ∀ n : ℕ, thickness 𝕜 s n ≤ r := by
  suffices hr : 0 ≤ r from thickness_le_of_subset_closedBall h hr
  rw [← nonempty_closedBall (x := x) (ε := r)]
  exact hs.mono h

end

section FiniteDimensional
variable
  {𝕜} [DivisionRing 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  {P} [AddTorsor V P] [PseudoEMetricSpace P]

theorem ethickness_eq_zero_of_finrank_le {s : Set P} {n : ℕ} (h : Module.finrank 𝕜 V ≤ n) :
    ethickness 𝕜 s n = 0 := by
  rw [← bot_eq_zero, eq_bot_iff, bot_eq_zero]
  apply sInf_le
  · use ⊤
    constructor
    · rw [AffineSubspace.direction_top, rank_top]
      rw [← Module.finrank_eq_rank']
      exact_mod_cast h
    · simp

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
  simp only [Finset.le_inf_iff, Finset.mem_range]
  constructor
  · intro h n
    exact h n.val n.prop
  · intro h n hn
    exact h ⟨n, hn⟩

/-- If `r : ℝ≥0` strictly exceeds `ethickness.scale 𝕜 s`, then `s` is contained in the
closed `r`-neighborhood of some affine subspace of codimension `1` in `V`. -/
theorem ethickness.exists_cthickening_of_scale_lt [Nontrivial V] {s : Set P} {r : ℝ≥0}
    (hr : ethickness.scale 𝕜 s < r) :
    ∃ A : AffineSubspace 𝕜 P, Nonempty A ∧
      Module.finrank 𝕜 V = Module.finrank 𝕜 A.direction + 1 ∧ s ⊆ cthickening r A := by
  rw [scale_eq] at hr
  obtain ⟨A, hA, hsA⟩ := exists_cthickening_of_ethickness_lt hr
  have hV : 0 < Module.finrank 𝕜 V := Module.finrank_pos
  have hA' : Module.finrank 𝕜 A.direction ≤ Module.finrank 𝕜 V - 1 :=
    Module.finrank_le_of_rank_le hA
  by_cases hAbot : A = ⊥
  · subst hAbot
    rw [AffineSubspace.bot_coe, Metric.cthickening_empty] at hsA
    have hs : s = ∅ := Set.subset_eq_empty hsA rfl
    obtain ⟨x⟩ : Nonempty P := inferInstance
    obtain ⟨W, -, hW⟩ := (⊥ : Submodule 𝕜 V).exists_le_finrank_eq
      (k := Module.finrank 𝕜 V - 1) (by simp) (Nat.sub_le _ _)
    refine ⟨AffineSubspace.mk' x W, ⟨⟨x, AffineSubspace.self_mem_mk' x W⟩⟩, ?_, ?_⟩
    · rw [AffineSubspace.direction_mk', hW]
      exact (Nat.sub_add_cancel hV).symm
    · rw [hs]; exact Set.empty_subset _
  · obtain ⟨x, hxA⟩ : (A : Set P).Nonempty :=
      (AffineSubspace.nonempty_iff_ne_bot A).mpr hAbot
    obtain ⟨W, hAW, hW⟩ := A.direction.exists_le_finrank_eq hA' (Nat.sub_le _ _)
    refine ⟨AffineSubspace.mk' x W, ⟨⟨x, AffineSubspace.self_mem_mk' x W⟩⟩, ?_, ?_⟩
    · rw [AffineSubspace.direction_mk', hW]
      exact (Nat.sub_add_cancel hV).symm
    · have hle : A ≤ AffineSubspace.mk' x W := fun p hp => by
        rw [AffineSubspace.mem_mk']
        exact hAW ((AffineSubspace.vsub_right_mem_direction_iff_mem hxA p).mpr hp)
      exact hsA.trans (Metric.cthickening_subset_of_subset _ (SetLike.coe_subset_coe.mpr hle))

end FiniteDimensional

end Metric

theorem Set.Subsingleton.ethickness_eq_zero {𝕜} [Ring 𝕜] [Nontrivial 𝕜]
    {V} [AddCommGroup V] [Module 𝕜 V]
    {P} [AddTorsor V P] [PseudoEMetricSpace P]
    {s : Set P} (hs : s.Subsingleton) (n) :
    Metric.ethickness 𝕜 s n = 0 := by
  rcases hs.eq_empty_or_singleton with hs | ⟨x, hs⟩
  · simp [hs]
  · apply csInf_eq_bot_of_bot_mem
    simp only [bot_eq_zero', Set.mem_ofPred_eq]
    use AffineSubspace.mk' x ⊥
    rw [AffineSubspace.direction_mk']
    constructor
    · simp
    · simp only [ENNReal.toReal_zero, Metric.cthickening_zero, hs, Set.singleton_subset_iff]
      apply subset_closure
      apply AffineSubspace.self_mem_mk'

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
  set δ : ℝ := Metric.thickness 𝕜 s n + ε
  have hthick : 0 ≤ Metric.thickness 𝕜 s n := Metric.thickness_nonneg s n
  have hδ : 0 < δ := by positivity
  set r : ℝ≥0 := δ.toNNReal with hr_def
  have hr_coe : (r : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have hscale_lt : Metric.ethickness.scale 𝕜 s < r := by
    rw [Metric.ethickness.scale_eq]
    have hsub : Module.finrank 𝕜 V - 1 = n := by omega
    rw [hsub, Metric.ethickness_thickness' h n,
      show ((r : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal δ from by
        rw [← hr_coe]; exact ENNReal.ofReal_coe_nnreal.symm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hthick).mpr (by linarith)
  obtain ⟨A, hAne, hAfr, hsA⟩ := Metric.ethickness.exists_cthickening_of_scale_lt hscale_lt
  exact ⟨A, hAne, by omega, hr_coe ▸ hsA⟩
