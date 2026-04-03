/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Absolutely Continuous Functions

This file defines absolutely continuous functions on a closed interval `uIcc a b` and proves some
basic properties about absolutely continuous functions.

A function `f` is *absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such
that for any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`,
`b i` are all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`.

We give a filter version of the definition of absolutely continuous functions in
`AbsolutelyContinuousOnInterval` based on `AbsolutelyContinuousOnInterval.totalLengthFilter`
and `AbsolutelyContinuousOnInterval.disjWithin` and prove its equivalence with the `ε`-`δ`
definition in `absolutelyContinuousOnInterval_iff`.

We use the filter version to prove that absolutely continuous functions are closed under
* addition - `AbsolutelyContinuousOnInterval.add`;
* negation - `AbsolutelyContinuousOnInterval.neg`;
* subtraction - `AbsolutelyContinuousOnInterval.sub`;
* scalar multiplication - `AbsolutelyContinuousOnInterval.const_smul`,
  `AbsolutelyContinuousOnInterval.const_mul`;
* multiplication - `AbsolutelyContinuousOnInterval.smul`,
  `AbsolutelyContinuousOnInterval.mul`;

and that absolutely continuous implies uniformly continuous in
`AbsolutelyContinuousOnInterval.uniformContinuousOn`.

We use the `ε`-`δ` definition to prove that
* Lipschitz continuous functions are absolutely continuous -
  `LipschitzOnWith.absolutelyContinuousOnInterval`;
* absolutely continuous functions have bounded variation -
  `AbsolutelyContinuousOnInterval.boundedVariationOn`.

We conclude that
* absolutely continuous functions are a.e. differentiable -
  `AbsolutelyContinuousOnInterval.ae_differentiableAt`;
* if `f` is integrable on `uIcc a b`, then for any `c` in `uIcc a b`, `fun x ↦ ∫ v in c..x, f v`
  is absolutely continuous on `uIcc a b` -
  `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.

## Tags
absolutely continuous
-/

@[expose] public section

variable {X F : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup F]

open Set Filter Function MeasureTheory

open scoped Topology NNReal

namespace AbsolutelyContinuousOnInterval

/-- The filter on the collection of all the finite sequences of `uIoc` intervals induced by the
function that maps the finite sequence of the intervals to the total length of the intervals.
Details:
1. Technically the filter is on `ℕ × (ℕ → X × X)`. A finite sequence `uIoc (a i) (b i)`, `i < n`
   is represented by any `E : ℕ × (ℕ → X × X)` which satisfies `E.1 = n` and `E.2 i = (a i, b i)`
   for `i < n`. Its total length is `∑ i ∈ Finset.range n, dist (a i) (b i)`.
2. For a sequence `G : ℕ → ℕ × (ℕ → X × X)`, convergence of `G` along `totalLengthFilter` means that
   the total length of `G j`, i.e., `∑ i ∈ Finset.range (G j).1, dist ((G j).2 i).1 ((G j).2 i).2)`,
   tends to `0` as `j` tends to infinity.
-/
def totalLengthFilter : Filter (ℕ × (ℕ → X × X)) := Filter.comap
  (fun E ↦ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)

lemma hasBasis_totalLengthFilter : totalLengthFilter.HasBasis (fun (ε : ℝ) => 0 < ε)
    (fun (ε : ℝ) =>
      {E : ℕ × (ℕ → X × X) | ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < ε}) := by
  convert Filter.HasBasis.comap (α := ℝ) _ (nhds_basis_Ioo_pos _) using 1
  ext ε E
  simp only [mem_setOf_eq, zero_sub, zero_add, mem_preimage, mem_Ioo, iff_and_self]
  suffices 0 ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 by grind
  exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)

/-- The subcollection of all the finite sequences of `uIoc` intervals consisting of
`uIoc (a i) (b i)`, `i < n` where `a i`, `b i` are all in `uIcc a b` for `i < n` and
`uIoc (a i) (b i)` are mutually disjoint for `i < n`. Technically the finite sequence
`uIoc (a i) (b i)`, `i < n` is represented by any `E : ℕ × (ℕ → ℝ × ℝ)` which satisfies
`E.1 = n` and `E.2 i = (a i, b i)` for `i < n`. -/
def disjWithin (a b : ℝ) := {E : ℕ × (ℕ → ℝ × ℝ) |
  (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i ↦ uIoc (E.2 i).1 (E.2 i).2)}

lemma disjWithin_comm (a b : ℝ) : disjWithin a b = disjWithin b a := by
  rw [disjWithin, disjWithin, uIcc_comm]

lemma disjWithin_mono {a b c d : ℝ} (habcd : uIcc c d ⊆ uIcc a b) :
    disjWithin c d ⊆ disjWithin a b := by
  grind [disjWithin]

lemma uIoc_subset_of_mem_disjWithin {a b : ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hnI : (n, I) ∈ disjWithin a b) {i : ℕ} (hi : i < n) : uIoc (I i).1 (I i).2 ⊆ uIoc a b := by
  simp only [disjWithin, Finset.mem_range, mem_setOf_eq, uIcc, mem_Icc] at hnI
  grind

lemma biUnion_uIoc_subset_of_mem_disjWithin {a b : ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hnI : (n, I) ∈ disjWithin a b) :
    (⋃ i ∈ Finset.range n, uIoc (I i).1 (I i).2) ⊆ uIoc a b := by
  simp only [iUnion_subset_iff, Finset.mem_range]
  exact fun i hi ↦ uIoc_subset_of_mem_disjWithin hnI hi

lemma tendsto_volume_totalLengthFilter_nhds_zero :
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
    totalLengthFilter (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E ↦ ENNReal.ofReal (∑ i ∈ Finset.range E.1, (dist (E.2 i).1 (E.2 i).2)))
  · convert ENNReal.tendsto_ofReal (Filter.tendsto_comap)
    simp
  · intro; simp
  · intro E
    simp only
    grw [measure_biUnion_finset_le]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
    apply Eq.le
    apply Finset.sum_congr rfl
    simp [uIoc, Real.dist_eq, max_sub_min_eq_abs']

lemma tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero (a b : ℝ) :
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume.restrict (uIoc a b)
        (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b))
      (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro; simp
  · intro E
    simp only [Finset.mem_range]
    apply Measure.restrict_le_self

/-- `AbsolutelyContinuousOnInterval f a b`: A function `f` is *absolutely continuous* on `uIcc a b`
if the function which (intuitively) maps `uIoc (a i) (b i)`, `i < n` to
`∑ i ∈ Finset.range n, dist (f (a i)) (f (b i))` tendsto `𝓝 0` wrt `totalLengthFilter` restricted
to `disjWithin a b`. This is equivalent to the traditional `ε`-`δ` definition: for any `ε > 0`,
there is `δ > 0` such that for any finite disjoint collection of intervals `uIoc (a i) (b i)` for
`i < n` where `a i`, `b i` are all in `uIcc a b` for `i < n`, if
`∑ i ∈ range n, dist (a i) (b i) < δ`, then `∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`. -/
def _root_.AbsolutelyContinuousOnInterval (f : ℝ → X) (a b : ℝ) :=
  Tendsto (fun E ↦ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)

/-- The traditional `ε`-`δ` definition of absolutely continuous: A function `f` is
*absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such that for
any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`, `b i` are
all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`. -/
theorem _root_.absolutelyContinuousOnInterval_iff (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ disjWithin a b →
    ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))]

variable {f g : ℝ → X} {a b c d : ℝ}

theorem symm (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f b a := by
  simp_all [AbsolutelyContinuousOnInterval, disjWithin_comm]

theorem mono (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d ⊆ uIcc a b) :
    AbsolutelyContinuousOnInterval f c d := by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans (Filter.map_mono ?_) hf
  gcongr; exact disjWithin_mono habcd

variable {f g : ℝ → F}

@[to_fun]
theorem add (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f + g) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) (by simpa using Tendsto.add hf hg)
  · exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · rw [← Finset.sum_add_distrib]
    gcongr
    exact dist_add_add_le _ _ _ _

@[to_fun]
theorem neg (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (-f) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) (by simpa using hf)
  · exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · simp

@[to_fun]
theorem sub (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f - g) a b := by
  simpa [sub_eq_add_neg] using hf.add (hg.neg)

theorem const_smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    (α : M) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ α • f x) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) (by simpa using hf.const_mul ‖α‖)
  · exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · simp [Finset.mul_sum, dist_smul₀]

theorem const_mul {f : ℝ → ℝ} (α : ℝ) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ α * f x) a b :=
  hf.const_smul α

lemma uniformity_eq_comap_totalLengthFilter :
    uniformity X = comap (fun x ↦ (1, fun _ ↦ x)) totalLengthFilter := by
  refine Filter.HasBasis.eq_of_same_basis Metric.uniformity_basis_dist ?_
  convert hasBasis_totalLengthFilter.comap _
  simp

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is uniformly continuous on `uIcc a b`.
-/
theorem uniformContinuousOn (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (uIcc a b) := by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap, uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert Filter.comap_mono hf
  · simp only [comap_inf, comap_principal]
    congr
    ext p
    simp only [disjWithin, Finset.mem_range, preimage_setOf_eq, Nat.lt_one_iff,
      forall_eq, mem_setOf_eq, mem_prod]
    simp
  · simp [totalLengthFilter, comap_comap, Function.comp_def]

@[deprecated (since := "2026-02-03")] alias uniformlyContinuousOn :=
  uniformContinuousOn

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is continuous on `uIcc a b`. -/
theorem continuousOn (hf : AbsolutelyContinuousOnInterval f a b) :
    ContinuousOn f (uIcc a b) :=
  hf.uniformContinuousOn.continuousOn

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is bounded on `uIcc a b`. -/
theorem exists_bound (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ (C : ℝ), ∀ x ∈ uIcc a b, ‖f x‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f • g` is absolutely continuous
on `uIcc a b`. -/
@[to_fun]
theorem smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    {f : ℝ → M} {g : ℝ → F}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f • g) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg
  apply squeeze_zero' ?_ ?_
    (by simpa using (hg.const_mul C).add (hf.const_mul D))
  · exact Filter.Eventually.of_forall <| fun _ ↦ Finset.sum_nonneg (fun i hi ↦ dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i hi
  trans dist (f (I i).1 • g (I i).1) (f (I i).1 • g (I i).2) +
    dist (f (I i).1 • g (I i).2) (f (I i).2 • g (I i).2)
  · exact dist_triangle _ _ _
  · simp only [disjWithin, mem_setOf_eq] at hnI
    gcongr
    · rw [dist_smul₀]
      gcongr
      exact hC _ (hnI.left i hi |>.left)
    · rw [mul_comm]
      grw [dist_pair_smul]
      gcongr
      rw [dist_zero_right]
      exact hD _ (hnI.left i hi |>.right)

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f * g` is absolutely continuous
on `uIcc a b`. -/
@[to_fun]
theorem mul {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f * g) a b :=
  hf.smul hg

/-- If `f` is Lipschitz on `uIcc a b`, then `f` is absolutely continuous on `uIcc a b`. -/
theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval {f : ℝ → X} {K : ℝ≥0}
    (hfK : LipschitzOnWith K f (uIcc a b)) : AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ ↦ ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have := hfK (hnI₁.left i hi).left (hnI₁.left i hi).right
      apply ENNReal.toReal_mono (Ne.symm (not_eq_of_beq_eq_false rfl)) at this
      rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at this
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by symm; exact Finset.mul_sum _ _ _
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

/-- If `f` is `C^1` on `uIcc a b`, then `f` is absolutely continuous on `uIcc a b`. -/
theorem _root_.ContDiffOn.absolutelyContinuousOnInterval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : ContDiffOn ℝ 1 f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.absolutelyContinuousOnInterval

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` has bounded variation on `uIcc a b`. -/
theorem boundedVariationOn (hf : AbsolutelyContinuousOnInterval f a b) :
    BoundedVariationOn f (uIcc a b) := by
  -- We may assume wlog that `a ≤ b`.
  wlog hab₀ : a ≤ b generalizing a b
  · specialize @this b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab₀]
  -- Split the cases `a = b` (which is trivial) and `a < b`.
  rcases hab₀.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  -- Now remains the case `a < b`.
  -- Use the `ε`-`δ` definition of AC to get a `δ > 0` such that whenever a finite set of disjoint
  --   intervals `uIoc (a i) (b i)`, `i < n` have total length `< δ` and `a i, b i` are all in
  --  `[a, b]`, we have `∑ i ∈ range n, dist (f (a i)) (f (b i)) < 1`.
  rw [absolutelyContinuousOnInterval_iff] at hf
  obtain ⟨δ, hδ₁, hδ₂⟩ := hf 1 (by linarith)
  have hab₁ : 0 < b - a := by linarith
  -- Split `[a, b]` into subintervals `[a + i * δ', a + (i + 1) * δ']` for `i = 0, ..., n`, where
  --   `a + (n + 1) * δ' = b` and `δ' < δ`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ₁ hab₁)
  set δ' := (b - a) / (n + 1)
  have hδ₃ : δ' < δ := by
    dsimp only [δ']
    convert mul_lt_mul_of_pos_right hn hab₁ using 1 <;> field
  have h_mono : Monotone fun (i : ℕ) ↦ a + ↑i * δ' := by
    apply Monotone.const_add
    apply Monotone.mul_const Nat.mono_cast
    simp only [δ']
    refine div_nonneg ?_ ?_ <;> linarith
  -- The variation of `f` on `[a, b]` is the sum of the variations on these subintervals.
  have v_sum : eVariationOn f (Icc a b) =
      ∑ i ∈ Finset.range (n + 1), eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) := by
    convert eVariationOn.sum' f (I := fun i ↦ a + i * δ') h_mono |>.symm
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field
    · norm_cast
  -- The variation of `f` on any subinterval `[x, y]` of `[a, b]` of length `< δ` is `≤ 1`.
  have v_each (x y : ℝ) (_ : a ≤ x) (_ : x ≤ y) (_ : y < x + δ) (_ : y ≤ b) :
      eVariationOn f (Icc x y) ≤ 1 := by
    simp only [eVariationOn, iSup_le_iff]
    intro p
    obtain ⟨hp₁, hp₂⟩ := p.2.property
    -- Focus on a partition `p` of `[x, y]` and show its variation with `f` is `≤ 1`.
    have vf : ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) < 1 := by
      apply hδ₂ (p.1, (fun i ↦ (p.2.val i, p.2.val (i + 1))))
      · constructor
        · have : Icc x y ⊆ uIcc a b := by rw [uIcc_of_le hab₀]; gcongr
          intro i hi
          constructor <;> exact this (hp₂ _)
        · rw [PairwiseDisjoint]
          convert hp₁.pairwise_disjoint_on_Ioc_succ.set_pairwise (Finset.range p.1) using 3
          rw [uIoc_of_le (hp₁ (by lia)), Nat.succ_eq_succ]
      · suffices p.2.val p.1 - p.2.val 0 < δ by
          convert this
          rw [← Finset.sum_range_sub]
          congr; ext i
          rw [dist_comm, Real.dist_eq, abs_eq_self.mpr]
          linarith [@hp₁ i (i + 1) (by lia)]
        linarith [mem_Icc.mp (hp₂ p.1), mem_Icc.mp (hp₂ 0)]
    -- Reduce edist in the goal to dist and clear up
    have veq : (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i))).toReal =
        ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) := by
      rw [ENNReal.toReal_sum (by simp [edist_ne_top])]
      simp_rw [← dist_edist]; congr; ext i; nth_rw 1 [dist_comm]
    have not_top : ∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ≠ ⊤ := by
      simp [edist_ne_top]
    rw [← ENNReal.ofReal_toReal not_top]
    convert ENNReal.ofReal_le_ofReal (veq.symm ▸ vf.le)
    simp
  -- Reduce to goal that the variation of `f` on each of these subintervals is finite.
  simp only [BoundedVariationOn, v_sum, ne_eq, ENNReal.sum_eq_top, Finset.mem_range, not_exists,
    not_and]
  intro i hi
  -- Reduce finiteness to `≤ 1`.
  suffices eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) ≤ 1 from
    fun hC ↦ by simp [hC] at this
  -- Verify that `[a + i * δ', a + (i + 1) * δ']` is indeed a subinterval of `[a, b]`
  apply v_each
  · convert h_mono (show 0 ≤ i by lia); simp
  · convert h_mono (show i ≤ i + 1 by lia); norm_cast
  · rw [add_mul, ← add_assoc]; simpa
  · convert h_mono (show i + 1 ≤ n + 1 by lia)
    · norm_cast
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` exists a.e. on `uIcc a b`. -/
theorem ae_differentiableAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ uIcc a b → DifferentiableAt ℝ f x :=
  hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

/-- If `f` is interval integrable on `a..b` and `c ∈ uIcc a b`, then `fun x ↦ ∫ v in c..x, f v` is
absolutely continuous on `uIcc a b`. -/
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral {f : ℝ → ℝ}
    {a b c : ℝ} (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  -- Step 1: Use `MeasureTheory.tendsto_setLIntegral_zero` to conclude that the function sending
  -- `E` to `∫⁻ (x : ℝ) in s E, ‖f x‖ₑ ∂volume.restrict (uIoc a b))` tends to `0` along
  -- `totalLengthFilter ⊓ 𝓟 (disjWithin a b)`.
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
    (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
    (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  -- Step 2: Use the lintegral in Step 1 to bound the sum of the distances between
  -- `∫ v in c..(E.2 i).2, f v` and `∫ v in c..(E.2 i).2, f v` that occurs in the definition
  -- of absolutely continuous.
  have := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp this
  refine squeeze_zero' ?_ ?_ this
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [comp_apply, s]
  have : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [this] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_setOf_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [Real.dist_eq,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
        Measure.restrict_restrict_of_subset
          (uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, abs_neg,
        intervalIntegral.abs_intervalIntegral_eq]
    exact abs_integral_le_integral_abs
  · intro i hi
    unfold IntegrableOn
    have h_subset := uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset h_subset]
    exact IntegrableOn.mono_set h.def'.norm h_subset |>.integrable

end AbsolutelyContinuousOnInterval
