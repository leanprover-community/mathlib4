/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Absolutely Continuous Functions

This file defines absolutely continuous functions on a closed interval `uIcc a b` and proves some
basic properties about absolutely continuous functions.

## Tags
absolutely continuous
-/

open Set Filter Function

open scoped Topology

lemma Monotone.sum_range_sub {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, dist (u i) (u (i + 1)) = u n - u 0 := by
  rw [← Finset.sum_range_sub]
  congr; ext i
  rw [dist_comm, Real.dist_eq, abs_eq_self.mpr]
  linarith [@hu i (i + 1) (by omega)]

namespace AbsolutelyContinuousOnInterval

/-- The filter on the collection of all the finite sequences of `uIoc` intervals induced by the
function that the finite sequence of the intervals to the total length of the intervals -/
def totalLengthFilter : Filter (ℕ × (ℕ → ℝ × ℝ)) := Filter.comap
  (fun E ↦ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝[≥] 0)

lemma hasBasis_totalLengthFilter : TotalLengthFilter.HasBasis
    (fun (ε : ℝ) => 0 < ε)
    (fun (ε : ℝ) => {E | ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < ε}) := by
  convert Filter.HasBasis.comap _ (nhdsGE_basis _) <;> try infer_instance
  ext E
  simp only [mem_setOf_eq, mem_preimage, mem_Ico, iff_and_self]
  exact fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)

/-- The subcollection of all the finite sequences of `uIoc` intervals, requiring that every
interval must have endpoints in `uIcc a b` and they are mutually disjoint -/
def DisjEnds (a b : ℝ) := {E : ℕ × (ℕ → ℝ × ℝ) |
  (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i ↦ uIoc (E.2 i).1 (E.2 i).2)}

lemma DisjEnds_comm (a b : ℝ) : DisjEnds a b = DisjEnds b a := by rw [DisjEnds, DisjEnds, uIcc_comm]

lemma DisjEnds_mono {a b c d : ℝ} (habcd : uIcc c d ⊆ uIcc a b) : DisjEnds c d ⊆ DisjEnds a b := by
  simp +contextual only [DisjEnds, Finset.mem_range, setOf_subset_setOf, and_true,
    and_imp, Prod.forall]
  exact fun (n I h1 h2 i hi) ↦ ⟨habcd (h1 i hi).left, habcd (h1 i hi).right⟩

end AbsolutelyContinuousOnInterval

/-- `AbsolutelyContinuousOnInterval f a b`: A function `f` is *absolutely continuous* on `uIcc a b`
if the function which applis `f` to every endpoint of the finite sequences of `uIoc` intervals
tendsto `TotalLengthFilter` wrt `TotalLengthFilter` restricted to `DisjEnds a b`. -/
def AbsolutelyContinuousOnInterval (f : ℝ → ℝ) (a b : ℝ) :=
  open AbsolutelyContinuousOnInterval in
  Tendsto (fun E ↦ (E.1, fun i ↦ ((f (E.2 i).1, f (E.2 i).2))))
    (TotalLengthFilter ⊓ 𝓟 (DisjEnds a b)) TotalLengthFilter

/-- The traditional `ε`-`δ` definition of absolutely continuous; A function `f` is
*absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such that for any finite
 disjoint collection of intervals `(x i, y i]` for `i < n`, all contained in `uIcc a b`,
 if `∑ i ∈ range n, y i - x i < δ`, then `∑ i ∈ range n, |f (y i) - f (x i)| < ε`.
-/
theorem absolutelyContinuousOnInterval_iff (f : ℝ → ℝ) (a b : ℝ) :
    open AbsolutelyContinuousOnInterval in
    AbsolutelyContinuousOnInterval f a b ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ DisjEnds a b →
    ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  open AbsolutelyContinuousOnInterval in
  simp only [AbsolutelyContinuousOnInterval]
  rw [Filter.HasBasis.tendsto_iff (TotalLengthFilter_hasBasis.inf_principal _)
        TotalLengthFilter_hasBasis]
  simp +contextual [imp.swap]

namespace AbsolutelyContinuousOnInterval

theorem symm {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f b a := by
  simp only [AbsolutelyContinuousOnInterval] at *
  rwa [DisjEnds_comm]

theorem mono {f : ℝ → ℝ} {a b c d : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (habcd : uIcc c d ⊆ uIcc a b) :
    AbsolutelyContinuousOnInterval f c d := by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans ?_ hf
  apply Filter.map_mono
  gcongr; exact DisjEnds_mono habcd

theorem add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ f x + g x) a b := by
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at *
  refine le_trans (le_inf hf hg) ?_
  rw [Filter.HasBasis.le_basis_iff
      ( (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis).inf
        (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis))
      (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis)]
  intro ε hε
  refine ⟨(ε / 2, ε / 2), by simpa, ?_⟩
  simp only [preimage_setOf_eq]
  intro E hE
  simp only [mem_inter_iff, mem_setOf_eq] at hE ⊢
  calc
    _ ≤ ∑ x ∈ Finset.range E.1, (dist (f (E.2 x).1) (f (E.2 x).2) +
        dist (g (E.2 x).1) (g (E.2 x).2)) := by
      gcongr; exact dist_add_add_le _ _ _ _
    _ = (∑ x ∈ Finset.range E.1, dist (f (E.2 x).1) (f (E.2 x).2)) +
        (∑ x ∈ Finset.range E.1, dist (g (E.2 x).1) (g (E.2 x).2)) := by
      apply Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 := by gcongr <;> tauto
    _ = ε := by simp

theorem const_mul {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (α : ℝ) :
    AbsolutelyContinuousOnInterval (fun x ↦ α * f x) a b := by
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at *
  refine le_trans hf ?_
  rw [Filter.HasBasis.le_basis_iff
      (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis)
      (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis)]
  intro ε hε
  have : |α| ≥ 0 := by simp
  refine ⟨ε / (|α| + 1) , by positivity, ?_⟩
  simp only [preimage_setOf_eq]
  intro E hE
  simp only [mem_setOf_eq] at hE ⊢
  calc
    _ = ∑ x ∈ Finset.range E.1, |α| * dist (f (E.2 x).1) (f (E.2 x).2) := by
      congr; simp_rw [← smul_eq_mul, dist_smul₀]; rfl
    _ = |α| * ∑ x ∈ Finset.range E.1, dist (f (E.2 x).1) (f (E.2 x).2) := by
      symm; exact Finset.mul_sum _ _ _
    _ ≤ |α| * (ε / (|α| + 1)) := by gcongr
    _ < (|α| + 1) * (ε / (|α| + 1)) := by gcongr; linarith
    _ = ε := by field_simp

theorem neg {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ -(f x) ) a b := by
  convert hf.const_mul (-1) using 1; simp

theorem sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ f x - g x) a b := by
  simp_rw [fun x ↦ show f x - g x = f x + (-(g x)) by abel]
  exact hf.add (hg.neg)

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is uniformly continuous on `uIcc a b`.
-/
theorem uniformlyContinuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (uIcc a b) := by
  simp only [UniformContinuousOn]
  simp only [AbsolutelyContinuousOnInterval] at hf
  rw [Filter.tendsto_iff_comap] at hf ⊢
  let J (x : ℝ × ℝ) : (ℕ × (ℕ → ℝ × ℝ)) := (1, fun _ ↦ x)
  have : uniformity ℝ = comap J TotalLengthFilter := by
    refine Filter.HasBasis.eq_of_same_basis Metric.uniformity_basis_dist ?_
    convert TotalLengthFilter_hasBasis.comap J
    ext p; simp [J]
  rw [this]
  convert Filter.comap_mono (m := J) hf
  · simp only [comap_inf, comap_principal, J]
    congr
    ext p
    simp only [DisjEnds, Finset.mem_range, preimage_setOf_eq, Nat.lt_one_iff,
      forall_eq, mem_setOf_eq]
    exact ⟨fun hp ↦ ⟨hp, by simp [PairwiseDisjoint, Set.Pairwise]⟩, fun hp ↦ hp.left⟩
  · rw [comap_comap, comap_comap]
    congr 1

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is continuous on `uIcc a b`. -/
theorem continuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ContinuousOn f (uIcc a b) :=
  hf.uniformlyContinuousOn.continuousOn

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is bounded on `uIcc a b`. -/
theorem exists_bound {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ (C : ℝ), ∀ x ∈ uIcc a b, |f x| ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is bounded on `uIcc a b` by a positive
number. -/
theorem exists_pos_bound {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ (C : ℝ), C > 0 ∧ ∀ x ∈ uIcc a b, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  exact ⟨max C 1, by simp, fun x hx ↦ by simp [hC x hx]⟩

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f * g` is absolutely continuous
on `uIcc a b`. -/
theorem mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ f x * g x) a b := by
  obtain ⟨C, hC1, hC2⟩ := hf.exists_pos_bound
  obtain ⟨D, hD1, hD2⟩ := hg.exists_pos_bound
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at *
  have h0 : TotalLengthFilter ⊓ 𝓟 (DisjEnds a b) ≤ 𝓟 (DisjEnds a b) := by exact inf_le_right
  refine le_trans (le_inf (le_inf hf hg) h0) ?_
  rw [Filter.HasBasis.le_basis_iff
      ( ((Filter.HasBasis.comap _ TotalLengthFilter_hasBasis).inf
        (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis)).inf_principal _)
      (Filter.HasBasis.comap _ TotalLengthFilter_hasBasis)]
  intro ε hε
  simp only [preimage_setOf_eq]
  refine ⟨(ε / (C + D), ε / (C + D)), (by simp only [and_self]; positivity), ?_⟩
  intro (n, I) hnI
  simp only [mem_inter_iff, mem_setOf_eq] at hnI ⊢
  calc
  _ ≤ ∑ i ∈ Finset.range n, (C * dist (g ((I i).1)) (g ((I i).2)) +
        D * dist (f ((I i).1))  (f ((I i).2))) := by
    gcongr with i hi
    trans dist (f (I i).1 * g (I i).1) (f (I i).1 * g (I i).2) +
      dist (f (I i).1 * g (I i).2) (f (I i).2 * g (I i).2)
    · exact dist_triangle _ _ _
    · have := hnI.right
      simp only [DisjEnds, mem_setOf_eq] at this
      gcongr
      · rw [← smul_eq_mul, ← smul_eq_mul, dist_smul₀]
        gcongr
        exact hC2 _ (this.left i hi |>.left)
      · rw [mul_comm _ (g (I i).2), mul_comm _ (g (I i).2), ← smul_eq_mul, ← smul_eq_mul,
            dist_smul₀]
        gcongr
        exact hD2 _ (this.left i hi |>.right)
  _ = C * ∑ i ∈ Finset.range n, dist (g ((I i).1)) (g ((I i).2)) +
      D * ∑ i ∈ Finset.range n, dist (f ((I i).1)) (f ((I i).2)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  _ < C * (ε / (C + D)) + D * (ε / (C + D)) := by gcongr <;> tauto
  _ = ε := by field_simp

end AbsolutelyContinuousOnInterval

/-- If `f` is Lipschitz on `uIcc a b`, then `f` is absolutely continuous on `uIcc a b`. -/
theorem LipschitzOnWith.absolutelyContinuousOnInterval {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∃ K, LipschitzOnWith K f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨K, hfK⟩ := hf
  use ε / (K + 1)
  refine ⟨by positivity, ?_⟩
  intro (n, I) hnI1 hnI2
  simp only [AbsolutelyContinuousOnInterval.DisjEnds, mem_setOf_eq] at hnI1
  simp only at hnI2
  simp only [LipschitzOnWith] at hfK
  calc
  _ ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 := by
    apply Finset.sum_le_sum
    intro i hi
    have := hfK (hnI1.left i hi).left (hnI1.left i hi).right
    apply ENNReal.toReal_mono at this
    · rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at this
    · exact Ne.symm (not_eq_of_beq_eq_false rfl)
  _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by symm; exact Finset.mul_sum _ _ _
  _ ≤ K * (ε / (K + 1)) := by gcongr
  _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
  _ = ε := by field_simp

namespace AbsolutelyContinuousOnInterval

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` has bounded variation on `uIcc a b`. -/
theorem boundedVariationOn {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    BoundedVariationOn f (uIcc a b) := by
  wlog hab0 : a ≤ b
  · specialize @this f b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab0]
  rcases hab0.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  · rw [absolutelyContinuousOnInterval_iff] at hf
    obtain ⟨δ, hδ1, hδ2⟩ := hf 1 (by linarith)
    have hab1 : 0 < b - a := by linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ1 hab1)
    set δ' := (b - a) / (n + 1)
    have hδ3 : δ' < δ := by
      dsimp only [δ']
      convert mul_lt_mul_of_pos_right hn hab1 using 1 <;> field_simp
    have h_mono : Monotone fun (i : ℕ) ↦ a + ↑i * δ' := by
      apply Monotone.const_add
      apply Monotone.mul_const Nat.mono_cast
      simp only [δ']
      refine div_nonneg ?_ ?_ <;> linarith
    have v_sum : eVariationOn f (Icc a b) =
        ∑ i ∈ Finset.range (n + 1), eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) := by
      convert eVariationOn.sum' f (I := fun i ↦ a + i * δ') h_mono
      · simp
      · simp only [Nat.cast_add, Nat.cast_one, δ']; field_simp; abel
      · norm_cast
    have v_each (x y : ℝ) (hxy1 : a ≤ x) (hxy2 : x ≤ y) (hxy3 : y < x + δ) (hxy4 : y ≤ b) :
        eVariationOn f (Icc x y) ≤ 1 := by
      simp only [eVariationOn]
      rw [iSup_le_iff]
      intro p
      obtain ⟨hp1, hp2⟩ := p.2.property
      have vf: ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) ≤ 1 := by
        suffices ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) < 1 by
          linarith
        apply hδ2 (p.1, (fun i ↦ (p.2.val i, p.2.val (i + 1))))
        · simp only [DisjEnds, mem_setOf_eq]
          constructor
          · have : Icc x y ⊆ uIcc a b := by rw [uIcc_of_le hab0]; gcongr
            intro i hi
            constructor <;> exact this (hp2 _)
          · rw [PairwiseDisjoint]
            convert hp1.pairwise_disjoint_on_Ioc_succ.set_pairwise (Finset.range p.1) using 3
            rw [uIoc_of_le (hp1 (by omega))]
            rfl
        · simp only
          rw [hp1.sum_range_sub]
          linarith [mem_Icc.mp (hp2 p.1), mem_Icc.mp (hp2 0)]
      have veq: (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i))).toReal =
          ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) := by
        rw [ENNReal.toReal_sum (by simp [edist_ne_top])]
        simp_rw [← dist_edist]; congr; ext i; nth_rw 1 [dist_comm]
      have not_top : ∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ≠ ⊤ := by
        simp [edist_ne_top]
      rw [← ENNReal.ofReal_toReal not_top]
      convert ENNReal.ofReal_le_ofReal (veq.symm ▸ vf)
      simp
    unfold BoundedVariationOn
    rw [v_sum]
    simp only [ne_eq, ENNReal.sum_eq_top, Finset.mem_range, not_exists, not_and]
    intro i hi
    suffices eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) ≤ 1 by
      intro hC; simp [hC] at this
    apply v_each
    · convert h_mono (show 0 ≤ i by omega); simp
    · convert h_mono (show i ≤ i + 1 by omega); norm_cast
    · rw [add_mul, ← add_assoc]; simpa
    · convert h_mono (show i + 1 ≤ n + 1 by omega)
      · norm_cast
      · simp only [Nat.cast_add, Nat.cast_one, δ']; field_simp; abel

end AbsolutelyContinuousOnInterval
