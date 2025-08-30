/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Absolutely Continuous Functions

This file defines absolutely continuous functions on a closed interval `[a, b]` and proves some
basic properties about absolutely continuous functions.

## Tags
absolutely continuous
-/

lemma Monotone.sum_range_sub {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, dist (u i) (u (i + 1)) = u n - u 0 := by
  calc
  _ = ∑ i ∈ Finset.range n, (u (i + 1) - u i) := by
        congr; ext i
        rw [Real.dist_eq, abs_eq_neg_self.mpr]
        · ring
        · linarith [@hu i (i + 1) (by omega)]
  _ = u n - u 0 := by rw [Finset.sum_range_sub]

/-- `AbsolutelyContinuousOnInterval f a b`: A function `f` is *absolutely continuous* on `uIcc a b`
 if
for any `ε > 0`, there is `δ > 0` such that for any finite disjoint collection of closed intervals
`[x i, y i]` for `i < n`, all contained in `uIcc a b`, if `∑ i ∈ range n, y i - x i < δ`, then
`∑ i ∈ range n, |f (y i) - f (x i)| < ε`.
-/
def AbsolutelyContinuousOnInterval (f : ℝ → ℝ) (a b : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ n : ℕ, ∀ I : ℕ → (ℝ × ℝ),
  (∀ i ∈ Finset.range n, min a b ≤ (I i).1 ∧ (I i).1 ≤ (I i).2 ∧ (I i).2 ≤ max a b) →
  Set.PairwiseDisjoint (Finset.range n) (fun i ↦ Set.Ioc (I i).1 (I i).2) →
  ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 < δ →
  ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) < ε

namespace AbsolutelyContinuousOnInterval

theorem symm {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f b a := by
  simp only [AbsolutelyContinuousOnInterval] at *
  simp_rw [min_comm b a, max_comm b a]
  exact hf

theorem mono {f : ℝ → ℝ} {a b c d : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (habcd : Set.uIcc c d ⊆ Set.uIcc a b) :
    AbsolutelyContinuousOnInterval f c d := by
  simp only [AbsolutelyContinuousOnInterval] at *
  intro ε hε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  use δ; constructor; · exact hδ1
  intro n I hI
  apply hδ2 n
  intro i hi
  specialize hI i hi
  suffices min a b ≤ min c d ∧ max c d ≤ max a b by
    exact ⟨by linarith [hI], by tauto, by linarith [hI]⟩
  rw [Set.uIcc, Set.uIcc, Set.Icc_subset_Icc_iff] at habcd
  · exact habcd
  · simp

theorem add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f + g) a b := by
  simp only [AbsolutelyContinuousOnInterval] at *
  intro ε hε
  obtain ⟨δf, hδf1, hδf2⟩ := hf (ε / 2) (by linarith); clear hf
  obtain ⟨δg, hδg1, hδg2⟩ := hg (ε / 2) (by linarith); clear hg
  let δ := min δf δg
  have : δ ≤ δf := by simp [δ]
  have : δ ≤ δg := by simp [δ]
  use δ
  constructor
  · simp [δ, hδf1, hδg1]
  · intro n I hIsub hIdis hIlen
    specialize hδf2 n I hIsub hIdis (by linarith)
    specialize hδg2 n I hIsub hIdis (by linarith)
    calc
    _ ≤ ∑ i ∈ Finset.range n, (dist (f (I i).1) (f (I i).2) + dist (g (I i).1) (g (I i).2)) := by
      gcongr; exact dist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) +
        ∑ i ∈ Finset.range n, dist (g (I i).1) (g (I i).2) := by
      apply Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := by simp

theorem smul {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (α : ℝ) :
    AbsolutelyContinuousOnInterval (α • f) a b := by
  simp only [AbsolutelyContinuousOnInterval] at *
  intro ε hε
  have : |α| ≥ 0 := by simp
  obtain ⟨δf, hδf1, hδf2⟩ := hf (ε / (|α| + 1) ) (by positivity); clear hf
  use δf
  constructor
  · assumption
  · intro n I hIsub hIdis hIlen
    specialize hδf2 n I hIsub hIdis (by assumption)
    calc
    _ = ∑ i ∈ Finset.range n, |α| * dist (f (I i).1) (f (I i).2) := by
      congr; ext i
      dsimp only [Pi.smul_apply, Real.dist_eq]
      rw [← smul_sub, abs_smul]
      simp
    _ = |α| * ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) := by
      symm; exact Finset.mul_sum _ _ _
    _ ≤ |α| * (ε / (|α| + 1)) := by gcongr
    _ < (|α| + 1) * (ε / (|α| + 1)) := by gcongr; linarith
    _ = ε := by field_simp

theorem neg {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (-f) a b := by
  exact (show -f = (-1 : ℝ) • f by simp) ▸ hf.smul (-1)

theorem sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f - g) a b := by
  rw [show f - g = f + (-g) by abel]
  exact hf.add (hg.neg)

/-- If `f` is absolutely continuous on `[[a, b]]`, then `f` is uniformly continuous on `[[a, b]]`.
-/
theorem uniformlyContinuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (Set.uIcc a b) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  dsimp only [AbsolutelyContinuousOnInterval] at hf
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  clear hf
  use δ
  simp only [hδ1, true_and]
  intro x hx y hy hxyδ
  simp only [Set.uIcc, Set.Icc, Set.mem_setOf_eq] at *
  wlog hxy : x ≤ y
  · specialize this ε hε δ hδ1 hδ2 y hy x hx (by rwa [dist_comm]) (by linarith)
    rwa [dist_comm]
  specialize hδ2 1 (fun _ ↦ (x, y))
  simp only [Finset.range_one, Finset.mem_singleton, forall_eq, Finset.coe_singleton,
    Set.pairwiseDisjoint_singleton, Finset.sum_const, Finset.card_singleton, one_smul,
    forall_const, and_imp] at hδ2
  apply hδ2 <;> tauto

/-- If `f` is absolutely continuous on `[[a, b]]`, then `f` is continuous on `[[a, b]]`. -/
theorem continuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ContinuousOn f (Set.uIcc a b) := by
  exact hf.uniformlyContinuousOn.continuousOn

/-- If `f` is absolutely continuous on `[[a, b]]`, then `f` is bounded on `[[a, b]]`. -/
theorem exists_bound {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ (C : ℝ), ∀ x ∈ Set.uIcc a b, |f x| ≤ C := by
  exact isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

/-- If `f` is absolutely continuous on `[[a, b]]`, then `f` is bounded on `[[a, b]]` by a positive
number. -/
theorem exists_pos_bound {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ (C : ℝ), C > 0 ∧ ∀ x ∈ Set.uIcc a b, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  use max C 1; constructor; · simp
  intro x hx; specialize hC x hx; simp [hC]

/-- If `f` and `g` are absolutely continuous on `[[a, b]]`, then `f * g` is absolutely continuous
on `[[a, b]]`. -/
theorem mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f * g) a b := by
  obtain ⟨C, hC1, hC2⟩ := hf.exists_pos_bound
  obtain ⟨D, hD1, hD2⟩ := hg.exists_pos_bound
  simp only [AbsolutelyContinuousOnInterval] at *
  intro ε hε
  obtain ⟨δf, hδf1, hδf2⟩ := hf (ε / (C + D) ) (by positivity); clear hf
  obtain ⟨δg, hδg1, hδg2⟩ := hg (ε / (C + D) ) (by positivity); clear hg
  let δ := min δf δg
  have : δ ≤ δf := by simp [δ]
  have : δ ≤ δg := by simp [δ]
  use δ
  constructor
  · simp [δ, hδf1, hδg1]
  · intro n I hIsub hIdis hIlen
    specialize hδf2 n I hIsub hIdis (by linarith)
    specialize hδg2 n I hIsub hIdis (by linarith)
    calc
    _ = ∑ i ∈ Finset.range n, |f ((I i).1) * (g ((I i).1) - g ((I i).2)) +
            g ((I i).2) * (f ((I i).1) - f ((I i).2))| := by
          congr; ext i; rw [Real.dist_eq]; congr 1; dsimp [Pi.mul_apply]; ring
    _ ≤ ∑ i ∈ Finset.range n, (|f (I i).1 * (g (I i).1 - g (I i).2)| +
              |g (I i).2 * (f (I i).1 - f (I i).2)|) := by
            gcongr with i hi
            apply abs_add_le
    _ = ∑ i ∈ Finset.range n, (|f ((I i).1)| * |g ((I i).1) - g ((I i).2)| +
            |g ((I i).2)| * |f ((I i).1) - f ((I i).2)|) := by
          congr; ext i; congr <;> apply abs_mul
    _ ≤ ∑ i ∈ Finset.range n, (C * |g ((I i).1) - g ((I i).2)| +
            D * |f ((I i).1) - f ((I i).2)|) := by
          gcongr with i hi
          · apply hC2; rw [Set.uIcc, Set.mem_Icc]; have := hIsub i hi; constructor <;> linarith
          · apply hD2; rw [Set.uIcc, Set.mem_Icc]; have := hIsub i hi; constructor <;> linarith
    _ = C * ∑ i ∈ Finset.range n, |g ((I i).1) - g ((I i).2)| +
            D * ∑ i ∈ Finset.range n, |f ((I i).1) - f ((I i).2)| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = C * ∑ i ∈ Finset.range n, dist (g (I i).1) (g (I i).2) +
            D * ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) := by dsimp [Real.dist_eq]
    _ < C * (ε / (C + D)) + D * (ε / (C + D)) := by gcongr
    _ = ε := by field_simp

end AbsolutelyContinuousOnInterval

/-- If `f` is Lipschitz on `[[a, b]]`, then `f` is absolutely continuous on `[[a, b]]`. -/
theorem LipschitzOnWith.absolutelyContinuousOnInterval {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∃ K, LipschitzOnWith K f (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  simp only [AbsolutelyContinuousOnInterval]
  intro ε hε
  obtain ⟨K, hfK⟩ := hf
  use ε / (K + 1)
  constructor
  · positivity
  · intro n I hIsub hIdis hIlen
    simp only [LipschitzOnWith] at hfK
    calc
    _ ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hI1, hI2, hI3⟩ := hIsub i hi
      have hI4 : (I i).1 ∈ Set.uIcc a b ∧ (I i).2 ∈ Set.uIcc a b := by
        constructor <;> (simp only [Set.uIcc, Set.Icc, Set.mem_setOf_eq]; constructor <;> linarith)
      have := hfK hI4.left hI4.right
      apply ENNReal.toReal_mono at this
      · rw [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at this
        convert this
      · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
      symm; exact Finset.mul_sum _ _ _
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field_simp

lemma split_interval {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ : δ > 0) :
    ∃ n : ℕ, ∃ c : ℕ → ℝ, (c 0 = a ∧ c n = b ∧
      ∀ i < n, a ≤ c i ∧ c i < c (i + 1) ∧ c (i + 1) < c i + δ ∧ c (i + 1) ≤ b) := by
  have : ∃ n : ℕ, b - a ≤ n • (δ / 2) := by
    exact Archimedean.arch (b - a) (by linarith)
  have hArchi : ∃ n : ℕ, b - a ≤ n * (δ / 2) := by
    simpa +contextual [← nsmul_eq_mul]
  let n := Nat.find hArchi
  have hn: b - a ≤ n * (δ / 2) := by exact Nat.find_spec hArchi
  have hnless (j : ℕ): j < n → ¬ (b - a ≤ j * (δ / 2)) := by exact Nat.find_min hArchi
  let c (i : ℕ) : ℝ := if i < n then a + i * (δ / 2) else b
  use n, c
  have c_le_b (i : ℕ) (hi : i < n) : c i < b := by
    simp only [hi, ↓reduceIte, c]
    specialize hnless i hi
    linarith
  have n_nonzero : n ≠ 0 := by intro hn0; simp [hn0] at hn; linarith
  repeat' constructor
  · simp [c, n_nonzero]
  · simp [c]
  · intro i hi
    have c_i : c i = a + i * (δ / 2) := by simp [c, hi]
    by_cases hilast : i + 1 = n
    · have c_i_1 : c (i + 1) = b := by simp [c, hilast]
      repeat' constructor
      · simp [c_i, hδ]
      · convert c_le_b i hi
      · suffices c (i + 1) ≤ c i + δ / 2 by linarith
        rw [c_i_1, c_i]
        rw [tsub_le_iff_left] at hn
        convert hn using 1
        rw [show (n : ℝ) = (i : ℝ) + 1 by symm; norm_cast]
        ring
      · simp [c_i_1]
    · replace hilast : i + 1 < n := by omega
      have c_i_1 : c (i + 1) = a + (i + 1) * (δ / 2) := by simp [c, hilast]
      repeat' constructor
      · simp [c_i, hδ]
      · simp [c_i, c_i_1, hδ]
      · simp only [c_i_1, c_i]; linarith
      · have := c_le_b (i + 1) hilast; linarith

namespace AbsolutelyContinuousOnInterval

/-- If `f` is absolutely continuous on `[[a, b]]`, then `f` has bounded variation on `[[a, b]]`. -/
theorem boundedVariationOn {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    BoundedVariationOn f (Set.uIcc a b) := by
  wlog hab0 : a ≤ b
  · specialize @this f b a hf.symm (by linarith)
    rwa [Set.uIcc_comm]
  simp only [hab0, Set.uIcc_of_le]
  by_cases hab1 : a = b
  · rw [show Set.Icc a b = {a} by simp [hab1]]
    simp [BoundedVariationOn]
  · have hab : a < b := lt_of_le_of_ne hab0 hab1
    obtain ⟨δ, hδ1, hδ2⟩ := hf 1 (by linarith)
    simp_rw [show min a b = a by simp [hab0], show max a b = b by simp [hab0] ] at hδ2
    obtain ⟨n, c, hc1, hc2, hc3⟩ := split_interval hab hδ1
    have v_sum: eVariationOn f (Set.Icc a b) =
        ∑ i ∈ Finset.range n, eVariationOn f (Set.Icc (c i) (c (i + 1))) := by
      suffices ∀ k ≤ n, eVariationOn f (Set.Icc a (c k)) =
          ∑ i ∈ Finset.range k, eVariationOn f (Set.Icc (c i) (c (i + 1))) by
        convert this n (by omega)
        exact hc2.symm
      intro k hk
      induction k with
      | zero => rw [show Set.Icc a (c 0) = {a} by simp [hc1]]; simp
      | succ k ih =>
        specialize ih (by omega)
        calc
        _ = eVariationOn f (Set.Icc a (c k)) + eVariationOn f (Set.Icc (c k) (c (k + 1))) := by
              have := hc3 k (by omega)
              have L : a ≤ c k := by tauto
              have R : c k ≤ c (k + 1) := by linarith
              have IG : IsGreatest (Set.Icc a (c k)) (c k) := by
                simp [IsGreatest, L, upperBounds]
              have IL : IsLeast (Set.Icc (c k) (c (k + 1))) (c k) := by
                simp +contextual [IsLeast, R, lowerBounds]
              convert eVariationOn.union f IG IL
              symm
              exact Set.Icc_union_Icc_eq_Icc L R
        _ = ∑ i ∈ Finset.range k, eVariationOn f (Set.Icc (c i) (c (i + 1))) +
                eVariationOn f (Set.Icc (c k) (c (k + 1))) := by rw [ih]
        _ = ∑ i ∈ Finset.range (k + 1), eVariationOn f (Set.Icc (c i) (c (i + 1))) := by
                rw [Finset.sum_range_succ]
    have v_each (x y : ℝ) (hxy : a ≤ x ∧ x < y ∧ y < x + δ ∧ y ≤ b):
        eVariationOn f (Set.Icc x y) ≤ 1 := by
      simp only [eVariationOn]
      rw [iSup_le_iff]
      intro p
      obtain ⟨hp1, hp2⟩ := p.2.property
      have vf:  ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) ≤ 1 := by
        suffices ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) < 1 by
          linarith
        specialize hδ2 p.1 (fun i ↦ (p.2.val i, p.2.val (i + 1)))
        apply hδ2
        · intro i hi
          simp only
          have := hp1 (show i ≤ i + 1 by omega)
          have := hp2 i; simp [Set.Icc] at this
          have := hp2 (i + 1); simp [Set.Icc] at this
          repeat' (first | constructor | linarith)
        · suffices (Monotone fun i ↦ (p.2.val i, p.2.val (i + 1)).1) by
            exact this.pairwise_disjoint_on_Ioc_succ.set_pairwise (Finset.range p.1)
          simpa
        · simp only
          rw [hp1.sum_range_sub]
          have := hp2 p.1; simp at this
          have := hp2 0; simp at this
          linarith
      have veq: (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i))).toReal =
          ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) := by
        rw [ENNReal.toReal_sum]
        swap
        · simp [edist_ne_top]
        · simp_rw [← dist_edist]
          congr; ext i; nth_rw 1 [dist_comm]
      have not_top : ∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ≠ ⊤ := by
        simp [edist_ne_top]
      rw [← ENNReal.ofReal_toReal not_top]
      convert ENNReal.ofReal_le_ofReal (veq.symm ▸ vf)
      simp
    unfold BoundedVariationOn
    rw [v_sum]
    simp only [ne_eq, ENNReal.sum_eq_top, Finset.mem_range, not_exists, not_and]
    intro i hi
    suffices eVariationOn f (Set.Icc (c i) (c (i + 1))) ≤ 1 by intro hC; simp [hC] at this
    apply v_each
    exact hc3 i hi

end AbsolutelyContinuousOnInterval
