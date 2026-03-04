/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Order.Archimedean.IndicatorCard
public import Mathlib.Probability.Martingale.Centering
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalStopping

/-!

# Generalized Borel-Cantelli lemma

This file proves Lévy's generalized Borel-Cantelli lemma which is a generalization of the
Borel-Cantelli lemmas. With this generalization, one can easily deduce the Borel-Cantelli lemmas
by choosing appropriate filtrations. This file also contains the one-sided martingale bound which
is required to prove the generalized Borel-Cantelli.

**Note**: the usual Borel-Cantelli lemmas are not in this file.
See `MeasureTheory.measure_limsup_atTop_eq_zero` for the first (which does not depend on
the results here), and `ProbabilityTheory.measure_limsup_eq_one` for the second (which does).

## Main results

- `MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto`: the one-sided martingale bound: given
  a submartingale `f` with uniformly bounded differences, the set for which `f` converges is almost
  everywhere equal to the set for which it is bounded.
- `MeasureTheory.ae_mem_limsup_atTop_iff`: Lévy's generalized Borel-Cantelli:
  given a filtration `ℱ` and a sequence of sets `s` such that `s n ∈ ℱ n` for all `n`,
  `limsup atTop s` is almost everywhere equal to the set for which `∑ ℙ[s (n + 1)∣ℱ n] = ∞`.

-/

@[expose] public section


open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {ι Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
/-!
### One-sided martingale bound
-/

/-- `leastGE f r` is the stopping time corresponding to the first time `f ≥ r`. -/
noncomputable def leastGE [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ici r) ⊥

theorem StronglyAdapted.isStoppingTime_leastGE [ConditionallyCompleteLinearOrderBot ι]
    {ℱ : Filtration ι m0} [WellFoundedLT ι] [Countable ι] [TopologicalSpace β]
    [Preorder β] [ClosedIciTopology β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {f : ι → Ω → β} (r : β) (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (leastGE f r) :=
  hf.adapted.isStoppingTime_hittingAfter measurableSet_Ici

/-- The stopped process of `f` above `r` is the process that is equal to `f` until `leastGE f r`
(the first time `f` passes above `r`), and then is constant afterwards. -/
noncomputable def stoppedAbove [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : ι → Ω → β :=
  stoppedProcess f (leastGE f r)

variable {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

protected lemma Submartingale.stoppedAbove [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (r : ℝ) :
    Submartingale (stoppedAbove f r) ℱ μ :=
  hf.stoppedProcess (hf.stronglyAdapted.isStoppingTime_leastGE r)

@[deprecated (since := "2025-10-25")] alias Submartingale.stoppedValue_leastGE :=
  Submartingale.stoppedAbove

variable {r : ℝ} {R : ℝ≥0}

set_option backward.isDefEq.respectTransparency false in
theorem stoppedAbove_le (hr : 0 ≤ r) (hf0 : f 0 = 0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    ∀ᵐ ω ∂μ, stoppedAbove f r i ω ≤ r + R := by
  filter_upwards [hbdd] with ω hbddω
  rw [stoppedAbove, stoppedProcess, ENat.some_eq_coe]
  by_cases h_zero : (min (i : ℕ∞) (leastGE f r ω)).untopA = 0
  · simp only [h_zero, hf0, Pi.zero_apply]
    positivity
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h_zero
  rw [hk, add_comm r, ← sub_le_iff_le_add]
  have := notMem_of_lt_hittingAfter (?_ : k < leastGE f r ω)
  · simp only [bot_eq_zero, zero_le, Set.mem_Ici, not_le, forall_const] at this
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _))
  · suffices (k : ℕ∞) < min (i : ℕ∞) (leastGE f r ω) from this.trans_le (min_le_right _ _)
    have h_top : min (i : ℕ∞) (leastGE f r ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    lift min (i : ℕ∞) (leastGE f r ω) to ℕ using h_top with p
    simp only [untopD_coe_enat, Nat.cast_lt, gt_iff_lt] at *
    lia

@[deprecated (since := "2025-10-25")] alias norm_stoppedValue_leastGE_le := stoppedAbove_le

set_option backward.isDefEq.respectTransparency false in
theorem Submartingale.eLpNorm_stoppedAbove_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hr : 0 ≤ r) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    eLpNorm (stoppedAbove f r i) 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal (r + R) := by
  refine eLpNorm_one_le_of_le' ((hf.stoppedAbove r).integrable _) ?_
    (stoppedAbove_le hr hf0 hbdd i)
  rw [← setIntegral_univ]
  refine le_trans ?_ ((hf.stoppedAbove r).setIntegral_le (zero_le _) MeasurableSet.univ)
  simp [stoppedAbove, stoppedProcess, hf0]

@[deprecated (since := "2025-10-25")] alias Submartingale.stoppedValue_leastGE_eLpNorm_le :=
  Submartingale.eLpNorm_stoppedAbove_le

theorem Submartingale.eLpNorm_stoppedAbove_le' [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hr : 0 ≤ r) (hf0 : f 0 = 0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    eLpNorm (stoppedAbove f r i) 1 μ
      ≤ ENNReal.toNNReal (2 * μ Set.univ * ENNReal.ofReal (r + R)) := by
  refine (hf.eLpNorm_stoppedAbove_le hr hf0 hbdd i).trans ?_
  simp [ENNReal.coe_toNNReal (measure_ne_top μ _), ENNReal.coe_toNNReal]

@[deprecated (since := "2025-10-25")] alias Submartingale.stoppedValue_leastGE_eLpNorm_le' :=
  Submartingale.eLpNorm_stoppedAbove_le'

/-- This lemma is superseded by `Submartingale.bddAbove_iff_exists_tendsto`. -/
theorem Submartingale.exists_tendsto_of_abs_bddAbove_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) → ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  have ht : ∀ᵐ ω ∂μ, ∀ i : ℕ, ∃ c, Tendsto (fun n => stoppedAbove f i n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    exact fun i ↦ Submartingale.exists_ae_tendsto_of_bdd (hf.stoppedAbove i)
      (hf.eLpNorm_stoppedAbove_le' i.cast_nonneg hf0 hbdd)
  filter_upwards [ht] with ω hω hωb
  rw [BddAbove] at hωb
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some
  have hib : ∀ n, f n ω < i := by
    intro n
    exact lt_of_le_of_lt ((mem_upperBounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi
  have heq : ∀ n, stoppedAbove f i n ω = f n ω := by
    intro n
    rw [stoppedAbove, stoppedProcess, leastGE, hittingAfter_eq_top_iff.mpr]
    · simp only [le_top, inf_of_le_left]
      congr
    · simp [hib]
  simp only [← heq, hω i]

theorem Submartingale.bddAbove_iff_exists_tendsto_aux [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.exists_tendsto_of_abs_bddAbove_aux hf0 hbdd] with ω hω using
    ⟨hω, fun ⟨c, hc⟩ => hc.bddAbove_range⟩

/-- One-sided martingale bound: If `f` is a submartingale which has uniformly bounded differences,
then for almost every `ω`, `f n ω` is bounded above (in `n`) if and only if it converges. -/
theorem Submartingale.bddAbove_iff_exists_tendsto [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  set g : ℕ → Ω → ℝ := fun n ω => f n ω - f 0 ω
  have hg : Submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.stronglyAdapted 0) (hf.integrable 0))
  have hg0 : g 0 = 0 := by
    ext ω
    simp only [g, sub_self, Pi.zero_apply]
  have hgbdd : ∀ᵐ ω ∂μ, ∀ i : ℕ, |g (i + 1) ω - g i ω| ≤ ↑R := by
    simpa only [g, sub_sub_sub_cancel_right]
  filter_upwards [hg.bddAbove_iff_exists_tendsto_aux hg0 hgbdd] with ω hω
  convert hω using 1
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨b, hb⟩ := h <;>
    refine ⟨b + |f 0 ω|, fun y hy => ?_⟩ <;> obtain ⟨n, rfl⟩ := hy
    · simp_rw [g, sub_eq_add_neg]
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs _)
    · exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩))
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨c, hc⟩ := h
    · exact ⟨c - f 0 ω, hc.sub_const _⟩
    · refine ⟨c + f 0 ω, ?_⟩
      have := hc.add_const (f 0 ω)
      simpa only [g, sub_add_cancel]

/-!
### Lévy's generalization of the Borel-Cantelli lemma

Lévy's generalization of the Borel-Cantelli lemma states that: given a natural number indexed
filtration $(\mathcal{F}_n)$, and a sequence of sets $(s_n)$ such that for all
$n$, $s_n \in \mathcal{F}_n$, $limsup_n s_n$ is almost everywhere equal to the set for which
$\sum_n \mathbb{P}[s_n \mid \mathcal{F}_n] = \infty$.

The proof strategy follows by constructing a martingale satisfying the one-sided martingale bound.
In particular, we define
$$
  f_n := \sum_{k < n} \big(\mathbf{1}_{s_{k + 1}} - \mathbb{P}[s_{k + 1} \mid \mathcal{F}_k]\big).
$$
Then, as a martingale is both a sub- and a super-martingale, the set for which it is unbounded from
above must agree with the set for which it is unbounded from below almost everywhere. Thus, it
can only converge to $\pm \infty$ with probability 0. Thus, by considering
$$
  \limsup_n s_n = \{\sum_n \mathbf{1}_{s_n} = \infty\}
$$
almost everywhere, the result follows.
-/


theorem Martingale.bddAbove_range_iff_bddBelow_range [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ BddBelow (Set.range fun n => f n ω) := by
  have hbdd' : ∀ᵐ ω ∂μ, ∀ i, |(-f) (i + 1) ω - (-f) i ω| ≤ R := by
    filter_upwards [hbdd] with ω hω i
    simp only [Pi.neg_apply]
    grind
  have hup := hf.submartingale.bddAbove_iff_exists_tendsto hbdd
  have hdown := hf.neg.submartingale.bddAbove_iff_exists_tendsto hbdd'
  filter_upwards [hup, hdown] with ω hω₁ hω₂
  have : (∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c)) ↔
      ∃ c, Tendsto (fun n => (-f) n ω) atTop (𝓝 c) := by
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨-c, hc.neg⟩
    · refine ⟨-c, ?_⟩
      convert hc.neg
      simp only [neg_neg, Pi.neg_apply]
  rw [hω₁, this, ← hω₂]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨-c, fun ω hω => ?_⟩
  · rw [mem_upperBounds] at hc
    refine neg_le.2 (hc _ ?_)
    simpa only [Pi.neg_apply, Set.mem_range, neg_inj]
  · rw [mem_lowerBounds] at hc
    simp_rw [Set.mem_range, Pi.neg_apply, neg_eq_iff_eq_neg] at hω
    refine le_neg.1 (hc _ ?_)
    simpa only [Set.mem_range]

theorem Martingale.ae_not_tendsto_atTop_atTop [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atTop := by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddAbove_of_tendsto_atTop htop (hω.2 <| bddBelow_range_of_tendsto_atTop_atTop htop)

theorem Martingale.ae_not_tendsto_atTop_atBot [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atBot := by
  filter_upwards [hf.bddAbove_range_iff_bddBelow_range hbdd] with ω hω htop using
    not_bddBelow_of_tendsto_atBot htop (hω.1 <| bddAbove_range_of_tendsto_atTop_atBot htop)

namespace BorelCantelli

/-- Auxiliary definition required to prove Lévy's generalization of the Borel-Cantelli lemmas for
which we will take the martingale part. -/
noncomputable def process (s : ℕ → Set Ω) (n : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range n, (s (k + 1)).indicator 1

variable {s : ℕ → Set Ω}

theorem process_zero : process s 0 = 0 := by rw [process, Finset.range_zero, Finset.sum_empty]

theorem stronglyAdapted_process (hs : ∀ n, MeasurableSet[ℱ n] (s n)) :
    StronglyAdapted ℱ (process s) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hk =>
    stronglyMeasurable_one.indicator <| ℱ.mono (Finset.mem_range.1 hk) _ <| hs _

theorem martingalePart_process_ae_eq (ℱ : Filtration ℕ m0) (μ : Measure Ω) (s : ℕ → Set Ω) (n : ℕ) :
    martingalePart (process s) ℱ μ n =
      ∑ k ∈ Finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k]) := by
  simp only [martingalePart_eq_sum, process_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [process, Finset.sum_range_succ_sub_sum]

theorem predictablePart_process_ae_eq (ℱ : Filtration ℕ m0) (μ : Measure Ω) (s : ℕ → Set Ω)
    (n : ℕ) : predictablePart (process s) ℱ μ n =
    ∑ k ∈ Finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] := by
  have := martingalePart_process_ae_eq ℱ μ s n
  simp_rw [martingalePart, process, Finset.sum_sub_distrib] at this
  exact sub_right_injective this

theorem process_difference_le (s : ℕ → Set Ω) (ω : Ω) (n : ℕ) :
    |process s (n + 1) ω - process s n ω| ≤ (1 : ℝ≥0) := by
  norm_cast
  rw [process, process, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_range_succ_sub_sum, ← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
  refine Set.indicator_le' (fun _ _ => ?_) (fun _ _ => zero_le_one) _
  rw [Pi.one_apply, norm_one]

theorem integrable_process (μ : Measure Ω) [IsFiniteMeasure μ] (hs : ∀ n, MeasurableSet[ℱ n] (s n))
    (n : ℕ) : Integrable (process s n) μ :=
  integrable_finset_sum' _ fun _ _ =>
    IntegrableOn.integrable_indicator (integrable_const 1) <| ℱ.le _ _ <| hs _

end BorelCantelli

open BorelCantelli

/-- An a.e. monotone strongly adapted process `f` with uniformly bounded differences converges to
`+∞` if and only if its predictable part also converges to `+∞`. -/
theorem tendsto_sum_indicator_atTop_iff [IsFiniteMeasure μ]
    (hfmono : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ f (n + 1) ω) (hf : StronglyAdapted ℱ f)
    (hint : ∀ n, Integrable (f n) μ) (hbdd : ∀ᵐ ω ∂μ, ∀ n, |f (n + 1) ω - f n ω| ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop atTop ↔
      Tendsto (fun n => predictablePart f ℱ μ n ω) atTop atTop := by
  have h₁ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atTop
    (martingalePart_bdd_difference ℱ hbdd)
  have h₂ := (martingale_martingalePart hf hint).ae_not_tendsto_atTop_atBot
    (martingalePart_bdd_difference ℱ hbdd)
  have h₃ : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ (μ[f (n + 1) - f n | ℱ n]) ω := by
    refine ae_all_iff.2 fun n => condExp_nonneg ?_
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄
  constructor <;> intro ht
  · refine tendsto_atTop_atTop_of_monotone' ?_ ?_
    · intro n m hnm
      simp only [predictablePart, Finset.sum_apply]
      exact Finset.sum_mono_set_of_nonneg hω₃ (Finset.range_mono hnm)
    rintro ⟨b, hbdd⟩
    rw [← tendsto_neg_atBot_iff] at ht
    simp only [martingalePart, sub_eq_add_neg] at hω₁
    exact hω₁ (tendsto_atTop_add_right_of_le _ (-b) (tendsto_neg_atBot_iff.1 ht) fun n =>
      neg_le_neg (hbdd ⟨n, rfl⟩))
  · refine tendsto_atTop_atTop_of_monotone' (monotone_nat_of_le_succ hω₄) ?_
    rintro ⟨b, hbdd⟩
    exact hω₂ ((tendsto_atBot_add_left_of_ge _ b fun n =>
      hbdd ⟨n, rfl⟩) <| tendsto_neg_atBot_iff.2 ht)

open BorelCantelli

theorem tendsto_sum_indicator_atTop_iff' [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) : ∀ᵐ ω ∂μ,
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      (s (k + 1)).indicator (1 : Ω → ℝ) ω) atTop atTop ↔
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω) atTop atTop := by
  have := tendsto_sum_indicator_atTop_iff (Eventually.of_forall fun ω n => ?_)
    (stronglyAdapted_process hs) (integrable_process μ hs)
    (Eventually.of_forall <| process_difference_le s)
  swap
  · rw [process, process, ← sub_nonneg, Finset.sum_apply, Finset.sum_apply,
      Finset.sum_range_succ_sub_sum]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  simp_rw [process, predictablePart_process_ae_eq] at this
  simpa using this

/-- **Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets `s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `limsup s atTop` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`. -/
theorem ae_mem_limsup_atTop_iff (μ : Measure Ω) [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) : ∀ᵐ ω ∂μ, ω ∈ limsup s atTop ↔
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω) atTop atTop := by
  rw [← limsup_nat_add s 1,
    Set.limsup_eq_tendsto_sum_indicator_atTop (zero_lt_one (α := ℝ)) (fun n ↦ s (n + 1))]
  exact tendsto_sum_indicator_atTop_iff' hs

end MeasureTheory
