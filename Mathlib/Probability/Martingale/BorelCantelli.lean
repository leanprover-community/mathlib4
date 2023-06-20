/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module probability.martingale.borel_cantelli
! leanprover-community/mathlib commit 2196ab363eb097c008d4497125e0dde23fb36db2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.Martingale.Convergence
import Mathbin.Probability.Martingale.OptionalStopping
import Mathbin.Probability.Martingale.Centering

/-!

# Generalized Borel-Cantelli lemma

This file proves Lévy's generalized Borel-Cantelli lemma which is a generalization of the
Borel-Cantelli lemmas. With this generalization, one can easily deduce the Borel-Cantelli lemmas
by choosing appropriate filtrations. This file also contains the one sided martingale bound which
is required to prove the generalized Borel-Cantelli.

## Main results

- `measure_theory.submartingale.bdd_above_iff_exists_tendsto`: the one sided martingale bound: given
  a submartingale `f` with uniformly bounded differences, the set for which `f` converges is almost
  everywhere equal to the set for which it is bounded.
- `measure_theory.ae_mem_limsup_at_top_iff`: Lévy's generalized Borel-Cantelli:
  given a filtration `ℱ` and a sequence of sets `s` such that `s n ∈ ℱ n` for all `n`,
  `limsup at_top s` is almost everywhere equal to the set for which `∑ ℙ[s (n + 1)∣ℱ n] = ∞`.

-/


open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators Topology

namespace MeasureTheory

variable {Ω : Type _} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {ω : Ω}

/-!
### One sided martingale bound
-/


-- TODO: `least_ge` should be defined taking values in `with_top ℕ` once the `stopped_process`
-- refactor is complete
/-- `least_ge f r n` is the stopping time corresponding to the first time `f ≥ r`. -/
noncomputable def leastGe (f : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) :=
  hitting f (Set.Ici r) 0 n
#align measure_theory.least_ge MeasureTheory.leastGe

theorem Adapted.isStoppingTime_leastGe (r : ℝ) (n : ℕ) (hf : Adapted ℱ f) :
    IsStoppingTime ℱ (leastGe f r n) :=
  hitting_isStoppingTime hf measurableSet_Ici
#align measure_theory.adapted.is_stopping_time_least_ge MeasureTheory.Adapted.isStoppingTime_leastGe

theorem leastGe_le {i : ℕ} {r : ℝ} (ω : Ω) : leastGe f r i ω ≤ i :=
  hitting_le ω
#align measure_theory.least_ge_le MeasureTheory.leastGe_le

-- The following four lemmas shows `least_ge` behaves like a stopped process. Ideally we should
-- define `least_ge` as a stopping time and take its stopped process. However, we can't do that
-- with our current definition since a stopping time takes only finite indicies. An upcomming
-- refactor should hopefully make it possible to have stopping times taking infinity as a value
theorem leastGe_mono {n m : ℕ} (hnm : n ≤ m) (r : ℝ) (ω : Ω) : leastGe f r n ω ≤ leastGe f r m ω :=
  hitting_mono hnm
#align measure_theory.least_ge_mono MeasureTheory.leastGe_mono

theorem leastGe_eq_min (π : Ω → ℕ) (r : ℝ) (ω : Ω) {n : ℕ} (hπn : ∀ ω, π ω ≤ n) :
    leastGe f r (π ω) ω = min (π ω) (leastGe f r n ω) := by
  classical
  refine' le_antisymm (le_min (least_ge_le _) (least_ge_mono (hπn ω) r ω)) _
  by_cases hle : π ω ≤ least_ge f r n ω
  · rw [min_eq_left hle, least_ge]
    by_cases h : ∃ j ∈ Set.Icc 0 (π ω), f j ω ∈ Set.Ici r
    · refine' hle.trans (Eq.le _)
      rw [least_ge, ← hitting_eq_hitting_of_exists (hπn ω) h]
    · simp only [hitting, if_neg h]
  · rw [min_eq_right (not_le.1 hle).le, least_ge, least_ge, ←
      hitting_eq_hitting_of_exists (hπn ω) _]
    rw [not_le, least_ge, hitting_lt_iff _ (hπn ω)] at hle 
    exact
      let ⟨j, hj₁, hj₂⟩ := hle
      ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
#align measure_theory.least_ge_eq_min MeasureTheory.leastGe_eq_min

theorem stoppedValue_stoppedValue_leastGe (f : ℕ → Ω → ℝ) (π : Ω → ℕ) (r : ℝ) {n : ℕ}
    (hπn : ∀ ω, π ω ≤ n) :
    stoppedValue (fun i => stoppedValue f (leastGe f r i)) π =
      stoppedValue (stoppedProcess f (leastGe f r n)) π :=
  by ext1 ω; simp_rw [stopped_process, stopped_value]; rw [least_ge_eq_min _ _ _ hπn]
#align measure_theory.stopped_value_stopped_value_least_ge MeasureTheory.stoppedValue_stoppedValue_leastGe

theorem Submartingale.stoppedValue_leastGe [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (r : ℝ) :
    Submartingale (fun i => stoppedValue f (leastGe f r i)) ℱ μ :=
  by
  rw [submartingale_iff_expected_stopped_value_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    simp_rw [stopped_value_stopped_value_least_ge f σ r fun i => (hσ_le_π i).trans (hπ_le_n i)]
    simp_rw [stopped_value_stopped_value_least_ge f π r hπ_le_n]
    refine' hf.expected_stopped_value_mono _ _ _ fun ω => (min_le_left _ _).trans (hπ_le_n ω)
    · exact hσ.min (hf.adapted.is_stopping_time_least_ge _ _)
    · exact hπ.min (hf.adapted.is_stopping_time_least_ge _ _)
    · exact fun ω => min_le_min (hσ_le_π ω) le_rfl
  ·
    exact fun i =>
      strongly_measurable_stopped_value_of_le hf.adapted.prog_measurable_of_discrete
        (hf.adapted.is_stopping_time_least_ge _ _) least_ge_le
  ·
    exact fun i =>
      integrable_stopped_value _ (hf.adapted.is_stopping_time_least_ge _ _) hf.integrable
        least_ge_le
#align measure_theory.submartingale.stopped_value_least_ge MeasureTheory.Submartingale.stoppedValue_leastGe

variable {r : ℝ} {R : ℝ≥0}

theorem norm_stoppedValue_leastGe_le (hr : 0 ≤ r) (hf0 : f 0 = 0)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    ∀ᵐ ω ∂μ, stoppedValue f (leastGe f r i) ω ≤ r + R :=
  by
  filter_upwards [hbdd] with ω hbddω
  change f (least_ge f r i ω) ω ≤ r + R
  by_cases heq : least_ge f r i ω = 0
  · rw [HEq, hf0, Pi.zero_apply]
    exact add_nonneg hr R.coe_nonneg
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero HEq
    rw [hk, add_comm, ← sub_le_iff_le_add]
    have := not_mem_of_lt_hitting (hk.symm ▸ k.lt_succ_self : k < least_ge f r i ω) (zero_le _)
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le] at this 
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _))
#align measure_theory.norm_stopped_value_least_ge_le MeasureTheory.norm_stoppedValue_leastGe_le

theorem Submartingale.stoppedValue_leastGe_snorm_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hr : 0 ≤ r) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    snorm (stoppedValue f (leastGe f r i)) 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal (r + R) :=
  by
  refine'
    snorm_one_le_of_le' ((hf.stopped_value_least_ge r).Integrable _) _
      (norm_stopped_value_least_ge_le hr hf0 hbdd i)
  rw [← integral_univ]
  refine' le_trans _ ((hf.stopped_value_least_ge r).set_integral_le (zero_le _) MeasurableSet.univ)
  simp_rw [stopped_value, least_ge, hitting_of_le le_rfl, hf0, integral_zero']
#align measure_theory.submartingale.stopped_value_least_ge_snorm_le MeasureTheory.Submartingale.stoppedValue_leastGe_snorm_le

theorem Submartingale.stoppedValue_leastGe_snorm_le' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hr : 0 ≤ r) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
    snorm (stoppedValue f (leastGe f r i)) 1 μ ≤
      ENNReal.toNNReal (2 * μ Set.univ * ENNReal.ofReal (r + R)) :=
  by
  refine' (hf.stopped_value_least_ge_snorm_le hr hf0 hbdd i).trans _
  simp [ENNReal.coe_toNNReal (measure_ne_top μ _), ENNReal.coe_toNNReal]
#align measure_theory.submartingale.stopped_value_least_ge_snorm_le' MeasureTheory.Submartingale.stoppedValue_leastGe_snorm_le'

/-- This lemma is superceded by `submartingale.bdd_above_iff_exists_tendsto`. -/
theorem Submartingale.exists_tendsto_of_abs_bddAbove_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) → ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) :=
  by
  have ht :
    ∀ᵐ ω ∂μ, ∀ i : ℕ, ∃ c, tendsto (fun n => stopped_value f (least_ge f i n) ω) at_top (𝓝 c) :=
    by
    rw [ae_all_iff]
    exact fun i =>
      submartingale.exists_ae_tendsto_of_bdd (hf.stopped_value_least_ge i)
        (hf.stopped_value_least_ge_snorm_le' i.cast_nonneg hf0 hbdd)
  filter_upwards [ht] with ω hω hωb
  rw [BddAbove] at hωb 
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some
  have hib : ∀ n, f n ω < i := by
    intro n
    exact lt_of_le_of_lt ((mem_upperBounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi
  have heq : ∀ n, stopped_value f (least_ge f i n) ω = f n ω :=
    by
    intro n
    rw [least_ge, hitting, stopped_value]
    simp only
    rw [if_neg]
    simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ici]
    push_neg
    exact fun j _ => hib j
  simp only [← HEq, hω i]
#align measure_theory.submartingale.exists_tendsto_of_abs_bdd_above_aux MeasureTheory.Submartingale.exists_tendsto_of_abs_bddAbove_aux

theorem Submartingale.bddAbove_iff_exists_tendsto_aux [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hf0 : f 0 = 0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.exists_tendsto_of_abs_bdd_above_aux hf0 hbdd] with ω hω using
    ⟨hω, fun ⟨c, hc⟩ => hc.bddAbove_range⟩
#align measure_theory.submartingale.bdd_above_iff_exists_tendsto_aux MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto_aux

/-- One sided martingale bound: If `f` is a submartingale which has uniformly bounded differences,
then for almost every `ω`, `f n ω` is bounded above (in `n`) if and only if it converges. -/
theorem Submartingale.bddAbove_iff_exists_tendsto [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) :=
  by
  set g : ℕ → Ω → ℝ := fun n ω => f n ω - f 0 ω with hgdef
  have hg : submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.adapted 0) (hf.integrable 0))
  have hg0 : g 0 = 0 := by
    ext ω
    simp only [hgdef, sub_self, Pi.zero_apply]
  have hgbdd : ∀ᵐ ω ∂μ, ∀ i : ℕ, |g (i + 1) ω - g i ω| ≤ ↑R := by
    simpa only [sub_sub_sub_cancel_right]
  filter_upwards [hg.bdd_above_iff_exists_tendsto_aux hg0 hgbdd] with ω hω
  convert hω using 1 <;> rw [eq_iff_iff]
  · simp only [hgdef]
    refine' ⟨fun h => _, fun h => _⟩ <;> obtain ⟨b, hb⟩ := h <;>
        refine' ⟨b + |f 0 ω|, fun y hy => _⟩ <;>
      obtain ⟨n, rfl⟩ := hy
    · simp_rw [sub_eq_add_neg]
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs_self _)
    · exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩))
  · simp only [hgdef]
    refine' ⟨fun h => _, fun h => _⟩ <;> obtain ⟨c, hc⟩ := h
    · exact ⟨c - f 0 ω, hc.sub_const _⟩
    · refine' ⟨c + f 0 ω, _⟩
      have := hc.add_const (f 0 ω)
      simpa only [sub_add_cancel]
#align measure_theory.submartingale.bdd_above_iff_exists_tendsto MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto

/-!
### Lévy's generalization of the Borel-Cantelli lemma

Lévy's generalization of the Borel-Cantelli lemma states that: given a natural number indexed
filtration $(\mathcal{F}_n)$, and a sequence of sets $(s_n)$ such that for all
$n$, $s_n \in \mathcal{F}_n$, $limsup_n s_n$ is almost everywhere equal to the set for which
$\sum_n \mathbb{P}[s_n \mid \mathcal{F}_n] = \infty$.

The proof strategy follows by constructing a martingale satisfying the one sided martingale bound.
In particular, we define
$$
  f_n := \sum_{k < n} \mathbf{1}_{s_{n + 1}} - \mathbb{P}[s_{n + 1} \mid \mathcal{F}_n].
$$
Then, as a martingale is both a sub and a super-martingale, the set for which it is unbounded from
above must agree with the set for which it is unbounded from below almost everywhere. Thus, it
can only converge to $\pm \infty$ with probability 0. Thus, by considering
$$
  \limsup_n s_n = \{\sum_n \mathbf{1}_{s_n} = \infty\}
$$
almost everywhere, the result follows.
-/


theorem Martingale.bddAbove_range_iff_bddBelow_range [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => f n ω) ↔ BddBelow (Set.range fun n => f n ω) :=
  by
  have hbdd' : ∀ᵐ ω ∂μ, ∀ i, |(-f) (i + 1) ω - (-f) i ω| ≤ R :=
    by
    filter_upwards [hbdd] with ω hω i
    erw [← abs_neg, neg_sub, sub_neg_eq_add, neg_add_eq_sub]
    exact hω i
  have hup := hf.submartingale.bdd_above_iff_exists_tendsto hbdd
  have hdown := hf.neg.submartingale.bdd_above_iff_exists_tendsto hbdd'
  filter_upwards [hup, hdown] with ω hω₁ hω₂
  have :
    (∃ c, tendsto (fun n => f n ω) at_top (𝓝 c)) ↔ ∃ c, tendsto (fun n => (-f) n ω) at_top (𝓝 c) :=
    by
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨-c, hc.neg⟩
    · refine' ⟨-c, _⟩
      convert hc.neg
      simp only [neg_neg, Pi.neg_apply]
  rw [hω₁, this, ← hω₂]
  constructor <;> rintro ⟨c, hc⟩ <;> refine' ⟨-c, fun ω hω => _⟩
  · rw [mem_upperBounds] at hc 
    refine' neg_le.2 (hc _ _)
    simpa only [Pi.neg_apply, Set.mem_range, neg_inj]
  · rw [mem_lowerBounds] at hc 
    simp_rw [Set.mem_range, Pi.neg_apply, neg_eq_iff_eq_neg] at hω 
    refine' le_neg.1 (hc _ _)
    simpa only [Set.mem_range]
#align measure_theory.martingale.bdd_above_range_iff_bdd_below_range MeasureTheory.Martingale.bddAbove_range_iff_bddBelow_range

theorem Martingale.ae_not_tendsto_atTop_atTop [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atTop := by
  filter_upwards [hf.bdd_above_range_iff_bdd_below_range hbdd] with ω hω htop using
    unbounded_of_tendsto_at_top htop (hω.2 <| bddBelow_range_of_tendsto_atTop_atTop htop)
#align measure_theory.martingale.ae_not_tendsto_at_top_at_top MeasureTheory.Martingale.ae_not_tendsto_atTop_atTop

theorem Martingale.ae_not_tendsto_atTop_atBot [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
    ∀ᵐ ω ∂μ, ¬Tendsto (fun n => f n ω) atTop atBot := by
  filter_upwards [hf.bdd_above_range_iff_bdd_below_range hbdd] with ω hω htop using
    unbounded_of_tendsto_at_bot htop (hω.1 <| bddAbove_range_of_tendsto_atTop_atBot htop)
#align measure_theory.martingale.ae_not_tendsto_at_top_at_bot MeasureTheory.Martingale.ae_not_tendsto_atTop_atBot

namespace BorelCantelli

/-- Auxiliary definition required to prove Lévy's generalization of the Borel-Cantelli lemmas for
which we will take the martingale part. -/
noncomputable def process (s : ℕ → Set Ω) (n : ℕ) : Ω → ℝ :=
  ∑ k in Finset.range n, (s (k + 1)).indicator 1
#align measure_theory.borel_cantelli.process MeasureTheory.BorelCantelli.process

variable {s : ℕ → Set Ω}

theorem process_zero : process s 0 = 0 := by rw [process, Finset.range_zero, Finset.sum_empty]
#align measure_theory.borel_cantelli.process_zero MeasureTheory.BorelCantelli.process_zero

theorem adapted_process (hs : ∀ n, measurable_set[ℱ n] (s n)) : Adapted ℱ (process s) := fun n =>
  Finset.stronglyMeasurable_sum' _ fun k hk =>
    stronglyMeasurable_one.indicator <| ℱ.mono (Finset.mem_range.1 hk) _ <| hs _
#align measure_theory.borel_cantelli.adapted_process MeasureTheory.BorelCantelli.adapted_process

theorem martingalePart_process_ae_eq (ℱ : Filtration ℕ m0) (μ : Measure Ω) (s : ℕ → Set Ω) (n : ℕ) :
    martingalePart (process s) ℱ μ n =
      ∑ k in Finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1|ℱ k]) :=
  by
  simp only [martingale_part_eq_sum, process_zero, zero_add]
  refine' Finset.sum_congr rfl fun k hk => _
  simp only [process, Finset.sum_range_succ_sub_sum]
#align measure_theory.borel_cantelli.martingale_part_process_ae_eq MeasureTheory.BorelCantelli.martingalePart_process_ae_eq

theorem predictablePart_process_ae_eq (ℱ : Filtration ℕ m0) (μ : Measure Ω) (s : ℕ → Set Ω)
    (n : ℕ) :
    predictablePart (process s) ℱ μ n =
      ∑ k in Finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ)|ℱ k] :=
  by
  have := martingale_part_process_ae_eq ℱ μ s n
  simp_rw [martingale_part, process, Finset.sum_sub_distrib] at this 
  exact sub_right_injective this
#align measure_theory.borel_cantelli.predictable_part_process_ae_eq MeasureTheory.BorelCantelli.predictablePart_process_ae_eq

theorem process_difference_le (s : ℕ → Set Ω) (ω : Ω) (n : ℕ) :
    |process s (n + 1) ω - process s n ω| ≤ (1 : ℝ≥0) :=
  by
  rw [Nonneg.coe_one, process, process, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_range_succ_sub_sum, ← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
  refine' Set.indicator_le' (fun _ _ => _) (fun _ _ => zero_le_one) _
  rw [Pi.one_apply, norm_one]
#align measure_theory.borel_cantelli.process_difference_le MeasureTheory.BorelCantelli.process_difference_le

theorem integrable_process (μ : Measure Ω) [IsFiniteMeasure μ] (hs : ∀ n, measurable_set[ℱ n] (s n))
    (n : ℕ) : Integrable (process s n) μ :=
  integrable_finset_sum' _ fun k hk =>
    IntegrableOn.integrable_indicator (integrable_const 1) <| ℱ.le _ _ <| hs _
#align measure_theory.borel_cantelli.integrable_process MeasureTheory.BorelCantelli.integrable_process

end BorelCantelli

open BorelCantelli

/-- An a.e. monotone adapted process `f` with uniformly bounded differences converges to `+∞` if
and only if its predictable part also converges to `+∞`. -/
theorem tendsto_sum_indicator_atTop_iff [IsFiniteMeasure μ]
    (hfmono : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ f (n + 1) ω) (hf : Adapted ℱ f) (hint : ∀ n, Integrable (f n) μ)
    (hbdd : ∀ᵐ ω ∂μ, ∀ n, |f (n + 1) ω - f n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => f n ω) atTop atTop ↔
        Tendsto (fun n => predictablePart f ℱ μ n ω) atTop atTop :=
  by
  have h₁ :=
    (martingale_martingale_part hf hint).ae_not_tendsto_atTop_atTop
      (martingale_part_bdd_difference ℱ hbdd)
  have h₂ :=
    (martingale_martingale_part hf hint).ae_not_tendsto_atTop_atBot
      (martingale_part_bdd_difference ℱ hbdd)
  have h₃ : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ (μ[f (n + 1) - f n|ℱ n]) ω :=
    by
    refine' ae_all_iff.2 fun n => condexp_nonneg _
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄
  constructor <;> intro ht
  · refine' tendsto_at_top_at_top_of_monotone' _ _
    · intro n m hnm
      simp only [predictable_part, Finset.sum_apply]
      refine' Finset.sum_mono_set_of_nonneg hω₃ (Finset.range_mono hnm)
    rintro ⟨b, hbdd⟩
    rw [← tendsto_neg_at_bot_iff] at ht 
    simp only [martingale_part, sub_eq_add_neg] at hω₁ 
    exact
      hω₁
        (tendsto_at_top_add_right_of_le _ (-b) (tendsto_neg_at_bot_iff.1 ht) fun n =>
          neg_le_neg (hbdd ⟨n, rfl⟩))
  · refine' tendsto_at_top_at_top_of_monotone' (monotone_nat_of_le_succ hω₄) _
    rintro ⟨b, hbdd⟩
    exact
      hω₂
        ((tendsto_at_bot_add_left_of_ge _ b fun n => hbdd ⟨n, rfl⟩) <| tendsto_neg_at_bot_iff.2 ht)
#align measure_theory.tendsto_sum_indicator_at_top_iff MeasureTheory.tendsto_sum_indicator_atTop_iff

open BorelCantelli

theorem tendsto_sum_indicator_atTop_iff' [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, measurable_set[ℱ n] (s n)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : Ω → ℝ) ω) atTop atTop ↔
        Tendsto (fun n => ∑ k in Finset.range n, (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|ℱ k]) ω) atTop
          atTop :=
  by
  have :=
    tendsto_sum_indicator_at_top_iff (eventually_of_forall fun ω n => _) (adapted_process hs)
      (integrable_process μ hs) (eventually_of_forall <| process_difference_le s)
  swap
  · rw [process, process, ← sub_nonneg, Finset.sum_apply, Finset.sum_apply,
      Finset.sum_range_succ_sub_sum]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  simp_rw [process, predictable_part_process_ae_eq] at this 
  simpa using this
#align measure_theory.tendsto_sum_indicator_at_top_iff' MeasureTheory.tendsto_sum_indicator_atTop_iff'

/-- **Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets `s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `at_top.limsup s` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`. -/
theorem ae_mem_limsup_atTop_iff (μ : Measure Ω) [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, measurable_set[ℱ n] (s n)) :
    ∀ᵐ ω ∂μ,
      ω ∈ limsup s atTop ↔
        Tendsto (fun n => ∑ k in Finset.range n, (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|ℱ k]) ω) atTop
          atTop :=
  (limsup_eq_tendsto_sum_indicator_atTop ℝ s).symm ▸ tendsto_sum_indicator_atTop_iff' hs
#align measure_theory.ae_mem_limsup_at_top_iff MeasureTheory.ae_mem_limsup_atTop_iff

end MeasureTheory

