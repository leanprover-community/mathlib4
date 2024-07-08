/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Constructions.Polish

#align_import probability.martingale.convergence from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfies some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale. It also contains the L¹ martingale convergence theorem which provides
an L¹ limit to a uniformly integrable submartingale. Finally, it also contains the Lévy upwards
theorems.

## Main results

* `MeasureTheory.Submartingale.ae_tendsto_limitProcess`: the almost everywhere martingale
  convergence theorem: an L¹-bounded submartingale adapted to the filtration `ℱ` converges almost
  everywhere to its limit process.
* `MeasureTheory.Submartingale.memℒp_limitProcess`: the limit process of an Lᵖ-bounded
  submartingale is Lᵖ.
* `MeasureTheory.Submartingale.tendsto_snorm_one_limitProcess`: part a of the L¹ martingale
  convergence theorem: a uniformly integrable submartingale adapted to the filtration `ℱ` converges
  almost everywhere and in L¹ to an integrable function which is measurable with respect to
  the σ-algebra `⨆ n, ℱ n`.
* `MeasureTheory.Martingale.ae_eq_condexp_limitProcess`: part b the L¹ martingale convergence
  theorem: if `f` is a uniformly integrable martingale adapted to the filtration `ℱ`, then
  `f n` equals `𝔼[g | ℱ n]` almost everywhere where `g` is the limiting process of `f`.
* `MeasureTheory.Integrable.tendsto_ae_condexp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges
  almost everywhere to `g`.
* `MeasureTheory.Integrable.tendsto_snorm_condexp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges in
  L¹ to `g`.

-/


open TopologicalSpace Filter MeasureTheory.Filtration

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0}

section AeConvergence

/-!

### Almost everywhere martingale convergence theorem

We will now prove the almost everywhere martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is an L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to an integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $\omega$ satisfying $\limsup_{n \to \infty} |f_n(\omega)| < \infty$ and the number of
upcrossings of $(f_n(\omega))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(\omega))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E} \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
implying $\limsup_{n \to \infty} |f_n| < \infty$ a.e. Furthermore, by the upcrossing estimate,
the number of upcrossings is finite almost everywhere implying $f$ converges pointwise almost
everywhere.

Thus, denoting $g$ the a.e. limit of $(f_n)$, $g$ is $\mathcal{F}_\infty$-measurable as for all
$n$, $f_n$ is $\mathcal{F}_n$-measurable and $\mathcal{F}_n \le \mathcal{F}_\infty$. Finally, $g$
is integrable as $|g| \le \liminf_{n \to \infty} |f_n|$ so
$$
  \mathbb{E}|g| \le \mathbb{E} \limsup_{n \to \infty} |f_n| \le
    \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
as required.

Implementationwise, we have `tendsto_of_no_upcrossings` which shows that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $|f_n(\omega)|$ is not
bounded, then either $f_n(\omega) \to \pm \infty$ or one of $\limsup f_n(\omega)$ or
$\liminf f_n(\omega)$ equals $\pm \infty$ while the other is finite. But the first case
contradicts $\liminf |f_n(\omega)| < \infty$ while the second case contradicts finite upcrossings.

Furthermore, we introduce `Filtration.limitProcess` which chooses the limiting random variable
of a stochastic process if it exists, otherwise returning 0. Hence, instead of showing an
existence statement, we phrase the a.e. martingale convergence theorem by showing that a
submartingale converges to its `limitProcess` almost everywhere.

-/


/-- If a stochastic process has bounded upcrossing from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
theorem not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
    ¬((∃ᶠ n in atTop, f n ω < a) ∧ ∃ᶠ n in atTop, b < f n ω) := by
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω
  replace hω : ∃ k, ∀ N, upcrossingsBefore a b f N ω < k := by
    obtain ⟨k, hk⟩ := hω
    exact ⟨k + 1, fun N => lt_of_le_of_lt (hk N) k.lt_succ_self⟩
  rintro ⟨h₁, h₂⟩
  rw [frequently_atTop] at h₁ h₂
  refine Classical.not_not.2 hω ?_
  push_neg
  intro k
  induction' k with k ih
  · simp only [Nat.zero_eq, zero_le, exists_const]
  · obtain ⟨N, hN⟩ := ih
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁
    exact ⟨N₂ + 1, Nat.succ_le_of_lt <|
      lt_of_le_of_lt hN (upcrossingsBefore_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩
#align measure_theory.not_frequently_of_upcrossings_lt_top MeasureTheory.not_frequently_of_upcrossings_lt_top

/-- A stochastic process that frequently visits below `a` and above `b` has infinite upcrossings. -/
theorem upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : ∃ᶠ n in atTop, f n ω < a)
    (h₂ : ∃ᶠ n in atTop, b < f n ω) : upcrossings a b f ω = ∞ :=
  by_contradiction fun h => not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩
#align measure_theory.upcrossings_eq_top_of_frequently_lt MeasureTheory.upcrossings_eq_top_of_frequently_lt

/-- A realization of a stochastic process with bounded upcrossings and bounded liminfs is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
theorem tendsto_of_uncrossing_lt_top (hf₁ : liminf (fun n => (‖f n ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
    ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun n => |f n ω|
  · rw [isBoundedUnder_le_abs] at h
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    intro a ha b hb hab
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ha, hb
    exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (Rat.cast_lt.1 hab)).ne
  · obtain ⟨a, b, hab, h₁, h₂⟩ := ENNReal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact
      False.elim ((hf₂ a b hab).ne (upcrossings_eq_top_of_frequently_lt (Rat.cast_lt.2 hab) h₁ h₂))
#align measure_theory.tendsto_of_uncrossing_lt_top MeasureTheory.tendsto_of_uncrossing_lt_top

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
theorem Submartingale.upcrossings_ae_lt_top' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) (hab : a < b) : ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ := by
  refine ae_lt_top (hf.adapted.measurable_upcrossings hab) ?_
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le] at this
  · refine (lt_of_le_of_lt this (ENNReal.div_lt_top ?_ ?_)).ne
    · have hR' : ∀ n, ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ R + ‖a‖₊ * μ Set.univ := by
        simp_rw [snorm_one_eq_lintegral_nnnorm] at hbdd
        intro n
        refine (lintegral_mono ?_ : ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ ∫⁻ ω, ‖f n ω‖₊ + ‖a‖₊ ∂μ).trans ?_
        · intro ω
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ENNReal.coe_add, ENNReal.coe_le_coe]
          exact nnnorm_add_le _ _
        · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add (hbdd _) le_rfl
      refine ne_of_lt (iSup_lt_iff.2 ⟨R + ‖a‖₊ * μ Set.univ, ENNReal.add_lt_top.2
        ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top ENNReal.coe_lt_top.ne (measure_ne_top _ _)⟩,
        fun n => le_trans ?_ (hR' n)⟩)
      refine lintegral_mono fun ω => ?_
      rw [ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
      · by_cases hnonneg : 0 ≤ f n ω - a
        · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        · rw [posPart_eq_zero.2 (not_le.1 hnonneg).le]
          exact norm_nonneg _
      · simp only [Ne, ENNReal.coe_ne_top, not_false_iff]
    · simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
  · simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le, true_or_iff]
  · simp only [Ne, ENNReal.ofReal_ne_top, not_false_iff, true_or_iff]
#align measure_theory.submartingale.upcrossings_ae_lt_top' MeasureTheory.Submartingale.upcrossings_ae_lt_top'

theorem Submartingale.upcrossings_ae_lt_top [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  rintro a b hab
  exact hf.upcrossings_ae_lt_top' hbdd (Rat.cast_lt.2 hab)
#align measure_theory.submartingale.upcrossings_ae_lt_top MeasureTheory.Submartingale.upcrossings_ae_lt_top

/-- An L¹-bounded submartingale converges almost everywhere. -/
theorem Submartingale.exists_ae_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_atTop_of_snorm_bdd one_ne_zero
    (fun n => (hf.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with ω h₁ h₂
  exact tendsto_of_uncrossing_lt_top h₂ h₁
#align measure_theory.submartingale.exists_ae_tendsto_of_bdd MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd

theorem Submartingale.exists_ae_trim_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ.trim (sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _ : ⨆ n, ℱ n ≤ m0),
      ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  letI := (⨆ n, ℱ n)
  rw [ae_iff, trim_measurableSet_eq]
  · exact hf.exists_ae_tendsto_of_bdd hbdd
  · exact MeasurableSet.compl <| measurableSet_exists_tendsto
      fun n => (hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩) le_rfl
#align measure_theory.submartingale.exists_ae_trim_tendsto_of_bdd MeasureTheory.Submartingale.exists_ae_trim_tendsto_of_bdd

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
theorem Submartingale.ae_tendsto_limitProcess [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  classical
  suffices
      ∃ g, StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) by
    rw [limitProcess, dif_pos this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω => if h : ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hg' : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.choose_spec
  have hg'm : @AEStronglyMeasurable _ _ _ (⨆ n, ℱ n) g' (μ.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (fun n => ((hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩
#align measure_theory.submartingale.ae_tendsto_limit_process MeasureTheory.Submartingale.ae_tendsto_limitProcess

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
theorem Submartingale.memℒp_limitProcess {p : ℝ≥0∞} (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) p μ ≤ R) : Memℒp (ℱ.limitProcess f μ) p μ :=
  memℒp_limitProcess_of_snorm_bdd
    (fun n => ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) hbdd
#align measure_theory.submartingale.mem_ℒp_limit_process MeasureTheory.Submartingale.memℒp_limitProcess

end AeConvergence

section L1Convergence

variable [IsFiniteMeasure μ] {g : Ω → ℝ}

/-!

### L¹ martingale convergence theorem

We will now prove the L¹ martingale convergence theorems.

The L¹ martingale convergence theorem states that:
(a) if `f` is a uniformly integrable (in the probability sense) submartingale adapted to the
  filtration `ℱ`, it converges in L¹ to an integrable function `g` which is measurable with
  respect to `ℱ∞ := ⨆ n, ℱ n` and
(b) if `f` is actually a martingale, `f n = 𝔼[g | ℱ n]` almost everywhere.
(c) Finally, if `h` is integrable and measurable with respect to `ℱ∞`, `(𝔼[h | ℱ n])ₙ` is a
  uniformly integrable martingale which converges to `h` almost everywhere and in L¹.

The proof is quite simple. (a) follows directly from the a.e. martingale convergence theorem
and the Vitali convergence theorem as our definition of uniform integrability (in the probability
sense) directly implies L¹-uniform boundedness. We note that our definition of uniform
integrability is slightly non-standard but is equivalent to the usual literary definition. This
equivalence is provided by `MeasureTheory.uniformIntegrable_iff`.

(b) follows since given $n$, we have for all $m \ge n$,
$$
  \|f_n - \mathbb{E}[g \mid \mathcal{F}_n]\|_1 =
    \|\mathbb{E}[f_m - g \mid \mathcal{F}_n]\|_1 \le \|\|f_m - g\|_1.
$$
Thus, taking $m \to \infty$ provides the almost everywhere equality.

Finally, to prove (c), we define $f_n := \mathbb{E}[h \mid \mathcal{F}_n]$. It is clear that
$(f_n)_n$ is a martingale by the tower property for conditional expectations. Furthermore,
$(f_n)_n$ is uniformly integrable in the probability sense. Indeed, as a single function is
uniformly integrable in the measure theory sense, for all $\epsilon > 0$, there exists some
$\delta > 0$ such that for all measurable set $A$ with $\mu(A) < δ$, we have
$\mathbb{E}|h|\mathbf{1}_A < \epsilon$. So, since for sufficently large $\lambda$, by the Markov
inequality, we have for all $n$,
$$
  \mu(|f_n| \ge \lambda) \le \lambda^{-1}\mathbb{E}|f_n| \le \lambda^{-1}\mathbb|g| < \delta,
$$
we have for sufficently large $\lambda$, for all $n$,
$$
  \mathbb{E}|f_n|\mathbf{1}_{|f_n| \ge \lambda} \le
    \mathbb|g|\mathbf{1}_{|f_n| \ge \lambda} < \epsilon,
$$
implying $(f_n)_n$ is uniformly integrable. Now, to prove $f_n \to h$ almost everywhere and in
L¹, it suffices to show that $h = g$ almost everywhere where $g$ is the almost everywhere and L¹
limit of $(f_n)_n$ from part (b) of the theorem. By noting that, for all $s \in \mathcal{F}_n$,
we have
$$
  \mathbb{E}g\mathbf{1}_s = \mathbb{E}[\mathbb{E}[g \mid \mathcal{F}_n]\mathbf{1}_s] =
    \mathbb{E}[\mathbb{E}[h \mid \mathcal{F}_n]\mathbf{1}_s] = \mathbb{E}h\mathbf{1}_s
$$
where $\mathbb{E}[g \mid \mathcal{F}_n = \mathbb{E}[h \mid \mathcal{F}_n]$ almost everywhere
by part (b); the equality also holds for all $s \in \mathcal{F}_\infty$ by Dynkin's theorem.
Thus, as both $h$ and $g$ are $\mathcal{F}_\infty$-measurable, $h = g$ almost everywhere as
required.

Similar to the a.e. martingale convergence theorem, rather than showing the existence of the
limiting process, we phrase the L¹-martingale convergence theorem by proving that a submartingale
does converge in L¹ to its `limitProcess`. However, in contrast to the a.e. martingale convergence
theorem, we do not need to introduce an L¹ version of `Filtration.limitProcess` as the L¹ limit
and the a.e. limit of a submartingale coincide.

-/


/-- Part a of the **L¹ martingale convergence theorem**: a uniformly integrable submartingale
adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. -/
theorem Submartingale.tendsto_snorm_one_limitProcess (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    Tendsto (fun n => snorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hunif.2.2
  have hmeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hf.stronglyMeasurable n).mono (ℱ.le _)).aestronglyMeasurable
  exact tendsto_Lp_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memℒp_limitProcess_of_snorm_bdd hmeas hR) hunif.2.1
    (tendstoInMeasure_of_tendsto_ae hmeas <| hf.ae_tendsto_limitProcess hR)
#align measure_theory.submartingale.tendsto_snorm_one_limit_process MeasureTheory.Submartingale.tendsto_snorm_one_limitProcess

theorem Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
  let ⟨_, hR⟩ := hunif.2.2
  hf.ae_tendsto_limitProcess hR
#align measure_theory.submartingale.ae_tendsto_limit_process_of_uniform_integrable MeasureTheory.Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable

/-- If a martingale `f` adapted to `ℱ` converges in L¹ to `g`, then for all `n`, `f n` is almost
everywhere equal to `𝔼[g | ℱ n]`. -/
theorem Martingale.eq_condexp_of_tendsto_snorm {μ : Measure Ω} (hf : Martingale f ℱ μ)
    (hg : Integrable g μ) (hgtends : Tendsto (fun n => snorm (f n - g) 1 μ) atTop (𝓝 0)) (n : ℕ) :
    f n =ᵐ[μ] μ[g|ℱ n] := by
  rw [← sub_ae_eq_zero, ← snorm_eq_zero_iff (((hf.stronglyMeasurable n).mono (ℱ.le _)).sub
    (stronglyMeasurable_condexp.mono (ℱ.le _))).aestronglyMeasurable one_ne_zero]
  have ht : Tendsto (fun m => snorm (μ[f m - g|ℱ n]) 1 μ) atTop (𝓝 0) :=
    haveI hint : ∀ m, Integrable (f m - g) μ := fun m => (hf.integrable m).sub hg
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (fun m => zero_le _)
      fun m => snorm_one_condexp_le_snorm _
  have hev : ∀ m ≥ n, snorm (μ[f m - g|ℱ n]) 1 μ = snorm (f n - μ[g|ℱ n]) 1 μ := by
    refine fun m hm => snorm_congr_ae ((condexp_sub (hf.integrable m) hg).trans ?_)
    filter_upwards [hf.2 n m hm] with x hx
    simp only [hx, Pi.sub_apply]
  exact tendsto_nhds_unique (tendsto_atTop_of_eventually_const hev) ht
#align measure_theory.martingale.eq_condexp_of_tendsto_snorm MeasureTheory.Martingale.eq_condexp_of_tendsto_snorm

/-- Part b of the **L¹ martingale convergence theorem**: if `f` is a uniformly integrable martingale
adapted to the filtration `ℱ`, then for all `n`, `f n` is almost everywhere equal to the conditional
expectation of its limiting process wrt. `ℱ n`. -/
theorem Martingale.ae_eq_condexp_limitProcess (hf : Martingale f ℱ μ)
    (hbdd : UniformIntegrable f 1 μ) (n : ℕ) : f n =ᵐ[μ] μ[ℱ.limitProcess f μ|ℱ n] :=
  let ⟨_, hR⟩ := hbdd.2.2
  hf.eq_condexp_of_tendsto_snorm ((memℒp_limitProcess_of_snorm_bdd hbdd.1 hR).integrable le_rfl)
    (hf.submartingale.tendsto_snorm_one_limitProcess hbdd) n
#align measure_theory.martingale.ae_eq_condexp_limit_process MeasureTheory.Martingale.ae_eq_condexp_limitProcess

/-- Part c of the **L¹ martingale convergence theorem**: Given an integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges almost everywhere to `g`.

This martingale also converges to `g` in L¹ and this result is provided by
`MeasureTheory.Integrable.tendsto_snorm_condexp` -/
theorem Integrable.tendsto_ae_condexp (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g|ℱ n]) x) atTop (𝓝 (g x)) := by
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hunif : UniformIntegrable (fun n => μ[g|ℱ n]) 1 μ :=
    hg.uniformIntegrable_condexp_filtration
  obtain ⟨R, hR⟩ := hunif.2.2
  have hlimint : Integrable (ℱ.limitProcess (fun n => μ[g|ℱ n]) μ) μ :=
    (memℒp_limitProcess_of_snorm_bdd hunif.1 hR).integrable le_rfl
  suffices g =ᵐ[μ] ℱ.limitProcess (fun n x => (μ[g|ℱ n]) x) μ by
    filter_upwards [this, (martingale_condexp g ℱ μ).submartingale.ae_tendsto_limitProcess hR] with
      x heq ht
    rwa [heq]
  have : ∀ n s, MeasurableSet[ℱ n] s →
      ∫ x in s, g x ∂μ = ∫ x in s, ℱ.limitProcess (fun n x => (μ[g|ℱ n]) x) μ x ∂μ := by
    intro n s hs
    rw [← setIntegral_condexp (ℱ.le n) hg hs, ← setIntegral_condexp (ℱ.le n) hlimint hs]
    refine setIntegral_congr_ae (ℱ.le _ _ hs) ?_
    filter_upwards [(martingale_condexp g ℱ μ).ae_eq_condexp_limitProcess hunif n] with x hx _
    rw [hx]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hle (fun s _ _ => hg.integrableOn)
    (fun s _ _ => hlimint.integrableOn) (fun s hs => ?_) hgmeas.aeStronglyMeasurable'
    stronglyMeasurable_limitProcess.aeStronglyMeasurable'
  apply @MeasurableSpace.induction_on_inter _ _ _ (⨆ n, ℱ n)
    (MeasurableSpace.measurableSpace_iSup_eq ℱ) _ _ _ _ _ _ hs
  · rintro s ⟨n, hs⟩ t ⟨m, ht⟩ -
    by_cases hnm : n ≤ m
    · exact ⟨m, (ℱ.mono hnm _ hs).inter ht⟩
    · exact ⟨n, hs.inter (ℱ.mono (not_le.1 hnm).le _ ht)⟩
  · simp only [measure_empty, ENNReal.zero_lt_top, Measure.restrict_empty, integral_zero_measure,
      forall_true_left]
  · rintro t ⟨n, ht⟩ -
    exact this n _ ht
  · rintro t htmeas ht -
    have hgeq := @integral_add_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas (hg.trim hle hgmeas)
    have hheq := @integral_add_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas
      (hlimint.trim hle stronglyMeasurable_limitProcess)
    rw [add_comm, ← eq_sub_iff_add_eq] at hgeq hheq
    rw [setIntegral_trim hle hgmeas htmeas.compl,
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas.compl, hgeq, hheq, ←
      setIntegral_trim hle hgmeas htmeas, ←
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas, ← integral_trim hle hgmeas, ←
      integral_trim hle stronglyMeasurable_limitProcess, ← integral_univ,
      this 0 _ MeasurableSet.univ, integral_univ, ht (measure_lt_top _ _)]
  · rintro f hf hfmeas heq -
    rw [integral_iUnion (fun n => hle _ (hfmeas n)) hf hg.integrableOn,
      integral_iUnion (fun n => hle _ (hfmeas n)) hf hlimint.integrableOn]
    exact tsum_congr fun n => heq _ (measure_lt_top _ _)
#align measure_theory.integrable.tendsto_ae_condexp MeasureTheory.Integrable.tendsto_ae_condexp

/-- Part c of the **L¹ martingale convergence theorem**: Given an integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges in L¹ to `g`.

This martingale also converges to `g` almost everywhere and this result is provided by
`MeasureTheory.Integrable.tendsto_ae_condexp` -/
theorem Integrable.tendsto_snorm_condexp (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun n => snorm (μ[g|ℱ n] - g) 1 μ) atTop (𝓝 0) :=
  tendsto_Lp_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condexp.mono (ℱ.le n)).aestronglyMeasurable)
    (memℒp_one_iff_integrable.2 hg) hg.uniformIntegrable_condexp_filtration.2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun n => (stronglyMeasurable_condexp.mono (ℱ.le n)).aestronglyMeasurable)
      (hg.tendsto_ae_condexp hgmeas))
#align measure_theory.integrable.tendsto_snorm_condexp MeasureTheory.Integrable.tendsto_snorm_condexp

/-- **Lévy's upward theorem**, almost everywhere version: given a function `g` and a filtration
`ℱ`, the sequence defined by `𝔼[g | ℱ n]` converges almost everywhere to `𝔼[g | ⨆ n, ℱ n]`. -/
theorem tendsto_ae_condexp (g : Ω → ℝ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g|ℱ n]) x) atTop (𝓝 ((μ[g|⨆ n, ℱ n]) x)) := by
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[μ[g|⨆ n, ℱ n]|ℱ n]) x) atTop (𝓝 ((μ[g|⨆ n, ℱ n]) x)) :=
    integrable_condexp.tendsto_ae_condexp stronglyMeasurable_condexp
  have heq : ∀ n, ∀ᵐ x ∂μ, (μ[μ[g|⨆ n, ℱ n]|ℱ n]) x = (μ[g|ℱ n]) x := fun n =>
    condexp_condexp_of_le (le_iSup _ n) (iSup_le fun n => ℱ.le n)
  rw [← ae_all_iff] at heq
  filter_upwards [heq, ht] with x hxeq hxt
  exact hxt.congr hxeq
#align measure_theory.tendsto_ae_condexp MeasureTheory.tendsto_ae_condexp

/-- **Lévy's upward theorem**, L¹ version: given a function `g` and a filtration `ℱ`, the
sequence defined by `𝔼[g | ℱ n]` converges in L¹ to `𝔼[g | ⨆ n, ℱ n]`. -/
theorem tendsto_snorm_condexp (g : Ω → ℝ) :
    Tendsto (fun n => snorm (μ[g|ℱ n] - μ[g|⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => snorm (μ[μ[g|⨆ n, ℱ n]|ℱ n] - μ[g|⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) :=
    integrable_condexp.tendsto_snorm_condexp stronglyMeasurable_condexp
  have heq : ∀ n, ∀ᵐ x ∂μ, (μ[μ[g|⨆ n, ℱ n]|ℱ n]) x = (μ[g|ℱ n]) x := fun n =>
    condexp_condexp_of_le (le_iSup _ n) (iSup_le fun n => ℱ.le n)
  refine ht.congr fun n => snorm_congr_ae ?_
  filter_upwards [heq n] with x hxeq
  simp only [hxeq, Pi.sub_apply]
#align measure_theory.tendsto_snorm_condexp MeasureTheory.tendsto_snorm_condexp

end L1Convergence

end MeasureTheory
