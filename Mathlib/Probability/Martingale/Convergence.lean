/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Martingale.Upcrossing
public import Mathlib.Probability.Process.LimitProcess

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

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
  convergence theorem: an L¹-bounded submartingale strongly adapted to the filtration `ℱ`
  converges almost everywhere to its limit process.
* `MeasureTheory.Submartingale.memLp_limitProcess`: the limit process of an Lᵖ-bounded
  submartingale is Lᵖ.
* `MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess`: part a of the L¹ martingale
  convergence theorem: a uniformly integrable submartingale strongly adapted to the filtration `ℱ`
  converges almost everywhere and in L¹ to an integrable function which is measurable with respect
  to the σ-algebra `⨆ n, ℱ n`.
* `MeasureTheory.Martingale.ae_eq_condExp_limitProcess`: part b the L¹ martingale convergence
  theorem: if `f` is a uniformly integrable martingale strongly adapted to the filtration `ℱ`, then
  `f n` equals `𝔼[g | ℱ n]` almost everywhere where `g` is the limiting process of `f`.
* `MeasureTheory.Integrable.tendsto_ae_condExp`: part c the L¹ martingale convergence theorem:
  given an integrable function `g` with values in a Banach space, which is almost everywhere
  strongly measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, `𝔼[g | ℱ n]`
  converges almost everywhere to `g`.
* `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`: part c the L¹ martingale convergence theorem:
  given an integrable function `g` with values in a Banach space, which is almost everywhere
  strongly measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, `𝔼[g | ℱ n]`
  converges in L¹ to `g`.
* `MeasureTheory.tendsto_ae_condExp`: **Lévy's upward theorem** almost everywhere: for any
  function `g` with values in a Banach space, `𝔼[g | ℱ n]` converges almost everywhere to
  `𝔼[g | ⨆ n, ℱ n]`.
* `MeasureTheory.tendsto_eLpNorm_condExp`: **Lévy's upward theorem** in L¹: for any function `g`
  with values in a Banach space, `𝔼[g | ℱ n]` converges in L¹ to `𝔼[g | ⨆ n, ℱ n]`.

-/

public section


open TopologicalSpace Filter MeasureTheory.Filtration

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
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

In terms of implementation, we have `tendsto_of_no_upcrossings` which shows that
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


/-- If a stochastic process has a finite number of upcrossings from below `a` to above `b`,
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
  push Not
  intro k
  induction k with
  | zero => simp only [zero_le, exists_const]
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁
    exact ⟨N₂ + 1, Nat.succ_le_of_lt <|
      lt_of_le_of_lt hN (upcrossingsBefore_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩

/-- A stochastic process that frequently visits below `a` and above `b` has infinite upcrossings. -/
theorem upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : ∃ᶠ n in atTop, f n ω < a)
    (h₂ : ∃ᶠ n in atTop, b < f n ω) : upcrossings a b f ω = ∞ :=
  by_contradiction fun h => not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩

/-- A realization of a stochastic process with bounded upcrossings and bounded limit inferiors is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
theorem tendsto_of_upcrossings_lt_top (hf₁ : liminf (fun n => (‖f n ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
    ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun n => |f n ω|
  · rw [isBoundedUnder_le_abs] at h
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (Rat.cast_lt.1 hab)).ne
  · obtain ⟨a, b, hab, h₁, h₂⟩ := ENNReal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact
      False.elim ((hf₂ a b hab).ne (upcrossings_eq_top_of_frequently_lt (Rat.cast_lt.2 hab) h₁ h₂))

@[deprecated (since := "2026-09-17")]
alias tendsto_of_uncrossing_lt_top := tendsto_of_upcrossings_lt_top

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
theorem Submartingale.upcrossings_ae_lt_top' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) (hab : a < b) : ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ := by
  refine ae_lt_top (hf.stronglyAdapted.measurable_upcrossings hab) ?_
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le] at this
  · refine (lt_of_le_of_lt this (ENNReal.div_lt_top ?_ ?_)).ne
    · have hR' : ∀ n, ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ R + ‖a‖₊ * μ Set.univ := by
        intro n
        have hb := hbdd n
        rw [eLpNorm_one_eq_lintegral_enorm
          ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable] at hb
        refine (lintegral_mono ?_ : ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ ∫⁻ ω, ‖f n ω‖₊ + ‖a‖₊ ∂μ).trans ?_
        · intro ω
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ENNReal.coe_add, ENNReal.coe_le_coe]
          exact nnnorm_add_le _ _
        · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add hb le_rfl
      refine ne_of_lt (iSup_lt_iff.2 ⟨R + ‖a‖₊ * μ Set.univ, ENNReal.add_lt_top.2
        ⟨ENNReal.coe_lt_top, by finiteness⟩,
        fun n => le_trans ?_ (hR' n)⟩)
      refine lintegral_mono fun ω => ?_
      rw [ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
      · by_cases! hnonneg : 0 ≤ f n ω - a
        · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        · rw [posPart_eq_zero.2 hnonneg.le]
          exact norm_nonneg _
      · finiteness
    · simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
  · left; simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
  · left; finiteness

theorem Submartingale.upcrossings_ae_lt_top [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  rintro a b hab
  exact hf.upcrossings_ae_lt_top' hbdd (Rat.cast_lt.2 hab)

/-- An L¹-bounded submartingale converges almost everywhere. -/
theorem Submartingale.exists_ae_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero
    hbdd] with ω h₁ h₂
  exact tendsto_of_upcrossings_lt_top h₂ h₁

theorem Submartingale.exists_ae_trim_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ.trim (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _ : ⨆ n, ℱ n ≤ m0),
      ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  let := (⨆ n, ℱ n)
  rw [ae_iff, trim_measurableSet_eq]
  · exact hf.exists_ae_tendsto_of_bdd hbdd
  · exact MeasurableSet.compl <| measurableSet_exists_tendsto
      fun n => (hf.stronglyMeasurable n).measurable.mono (le_iSup _ n) le_rfl

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
theorem Submartingale.ae_tendsto_limitProcess [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  classical
  apply HasLimitProcess.ae_tendsto_limitProcess
  set g' : Ω → ℝ := fun ω => if h : ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hg' : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dite_eq_left hω]
    exact hω.choose_spec
  have hg'm : AEStronglyMeasurable[⨆ n, ℱ n] g' (μ.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (fun n => ((hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
theorem Submartingale.memLp_limitProcess {p : ℝ≥0∞} (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : MemLp (ℱ.limitProcess f μ) p μ :=
  memLp_limitProcess_of_eLpNorm_bdd
    (fun n => ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) hbdd

end AeConvergence

section L1Convergence

variable [IsFiniteMeasure μ] {g : Ω → ℝ}

/-!

### L¹ martingale convergence theorem

We will now prove the L¹ martingale convergence theorems.

The L¹ martingale convergence theorem states that:
(a) if `f` is a uniformly integrable (in the probability sense) submartingale strongly adapted to
  the filtration `ℱ`, it converges in L¹ to an integrable function `g` which is measurable with
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
    \|\mathbb{E}[f_m - g \mid \mathcal{F}_n]\|_1 \le \|f_m - g\|_1.
$$
Thus, taking $m \to \infty$ provides the almost everywhere equality.

Finally, to prove (c), we define $f_n := \mathbb{E}[h \mid \mathcal{F}_n]$. It is clear that
$(f_n)_n$ is a martingale by the tower property for conditional expectations. Furthermore,
$(f_n)_n$ is uniformly integrable in the probability sense. Indeed, as a single function is
uniformly integrable in the measure theory sense, for all $\epsilon > 0$, there exists some
$\delta > 0$ such that for all measurable set $A$ with $\mu(A) < δ$, we have
$\mathbb{E}|h|\mathbf{1}_A < \epsilon$. So, since for sufficiently large $\lambda$, by the Markov
inequality, we have for all $n$,
$$
  \mu(|f_n| \ge \lambda) \le \lambda^{-1}\mathbb{E}|f_n| \le \lambda^{-1}\mathbb{E}|h| < \delta,
$$
we have for sufficiently large $\lambda$, for all $n$,
$$
  \mathbb{E}|f_n|\mathbf{1}_{|f_n| \ge \lambda} \le
    \mathbb{E}|h|\mathbf{1}_{|f_n| \ge \lambda} < \epsilon,
$$
implying $(f_n)_n$ is uniformly integrable. Now, to prove $f_n \to h$ almost everywhere and in
L¹, it suffices to show that $h = g$ almost everywhere where $g$ is the almost everywhere and L¹
limit of $(f_n)_n$ from part (b) of the theorem. By noting that, for all $s \in \mathcal{F}_n$,
we have
$$
  \mathbb{E}g\mathbf{1}_s = \mathbb{E}[\mathbb{E}[g \mid \mathcal{F}_n]\mathbf{1}_s] =
    \mathbb{E}[\mathbb{E}[h \mid \mathcal{F}_n]\mathbf{1}_s] = \mathbb{E}h\mathbf{1}_s
$$
where $\mathbb{E}[g \mid \mathcal{F}_n] = \mathbb{E}[h \mid \mathcal{F}_n]$ almost everywhere
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
strongly adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. -/
theorem Submartingale.tendsto_eLpNorm_one_limitProcess (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hunif.2
  have hmeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hf.stronglyMeasurable n).mono (ℱ.le _)).aestronglyMeasurable
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memLp_limitProcess_of_eLpNorm_bdd hmeas hR) hunif.1
    (tendstoInMeasure_of_tendsto_ae hmeas <| hf.ae_tendsto_limitProcess hR)

theorem Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
  let ⟨_, hR⟩ := hunif.2
  hf.ae_tendsto_limitProcess hR

/-- If a martingale `f` strongly adapted to `ℱ` converges in L¹ to `g`, then for all `n`, `f n` is
almost everywhere equal to `𝔼[g | ℱ n]`. -/
theorem Martingale.eq_condExp_of_tendsto_eLpNorm {μ : Measure Ω} (hf : Martingale f ℱ μ)
    (hg : Integrable g μ) (hgtends : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) (n : ℕ) :
    f n =ᵐ[μ] μ[g | ℱ n] := by
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff one_ne_zero]
  have ht : Tendsto (fun m => eLpNorm (μ[f m - g | ℱ n]) 1 μ) atTop (𝓝 0) :=
    haveI hint : ∀ m, Integrable (f m - g) μ := fun m => (hf.integrable m).sub hg
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (fun m => zero_le)
      fun m => eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hev : ∀ m ≥ n, eLpNorm (μ[f m - g | ℱ n]) 1 μ = eLpNorm (f n - μ[g | ℱ n]) 1 μ := by
    refine fun m hm => eLpNorm_congr_ae ((condExp_sub (hf.integrable m) hg _).trans ?_)
    filter_upwards [hf.2 n m hm] with x hx
    simp only [hx, Pi.sub_apply]
  exact tendsto_nhds_unique (tendsto_atTop_of_eventually_const hev) ht

/-- Part b of the **L¹ martingale convergence theorem**: if `f` is a uniformly integrable martingale
strongly adapted to the filtration `ℱ`, then for all `n`, `f n` is almost everywhere equal to the
conditional expectation of its limiting process w.r.t. `ℱ n`. -/
theorem Martingale.ae_eq_condExp_limitProcess (hf : Martingale f ℱ μ)
    (hbdd : UniformIntegrable f 1 μ) (n : ℕ) : f n =ᵐ[μ] μ[ℱ.limitProcess f μ | ℱ n] :=
  let ⟨_, hR⟩ := hbdd.2
  hf.eq_condExp_of_tendsto_eLpNorm
    ((memLp_limitProcess_of_eLpNorm_bdd hbdd.aestronglyMeasurable hR).integrable le_rfl)
    (hf.submartingale.tendsto_eLpNorm_one_limitProcess hbdd) n

/-- The real case of `MeasureTheory.Integrable.tendsto_ae_condExp`, used to prove the general
case. -/
private theorem Integrable.tendsto_ae_condExp_real (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 (g x)) := by
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hunif : UniformIntegrable (fun n => μ[g | ℱ n]) 1 μ :=
    hg.uniformIntegrable_condExp_filtration
  obtain ⟨R, hR⟩ := hunif.2
  have hlimint : Integrable (ℱ.limitProcess (fun n => μ[g | ℱ n]) μ) μ :=
    (memLp_limitProcess_of_eLpNorm_bdd hunif.aestronglyMeasurable hR).integrable le_rfl
  suffices g =ᵐ[μ] ℱ.limitProcess (fun n x => (μ[g | ℱ n]) x) μ by
    filter_upwards [this, (martingale_condExp g ℱ μ).submartingale.ae_tendsto_limitProcess hR] with
      x heq ht
    rwa [heq]
  have : ∀ n s, MeasurableSet[ℱ n] s →
      ∫ x in s, g x ∂μ = ∫ x in s, ℱ.limitProcess (fun n x => (μ[g | ℱ n]) x) μ x ∂μ := by
    intro n s hs
    rw [← setIntegral_condExp (ℱ.le n) hg hs, ← setIntegral_condExp (ℱ.le n) hlimint hs]
    refine setIntegral_congr_ae (ℱ.le _ _ hs) ?_
    filter_upwards [(martingale_condExp g ℱ μ).ae_eq_condExp_limitProcess hunif n] with x hx _
    rw [hx]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hle (fun s _ _ => hg.integrableOn)
    (fun s _ _ => hlimint.integrableOn) (fun s hs _ => ?_) hgmeas.aestronglyMeasurable
    stronglyMeasurable_limitProcess.aestronglyMeasurable
  have hpi : IsPiSystem {s | ∃ n, MeasurableSet[ℱ n] s} := by
    rw [Set.ofPred_exists]
    exact isPiSystem_iUnion_of_monotone _ (fun n ↦ (ℱ n).isPiSystem_measurableSet) fun _ _ ↦ ℱ.mono
  induction s, hs
    using MeasurableSpace.induction_on_inter (MeasurableSpace.measurableSpace_iSup_eq ℱ) hpi with
  | empty =>
    simp only [Measure.restrict_empty, integral_zero_measure]
  | basic s hs =>
    rcases hs with ⟨n, hn⟩
    exact this n _ hn
  | compl t htmeas ht =>
    have hgeq := @setIntegral_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas (hg.trim hle hgmeas)
    have hheq := @setIntegral_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas
      (hlimint.trim hle stronglyMeasurable_limitProcess)
    rw [setIntegral_trim hle hgmeas htmeas.compl,
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas.compl, hgeq, hheq, ←
      setIntegral_trim hle hgmeas htmeas, ←
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas, ← integral_trim hle hgmeas, ←
      integral_trim hle stronglyMeasurable_limitProcess, ← setIntegral_univ,
      this 0 _ MeasurableSet.univ, setIntegral_univ, ht (measure_lt_top _ _)]
  | iUnion f hf hfmeas heq =>
    rw [integral_iUnion (fun n => hle _ (hfmeas n)) hf hg.integrableOn,
      integral_iUnion (fun n => hle _ (hfmeas n)) hf hlimint.integrableOn]
    exact tsum_congr fun n => heq _ (measure_lt_top _ _)

/-- The real case of `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`, used to prove the general
case. -/
private theorem Integrable.tendsto_eLpNorm_condExp_real (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable)
    (memLp_one_iff_integrable.2 hg) hg.uniformIntegrable_condExp_filtration.1
    (tendstoInMeasure_of_tendsto_ae
      (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable)
      (hg.tendsto_ae_condExp_real hgmeas))

end L1Convergence

section L1ConvergenceBanach

/-! ### Lévy's upward theorem in `L¹` for functions with values in a Banach space

The set of functions `g` for which `μ[g | ℱ n]` tends to `g` in `L¹` is closed under addition and
under limits in `L¹`, and it contains the indicators `s.indicator fun _ ↦ c` of the sets `s` which
are measurable with respect to `⨆ n, ℱ n` by the real case. Hence it contains all integrable
functions which are almost everywhere strongly measurable with respect to `⨆ n, ℱ n`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {g : Ω → E}

/-- If `μ[a j | ℱ n]` tends to `a j` in `L¹` as `n` tends to infinity for all `j`, and if `a j`
tends to `g` in `L¹` along a nontrivial filter, then `μ[g | ℱ n]` tends to `g` in `L¹`. -/
private lemma tendsto_eLpNorm_condExp_sub_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (hg : Integrable g μ) {a : ι → Ω → E} (ha_int : ∀ j, Integrable (a j) μ)
    (ha_lim : Tendsto (fun j ↦ eLpNorm (a j - g) 1 μ) l (𝓝 0))
    (ha : ∀ j, Tendsto (fun n ↦ eLpNorm (μ[a j | ℱ n] - a j) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by simp)
  obtain ⟨j, hj⟩ := (ha_lim.eventually_le_const hε3).exists
  obtain ⟨n₀, hn₀⟩ := ENNReal.tendsto_atTop_zero.1 (ha j) (ε / 3) hε3
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have h_eq : μ[g | ℱ n] - g =ᵐ[μ] μ[g - a j | ℱ n] + (μ[a j | ℱ n] - a j) + (a j - g) := by
    filter_upwards [condExp_sub hg (ha_int j) (ℱ n)] with ω hω
    simp only [Pi.sub_apply, Pi.add_apply, hω]
    abel
  rw [eLpNorm_congr_ae h_eq]
  calc eLpNorm (μ[g - a j | ℱ n] + (μ[a j | ℱ n] - a j) + (a j - g)) 1 μ
    _ ≤ eLpNorm (μ[g - a j | ℱ n]) 1 μ + eLpNorm (μ[a j | ℱ n] - a j) 1 μ
        + eLpNorm (a j - g) 1 μ :=
      (eLpNorm_add_le le_rfl).trans (add_le_add_left (eLpNorm_add_le le_rfl) _)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans ((eLpNorm_sub_comm ..).trans_le hj)
      · exact hn₀ n hn
    _ = ε := ENNReal.add_thirds ε

variable [IsFiniteMeasure μ]

/-- Lévy's upward theorem in `L¹` for the indicator of a set, which follows from the real case.
Auxiliary result for `Integrable.tendsto_eLpNorm_condExp`. -/
private lemma tendsto_eLpNorm_condExp_sub_indicator_const (c : E) {s : Set Ω}
    (hs : MeasurableSet[⨆ n, ℱ n] s) :
    Tendsto (fun n ↦ eLpNorm (μ[s.indicator (fun _ ↦ c) | ℱ n] - s.indicator (fun _ ↦ c)) 1 μ)
      atTop (𝓝 0) := by
  have hle : ⨆ n, ℱ n ≤ m0 := iSup_le ℱ.le
  -- `u` is the real indicator of `s`, and `T` is the linear map `x ↦ x • c`
  let u : Ω → ℝ := s.indicator fun _ ↦ 1
  have hu_int : Integrable u μ := (integrable_const 1).indicator (hle s hs)
  have hu : Tendsto (fun n ↦ eLpNorm (μ[u | ℱ n] - u) 1 μ) atTop (𝓝 0) :=
    hu_int.tendsto_eLpNorm_condExp_real (stronglyMeasurable_const.indicator hs)
  let T : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ c
  have hT : T ∘ u = s.indicator fun _ ↦ c := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [T, u, hω]
  have h_bound (n : ℕ) :
      eLpNorm (μ[s.indicator (fun _ ↦ c) | ℱ n] - s.indicator (fun _ ↦ c)) 1 μ
        ≤ ‖c‖₊ * eLpNorm (μ[u | ℱ n] - u) 1 μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
      (integrable_condExp.sub ((integrable_const c).indicator (hle s hs))).aestronglyMeasurable ?_ 1
    filter_upwards [T.comp_condExp_comm hu_int (m := ℱ n)] with ω hω
    rw [hT] at hω
    have h_eq : (μ[s.indicator (fun _ ↦ c) | ℱ n] - s.indicator fun _ ↦ c) ω
        = (μ[u | ℱ n] ω - u ω) • c := by
      rw [Pi.sub_apply, ← hω, ← congrFun hT ω, sub_smul]
      rfl
    rw [h_eq, enorm_smul, mul_comm, enorm_eq_nnnorm c, Pi.sub_apply]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) h_bound
  simpa using ENNReal.Tendsto.const_mul hu (.inr ENNReal.coe_ne_top)

/-- **Lévy's upward theorem**, `L¹` version, for a function with values in a Banach space: if `g`
is integrable and almost everywhere strongly measurable with respect to `⨆ n, ℱ n`, then the
conditional expectations `μ[g | ℱ n]` tend to `g` in `L¹`.

The convergence also holds almost everywhere: see `MeasureTheory.Integrable.tendsto_ae_condExp`. -/
theorem Integrable.tendsto_eLpNorm_condExp (hg : Integrable g μ)
    (hgmeas : AEStronglyMeasurable[⨆ n, ℱ n] g μ) :
    Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) := by
  refine MemLp.induction_stronglyMeasurable (iSup_le ℱ.le) ENNReal.one_ne_top
    (fun g ↦ Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0)) ?_ ?_ ?_ ?_
    (memLp_one_iff_integrable.2 hg) hgmeas
  · exact fun c s hs _ ↦ tendsto_eLpNorm_condExp_sub_indicator_const c hs
  · intro f₁ f₂ _ hf₁ hf₂ _ _ hPf₁ hPf₂
    rw [memLp_one_iff_integrable] at hf₁ hf₂
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hPf₁.add hPf₂) (fun _ ↦ zero_le) fun n ↦ ?_
    have h_eq : μ[f₁ + f₂ | ℱ n] - (f₁ + f₂) =ᵐ[μ] (μ[f₁ | ℱ n] - f₁) + (μ[f₂ | ℱ n] - f₂) := by
      filter_upwards [condExp_add hf₁ hf₂ (ℱ n)] with ω hω
      simp only [Pi.sub_apply, Pi.add_apply, hω]
      abel
    rw [eLpNorm_congr_ae h_eq]
    exact eLpNorm_add_le le_rfl
  · refine IsSeqClosed.isClosed fun a f ha h_lim ↦ ?_
    have h_lim' : Tendsto (fun j ↦ (a j : Lp E 1 μ)) atTop (𝓝 (f : Lp E 1 μ)) :=
      (continuous_subtype_val.tendsto f).comp h_lim
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h_lim'
    exact tendsto_eLpNorm_condExp_sub_of_tendsto (L1.integrable_coeFn _)
      (fun j ↦ L1.integrable_coeFn _) h_lim' ha
  · intro f₁ f₂ hf _ hPf₁
    refine hPf₁.congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [condExp_congr_ae hf (m := ℱ n), hf] with ω hω hω'
    rw [Pi.sub_apply, Pi.sub_apply, hω, hω']

variable (ℱ) in
/-- **Lévy's upward theorem**, `L¹` version, for a function with values in a Banach space: the
conditional expectations `μ[g | ℱ n]` tend to `μ[g | ⨆ n, ℱ n]` in `L¹`.

The convergence also holds almost everywhere: see `MeasureTheory.tendsto_ae_condExp`. -/
theorem tendsto_eLpNorm_condExp (g : Ω → E) :
    Tendsto (fun n ↦ eLpNorm (μ[g | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) := by
  have h : Tendsto (fun n ↦ eLpNorm (μ[μ[g | ⨆ n, ℱ n] | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) atTop
      (𝓝 0) :=
    integrable_condExp.tendsto_eLpNorm_condExp stronglyMeasurable_condExp.aestronglyMeasurable
  refine h.congr fun n ↦ eLpNorm_congr_ae ?_
  have h_eq : μ[μ[g | ⨆ n, ℱ n] | ℱ n] =ᵐ[μ] μ[g | ℱ n] :=
    condExp_condExp_of_le (le_iSup _ n) (iSup_le ℱ.le)
  filter_upwards [h_eq] with ω hω
  rw [Pi.sub_apply, Pi.sub_apply, hω]

end L1ConvergenceBanach

section AeConvergenceBanach

/-! ### Lévy's upward theorem almost everywhere for functions with values in a Banach space

We deduce the Banach-valued case from the real case. Let `g` be integrable and strongly measurable
with respect to `⨆ n, ℱ n`, and let `D` be a countable dense subset of its range. For all `c ∈ D`,
the real case applied to `‖g - c‖` shows that `μ[‖g - c‖ | ℱ n]` tends to `‖g - c‖` almost
everywhere, and the conditional Jensen inequality gives `‖μ[g | ℱ n] - c‖ ≤ μ[‖g - c‖ | ℱ n]`.
Hence for almost every `ω`, the limsup of `‖μ[g | ℱ n] ω - g ω‖` is at most `2 * ‖g ω - c‖` for
all `c ∈ D`, so it is zero. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasure μ] {g : Ω → E}

/-- Auxiliary result for `Integrable.tendsto_ae_condExp`: the case of a function which is strongly
measurable with respect to `⨆ n, ℱ n`. -/
private lemma Integrable.tendsto_ae_condExp_of_stronglyMeasurable (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | ℱ n] ω) atTop (𝓝 (g ω)) := by
  obtain ⟨D, -, hD, hD_dense⟩ := hgmeas.isSeparable_range.exists_countable_dense_subset
  have h_tendsto : ∀ᵐ ω ∂μ, ∀ c ∈ D,
      Tendsto (fun n ↦ μ[fun ω ↦ ‖g ω - c‖ | ℱ n] ω) atTop (𝓝 ‖g ω - c‖) :=
    (ae_ball_iff hD).2 fun c _ ↦ (hg.sub (integrable_const c)).norm.tendsto_ae_condExp_real
      (hgmeas.sub stronglyMeasurable_const).norm
  have h_le : ∀ᵐ ω ∂μ, ∀ c ∈ D, ∀ n, ‖μ[g | ℱ n] ω - c‖ ≤ μ[fun ω ↦ ‖g ω - c‖ | ℱ n] ω := by
    refine (ae_ball_iff hD).2 fun c _ ↦ ae_all_iff.2 fun n ↦ ?_
    filter_upwards [norm_condExp_le (μ := μ) (m := ℱ n) (g - fun _ ↦ c),
      condExp_sub hg (integrable_const c) (ℱ n)] with ω h_norm h_sub
    rw [h_sub, condExp_const (ℱ.le n)] at h_norm
    exact h_norm
  filter_upwards [h_tendsto, h_le] with ω h_tendsto h_le
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨c, hcD, hc⟩ := Metric.mem_closure_iff.1 (hD_dense (Set.mem_range_self ω)) _ hε3
  obtain ⟨N, hN⟩ := eventually_atTop.1 <|
    (h_tendsto c hcD).eventually_lt_const (lt_add_of_pos_right _ hε3)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h_dist : dist (μ[g | ℱ n] ω) c < dist (g ω) c + ε / 3 := by
    rw [dist_eq_norm, dist_eq_norm]
    exact (h_le c hcD n).trans_lt (hN n hn)
  linarith [dist_triangle_right (μ[g | ℱ n] ω) (g ω) c]

/-- Part c of the **L¹ martingale convergence theorem**, almost everywhere version, for a function
with values in a Banach space: if `g` is integrable and almost everywhere strongly measurable with
respect to `⨆ n, ℱ n`, then the conditional expectations `μ[g | ℱ n]` tend to `g` almost
everywhere.

The convergence also holds in `L¹`: see `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`. -/
theorem Integrable.tendsto_ae_condExp (hg : Integrable g μ)
    (hgmeas : AEStronglyMeasurable[⨆ n, ℱ n] g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | ℱ n] ω) atTop (𝓝 (g ω)) := by
  obtain ⟨g', hg'_meas, hgg'⟩ := hgmeas
  have h_eq : ∀ᵐ ω ∂μ, ∀ n, μ[g' | ℱ n] ω = μ[g | ℱ n] ω :=
    ae_all_iff.2 fun n ↦ condExp_congr_ae hgg'.symm
  filter_upwards [(hg.congr hgg').tendsto_ae_condExp_of_stronglyMeasurable hg'_meas, hgg', h_eq]
    with ω hω hω' h_eq
  rw [hω']
  exact hω.congr h_eq

variable (ℱ) in
/-- **Lévy's upward theorem**, almost everywhere version, for a function with values in a Banach
space: the conditional expectations `μ[g | ℱ n]` tend to `μ[g | ⨆ n, ℱ n]` almost everywhere.

The convergence also holds in `L¹`: see `MeasureTheory.tendsto_eLpNorm_condExp`. -/
theorem tendsto_ae_condExp (g : Ω → E) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | ℱ n] ω) atTop (𝓝 (μ[g | ⨆ n, ℱ n] ω)) := by
  have h : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[μ[g | ⨆ n, ℱ n] | ℱ n] ω) atTop
      (𝓝 (μ[g | ⨆ n, ℱ n] ω)) :=
    integrable_condExp.tendsto_ae_condExp stronglyMeasurable_condExp.aestronglyMeasurable
  have h_eq : ∀ᵐ ω ∂μ, ∀ n, μ[μ[g | ⨆ n, ℱ n] | ℱ n] ω = μ[g | ℱ n] ω :=
    ae_all_iff.2 fun n ↦ condExp_condExp_of_le (le_iSup _ n) (iSup_le ℱ.le)
  filter_upwards [h, h_eq] with ω hω h_eq
  exact hω.congr h_eq

end AeConvergenceBanach

end MeasureTheory
