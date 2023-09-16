/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Data.Finset.Interval
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Gagliardo-Nirenberg-Sobolev inequality
-/


open scoped Classical BigOperators Topology ENNReal
open Filter
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}

section Finset

open Finset

namespace Real

theorem prod_rpow {ι} (s : Finset ι) {f : ι → ℝ} (hf : 0 ≤ f) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r :=
  finset_prod_rpow s f (fun i _ ↦ hf i) r

end Real

namespace NNReal

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

theorem rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
  x ^ (y + z) = x ^ y * x ^ z := by
  by_cases h : y + z = 0
  · obtain rfl : y = 0 := by linarith
    obtain rfl : z = 0 := by linarith
    simp [h]
  · exact rpow_add' _ h

end NNReal

namespace ENNReal

open NNReal

theorem rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

-- unused
theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_lt_top h2f |>.ne

-- unused
theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i in s, (f i : ℝ≥0∞) ^ r = ((∏ i in s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

end ENNReal

end Finset

section Calculus

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] [Fintype ι]
variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiff_update (k : ℕ∞) (x : ∀ i, E i) (i : ι) : ContDiff 𝕜 k (Function.update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

theorem hasFDerivAt_sub_const {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]  {x : E} (c : E) :
    HasFDerivAt (· - c) (ContinuousLinearMap.id 𝕜 (E)) x :=
  (hasFDerivAt_id x).sub_const c

theorem hasFDerivAt_update {x : ∀ i, E i} {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i)
      (ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i)))) y := by
  set l := (ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))))
  have update_eq : Function.update x i = (fun _ ↦ x) + l ∘ (· - x i)
  · ext t j
    dsimp [Function.update]
    split_ifs with hji
    · subst hji
      simp
    · simp
  rw [update_eq]
  convert (hasFDerivAt_const _ _).add (l.hasFDerivAt.comp y (hasFDerivAt_sub_const (x i)))
  rw [zero_add, ContinuousLinearMap.comp_id]

theorem fderiv_update {x : ∀ i, E i} {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y =
      ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))) :=
  (hasFDerivAt_update y).fderiv

theorem hasDerivAt_update {x : ι → 𝕜} {i : ι} (y : 𝕜) :
    HasDerivAt (Function.update x i) (Pi.single i (1:𝕜)) y := by
  convert (hasFDerivAt_update (E := fun _ ↦ 𝕜) y).hasDerivAt
  ext z j
  rw [Pi.single, Function.update_apply]
  split_ifs with h
  · simp [h]
  · simp [Function.update_noteq h]

theorem deriv_update {x : ι → 𝕜} {i : ι} (y : 𝕜) :
    deriv (Function.update x i) y = (Pi.single i (1:𝕜)) :=
  (hasDerivAt_update y).deriv

open NNReal

theorem Pi.nnnorm_single (y : E i) : ‖Pi.single i y‖₊ = ‖y‖₊ := by
  classical
  have H : ∀ b, ‖single i y b‖₊ = single (f := fun _ ↦ ℝ≥0) i ‖y‖₊ b
  · intro b
    refine Pi.apply_single (fun i (x : E i) ↦ ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite,
    Finset.filter_eq' (Finset.univ : Finset ι)]

theorem Pi.norm_single (y : E i) : ‖Pi.single i y‖ = ‖y‖ :=
  congr_arg Subtype.val (Pi.nnnorm_single y)

end Calculus

section RealCalculus

open Set MeasureTheory

variable {E : Type*} {f f' : ℝ → E} {g g' : ℝ → ℝ} {a b l : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a)` and continuity on `(-∞, a]`.-/
theorem integral_Iio_of_hasDerivAt_of_tendsto (hcont : ContinuousOn f (Iic a))
    (hderiv : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  refine' tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) _
  apply Tendsto.congr' _ (hf.const_sub _)
  filter_upwards [Iic_mem_atBot a] with x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
  rw [intervalIntegrable_iff_integrable_Ioc_of_le hx]
  exact f'int.mono (fun y hy => hy.2) le_rfl

theorem atBot_le_cocompact : atBot ≤ cocompact ℝ := by simp
theorem atTop_le_cocompact : atTop ≤ cocompact ℝ := by simp

theorem _root_.Filter.EventuallyEq.tendsto [TopologicalSpace β] {f : α → β} {l : Filter α} {a : β}
    (hf : f =ᶠ[l] fun _ ↦ a) : Tendsto f l (𝓝 a) :=
  tendsto_nhds_of_eventually_eq hf

-- very special case of `integral_Iio_of_hasDerivAt_of_tendsto`.
theorem _root_.HasCompactSupport.integral_deriv_eq {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Iic b, deriv f x = f b := by
  have := fun x (_ : x ∈ Iio b) ↦ hf.differentiable le_rfl x |>.hasDerivAt
  rw [integral_Iio_of_hasDerivAt_of_tendsto hf.continuous.continuousOn this, sub_zero]
  refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono atBot_le_cocompact |>.tendsto

end RealCalculus


open Set Function MeasurableSpace Finset

namespace MeasureTheory

/-- A different formulation of Hölder's inequality for two functions -/
theorem _root_.ENNReal.lintegral_mul_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ∫⁻ a, f a ^ p * g a ^ q ∂μ ≤ (∫⁻ a, f a ∂μ) ^ p * (∫⁻ a, g a ∂μ) ^ q := by
  rcases hp.eq_or_lt with rfl|hp
  · simp at hpq
    subst hpq
    simp
  rcases hq.eq_or_lt with rfl|hq
  · simp at hpq
    subst hpq
    simp
  have h2p : 1 < 1 / p
  · rw [one_div]
    apply one_lt_inv hp
    linarith
  have h2pq : 1 / (1 / p) + 1 / (1 / q) = 1
  · simp [hp.ne', hq.ne', hpq]
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ ⟨h2p, h2pq⟩ (hf.pow_const p) (hg.pow_const q)
  simpa [← ENNReal.rpow_mul, hp.ne', hq.ne'] using this


@[to_additive]
theorem prod_insert_div [CommGroup β] [DecidableEq α] (ha : a ∉ s) {f : α → β} :
    (∏ x in insert a s, f x) / f a = ∏ x in s, f x := by simp [ha]

attribute [gcongr] ENNReal.rpow_le_rpow
set_option maxHeartbeats 300000 in
/-- A version of Hölder with multiple arguments -/
theorem _root_.ENNReal.lintegral_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    (hs : s.Nonempty)
    {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ) {p : ι → ℝ} (hp : ∑ i in s, p i = 1)
    (h2p : ∀ i ∈ s, 0 ≤ p i) :
      ∫⁻ a, ∏ i in s, f i a ^ p i ∂μ ≤
      ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
  induction s using Finset.induction generalizing p
  case empty =>
    simp at hs
  case insert i₀ s hi₀ ih =>
    rcases eq_or_ne (p i₀) 1 with h2i₀|h2i₀
    · simp [hi₀]
      have h2p : ∀ i ∈ s, p i = 0
      · simpa [hi₀, h2i₀, sum_eq_zero_iff_of_nonneg (fun i hi ↦ h2p i <| mem_insert_of_mem hi)]
          using hp
      calc ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, 1 ∂μ := by
            congr! 3 with x
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, 1 := by simp [h2i₀]
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
            congr 1
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
    · have hs : s.Nonempty
      · rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp [h2i₀] at hp
      have hpi₀ : 0 ≤ 1 - p i₀
      · simp_rw [sub_nonneg, ← hp, single_le_sum h2p (mem_insert_self ..)]
      have h2pi₀ : 1 - p i₀ ≠ 0
      · rwa [sub_ne_zero, ne_comm]
      let q := fun i ↦ p i / (1 - p i₀)
      have hq : ∑ i in s, q i = 1
      · rw [← sum_div, ← sum_insert_sub hi₀, hp, div_self h2pi₀]
      have h2q : ∀ i ∈ s, 0 ≤ q i
      · exact fun i hi ↦ div_nonneg (h2p i <| mem_insert_of_mem hi) hpi₀
      calc ∫⁻ a, ∏ i in insert i₀ s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, f i a ^ p i ∂μ := by simp [hi₀]
        _ = ∫⁻ a, f i₀ a ^ p i₀ * (∏ i in s, f i a ^ q i) ^ (1 - p i₀) ∂μ := by
            simp [← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel (h := h2pi₀)]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∫⁻ a, ∏ i in s, f i a ^ q i ∂μ) ^ (1 - p i₀) := by
            apply ENNReal.lintegral_mul_norm_pow_le
            · exact hf i₀ <| mem_insert_self ..
            · exact s.aemeasurable_prod <| fun i hi ↦ (hf i <| mem_insert_of_mem hi).pow_const _
            · exact h2p i₀ <| mem_insert_self ..
            · exact hpi₀
            · apply add_sub_cancel'_right
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∏ i in s, (∫⁻ a, f i a ∂μ) ^ q i) ^ (1 - p i₀) := by
            gcongr -- the behavior of gcongr is heartbeat-dependent, which makes code really fragile...
            exact ih hs (fun i hi ↦ hf i <| mem_insert_of_mem hi) hq h2q
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
            simp [← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel (h := h2pi₀)]
        _ = ∏ i in insert i₀ s, (∫⁻ a, f i a ∂μ) ^ p i := by simp [hi₀]

/-- A version of Hölder with multiple arguments, one of which plays a distinguished role -/
theorem _root_.ENNReal.lintegral_mul_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    {g : α →  ℝ≥0∞} {f : ι → α → ℝ≥0∞} (hg : AEMeasurable g μ) (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    (q : ℝ) {p : ι → ℝ} (hpq : q + ∑ i in s, p i = 1) (hq :  0 ≤ q)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∫⁻ a, g a ^ q * ∏ i in s, f i a ^ p i ∂μ ≤
      (∫⁻ a, g a ∂μ) ^ q * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
  calc
    ∫⁻ t, g t ^ q * ∏ j in s, (f j t) ^ p j ∂μ
      = ∫⁻ t, ∏ j in insertNone s,
            Option.elim j (g t) (fun j ↦ f j t) ^ Option.elim j q p ∂μ := by
          congr! 1
          ext t
          rw [prod_insertNone]
          dsimp
    _ ≤ ∏ j in insertNone s,
          (∫⁻ t, Option.elim j (g t) (fun j ↦ f j t) ∂μ) ^ Option.elim j q p := by
          refine ENNReal.lintegral_prod_norm_pow_le _ insertNone_nonempty ?_ ?_ ?_
          · rintro (_|i) hi
            · exact hg
            · refine hf i ?_
              simpa using hi
          · simp_rw [sum_insertNone, Option.elim]
            exact hpq
          · rintro (_|i) hi
            · exact hq
            · refine hp i ?_
              simpa using hi
    _ = (∫⁻ t, g t ∂μ) ^ q * ∏ j in s, (∫⁻ t, f j t ∂μ) ^ p j := by
          -- this proof could be `simp [prod_insertNone]` but that's too slow
          simp_rw [prod_insertNone]
          dsimp

end MeasureTheory

open MeasureTheory

section Sobolev

open TopologicalSpace

variable [Fintype ι] {π : ι → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
  [∀ i, SigmaFinite (μ i)] (u : (ι → ℝ) → ℝ) {f : (∀ i, π i) → ℝ≥0∞}


local prefix:max "#" => Fintype.card

/--
  The function that is central in the inductive proof of the Sobolev inequality.
-/
def rhsAux (p : ℝ) (f : (∀ i, π i) → ℝ≥0∞) (s : Finset ι) (x : ∀ i, π i) : ℝ≥0∞ :=
  (∫⋯∫_s, f ∂μ) x ^ (1 - (sᶜ.card - 1 : ℝ) * p) *
    ∏ i in sᶜ, (∫⋯∫_insert i s, f ∂μ) x ^ p

lemma rhsAux_empty' (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    rhsAux μ p f ∅ x = f x ^ (1 - (#ι - 1 : ℝ) * p) * ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ p := by
  simp [rhsAux, marginal_singleton, card_univ]

lemma rhsAux_empty [Nontrivial ι] (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    rhsAux μ ((1 : ℝ) / (#ι - 1 : ℝ)) f ∅ x
    = ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := by
  rw [rhsAux_empty']
  convert one_mul _
  convert ENNReal.rpow_zero
  have : (1:ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have : (0:ℝ) < #ι - 1 := by linarith
  field_simp

lemma rhsAux_univ' (p : ℝ) (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
   rhsAux μ p f univ x = (∫⁻ x, f x ∂(Measure.pi μ)) ^ (1 + p) := by
  simp [rhsAux, marginal_univ, Finset.card_univ]

lemma rhsAux_univ [Nontrivial ι] (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
   rhsAux μ ((1 : ℝ) / (#ι - 1 : ℝ)) f univ x
   = (∫⁻ x, f x ∂(Measure.pi μ)) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  rw [rhsAux_univ']
  congr
  have : (1:ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have : (0:ℝ) < #ι - 1 := by linarith
  field_simp

lemma Measurable.rhsAux (p : ℝ) (hf : Measurable f) : Measurable (rhsAux μ p f s) := by
  refine ((hf.marginal μ).pow_const _).mul ?_
  exact Finset.measurable_prod _ fun i _ ↦ ((hf.marginal μ).pow_const _)

/-- The main inductive step -/
theorem marginal_singleton_rhsAux_le {p : ℝ} (hp1 : 0 ≤ p) (f : (∀ i, π i) → ℝ≥0∞)
    (hf : Measurable f) (s : Finset ι) (hp2 : (sᶜ.card - 1 : ℝ) * p ≤ 1) (i : ι) (hi : i ∉ s) :
    ∫⋯∫_sᶜ, rhsAux μ p f s ∂μ ≤ ∫⋯∫_(insert i s)ᶜ, rhsAux μ p f (insert i s) ∂μ := by
  have hi' : i ∉ (insert i s)ᶜ := not_mem_compl.mpr <| mem_insert_self i s
  calc ∫⋯∫_sᶜ, rhsAux μ p f s ∂μ
      = ∫⋯∫_insert i (insert i s)ᶜ, rhsAux μ p f s ∂μ := by simp_rw [← insert_compl_insert hi]
    _ = ∫⋯∫_(insert i s)ᶜ, (fun x ↦ ∫⁻ xᵢ, rhsAux μ p f s (Function.update x i xᵢ) ∂μ i) ∂μ :=
        marginal_insert' _ (hf.rhsAux μ p) hi'
    _ ≤ ∫⋯∫_(insert i s)ᶜ, rhsAux μ p f (insert i s) ∂μ := marginal_mono (fun x ↦ ?_)
  -- it suffices to compare the `i`-integral of `rhsAux s` with `rhsAux (insert i s)`
  have hf' : ∀ {s' : Finset ι}, Measurable fun t ↦ (∫⋯∫_s', f ∂μ) (update x i t) :=
    fun {_} ↦ hf.marginal μ |>.comp <| measurable_update _
  have hk₀ : sᶜ.card = (insert i s)ᶜ.card + 1
  · have H₁ : ((insert i s).card) = s.card + 1 := Finset.card_insert_of_not_mem hi
    have H₂ : ((insert i s).card) + (insert i s)ᶜ.card = #ι := (insert i s).card_add_card_compl
    have H₃ : (s.card) + sᶜ.card = #ι := s.card_add_card_compl
    zify at H₁ H₂ H₃ ⊢
    linear_combination H₁ - H₂ + H₃
  let k : ℝ := (insert i s)ᶜ.card
  have hk : sᶜ.card = k + 1 := by exact_mod_cast hk₀
  have hk' : 0 ≤ 1 - k * p
  · rw [hk] at hp2
    linarith only [hp2]
  let X := update x i
  let F : Finset ι → (∀ j, π j) → ℝ≥0∞ := fun s' ↦ ∫⋯∫_s', f ∂μ
  calc ∫⁻ t, F s (X t) ^ (1 - (sᶜ.card - 1 : ℝ) * p)
          * ∏ i in sᶜ, F (insert i s) (X t) ^ p ∂ (μ i)
      = ∫⁻ t, F (insert i s) (X t) ^ p * (F s (X t) ^ (1 - k * p)
          * ∏ j in (insert i s)ᶜ, (F (insert j s) (X t) ^ p)) ∂(μ i) := by
              -- rewrite integrand so that `(∫⋯∫_insert i s, f ∂μ) ^ p` comes first
              clear_value F X
              rw [hk]
              congr! 2 with t
              simp_rw [← insert_compl_insert hi, prod_insert hi']
              ring_nf
    _ = F (insert i s) x ^ p *
          ∫⁻ t, F s (X t) ^ (1 - k * p) * ∏ j in (insert i s)ᶜ, (F (insert j s) (X t)) ^ p ∂(μ i) := by
              -- pull out this constant factor
              simp_rw [marginal_update_of_mem μ (s.mem_insert_self i)]
              rw [lintegral_const_mul]
              exact (hf'.pow_const _).mul <| Finset.measurable_prod _ fun _ _ ↦ hf'.pow_const _
    _ ≤ F (insert i s) x ^ p *
          ((∫⁻ t, F s (X t) ∂μ i) ^ (1 - k * p) *
            ∏ j in (insert i s)ᶜ, (∫⁻ t, F (insert j s) (X t) ∂(μ i)) ^ p) := by
              -- apply Hölder's inequality
              gcongr
              apply ENNReal.lintegral_mul_prod_norm_pow_le
              · exact hf'.aemeasurable
              · intros
                exact hf'.aemeasurable
              · simp only [sum_const, nsmul_eq_mul]
                ring
              · exact hk'
              · exact fun _ _ ↦ hp1
    _ = F (insert i s) x ^ p *
          (F (insert i s) x ^ (1 - k * p) *
            ∏ j in (insert i s)ᶜ, F (insert i (insert j s)) x ^ p) := by
              -- absorb the newly-created integrals into `∫⋯∫`
              dsimp only
              rw [marginal_insert _ hf hi]
              congr! 2; refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ insert j s
              · simp only [Finset.mem_insert, Finset.mem_compl] at hj ⊢
                tauto
              rw [marginal_insert _ hf hi']
    _ = F (insert i s) x ^ (p + (1 - k * p)) *
            ∏ j in (insert i s)ᶜ, F (insert i (insert j s)) x ^ p := by
              -- combine two `(∫⋯∫_insert i s, f ∂μ) x` terms
              rw [ENNReal.rpow_add_of_nonneg]
              · ring
              · exact hp1
              · exact hk'
    _ = F (insert i s) x ^ (1 - ((insert i s)ᶜ.card - 1 : ℝ) * p)
          * ∏ j in (insert i s)ᶜ, F (insert j (insert i s)) x ^ p := by
              -- identify the result with the RHS integrand
              clear_value F
              simp_rw [Insert.comm]
              push_cast
              ring_nf

theorem marginal_rhsAux_monotone {p : ℝ} (hp1 : 0 ≤ p) (hp2 : (#ι - 1 : ℝ) * p ≤ 1)
    (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) :
    Monotone (fun s ↦ ∫⋯∫_sᶜ, rhsAux μ p f s ∂μ) := by
  rw [Finset.monotone_iff']
  intro s i hi
  refine marginal_singleton_rhsAux_le μ hp1 f hf s (le_trans ?_ hp2) i hi
  gcongr
  exact card_le_univ sᶜ

theorem lintegral_prod_lintegral_pow_le [Nontrivial ι] (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂Measure.pi μ ≤
      (∫⁻ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  cases isEmpty_or_nonempty (∀ i, π i)
  · simp_rw [lintegral_of_isEmpty]; refine' zero_le _
  inhabit ∀ i, π i
  have H : (∅ : Finset ι) ≤ Finset.univ := Finset.empty_subset _
  have : (1:ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have : (0:ℝ) < #ι - 1 := by linarith
  have hp1 : 0 ≤ ((1 : ℝ) / (#ι - 1 : ℝ)) := by positivity
  have hp2 : (#ι - 1 : ℝ) * ((1 : ℝ) / (#ι - 1 : ℝ)) ≤ 1 := by field_simp
  simpa [marginal_univ, rhsAux_empty, rhsAux_univ, -one_div] using
    marginal_rhsAux_monotone μ hp1 hp2 f hf H default
-- theorem integral_prod_integral_pow_le {f : (∀ i, π i) → ℝ} (hf : Measurable f)
--     (h2f : ∀ x, 0 ≤ f x) :
--     ∫ x,
--         ∏ i,
--           (∫ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1)) ∂Measure.pi μ ≤
--       (∫ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1)) :=
--   by sorry
section

-- move to MeasureTheory.Function.L1Space
theorem _root_.MeasureTheory.Integrable.nnnorm_toL1 {α : Type _} {β : Type _}
    {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β] (f : α → β)
    (hf : Integrable f μ) :
    (‖hf.toL1 f‖₊ : ℝ≥0∞) = ∫⁻ a, ‖f a‖₊ ∂μ := by
  simpa [Integrable.toL1, snorm, snorm'] using ENNReal.coe_toNNReal hf.2.ne

-- move to MeasureTheory.Integral.Bochner
theorem _root_.MeasureTheory.L1.nnnorm_Integral_le_one {α : Type _} {E : Type _}
    [NormedAddCommGroup E] {_ : MeasurableSpace α} {μ : Measure α} [NormedSpace ℝ E]
    [CompleteSpace E] : ‖L1.integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ (1 : ℝ) :=
  L1.norm_Integral_le_one

-- move to MeasureTheory.Integral.Bochner
theorem _root_.MeasureTheory.L1.nnnorm_integral_le {α : Type _} {E : Type _}
    [NormedAddCommGroup E] {_ : MeasurableSpace α} {μ : Measure α} [NormedSpace ℝ E]
    [CompleteSpace E] (f : α →₁[μ] E) : ‖L1.integral f‖₊ ≤ ‖f‖₊ :=
  L1.norm_integral_le f

end

-- move to MeasureTheory.Integral.Bochner
theorem nnnorm_integral_le_lintegral_nnnorm {α E : Type _} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : α → E) :
    ‖∫ x, f x ∂μ‖₊ ≤ ∫⁻ x, ‖f x‖₊ ∂ μ := by
  rw [integral_def, dif_pos ‹_›]
  split_ifs with hf
  · calc _ ≤ (‖(Integrable.toL1 f hf)‖₊ : ℝ≥0∞) := by norm_cast; apply L1.nnnorm_integral_le
      _ = _ := hf.nnnorm_toL1
  · simp

/-- The Gagliardo-Nirenberg-Sobolev inequality -/
theorem lintegral_pow_le [Nontrivial ι] [Fintype ι] (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) : ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) ≤
      (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  have : (1:ℝ) ≤ ↑#ι - 1
  · have hι : (2:ℝ) ≤ #ι := by exact_mod_cast Fintype.one_lt_card
    linarith
  calc ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ))
      = ∫⁻ x, ((‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        congr! 2 with x
        rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity), ← ENNReal.rpow_mul]
        field_simp
    _ = ∫⁻ x, ∏ _i : ι, (‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ)) := by
        congr! 2 with x
        simp_rw [prod_const, card_univ]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, ‖fderiv ℝ u (Function.update x i xᵢ)‖₊) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := ?_
    _ ≤ (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
        apply lintegral_prod_lintegral_pow_le
        borelize ((ι → ℝ) →L[ℝ] ℝ)
        have : Measurable (fun x ↦ fderiv ℝ u x) := (hu.continuous_fderiv (le_refl _)).measurable
        measurability
  gcongr with x i
  calc (‖u x‖₊ : ℝ≥0∞)
      = (‖∫ xᵢ : ℝ in Set.Iic (x i), deriv (u ∘ update x i) xᵢ‖₊ : ℝ≥0∞) := by
        have h3u : ContDiff ℝ 1 (u ∘ update x i) := hu.comp (contDiff_update 1 x i)
        have h4u : HasCompactSupport (u ∘ update x i)
        · apply h2u.comp_closedEmbedding
          -- `update x i` is a closed embedding -- make this a lemma
          have h5u : LeftInverse (fun v ↦ v i) (update x i) := fun t ↦ update_same i t x
          apply h5u.closedEmbedding
          · exact continuous_apply i
          · have : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prod_mk continuous_id
            exact (continuous_update i).comp this
        rw [h4u.integral_deriv_eq h3u (x i)]
        simp
    _ ≤ ∫⁻ xᵢ : ℝ in Set.Iic (x i), ‖deriv (u ∘ update x i) xᵢ‖₊ :=
        nnnorm_integral_le_lintegral_nnnorm _
    _ ≤ ∫⁻ (xᵢ : ℝ), ↑‖fderiv ℝ u (update x i xᵢ)‖₊ := ?_
  gcongr with y; swap; exact Measure.restrict_le_self
  calc ‖deriv (u ∘ update x i) y‖₊ = ‖fderiv ℝ u (update x i y) (deriv (update x i) y)‖₊ := by
        rw [fderiv.comp_deriv _ (hu.differentiable le_rfl).differentiableAt
          (hasDerivAt_update y).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ * ‖deriv (update x i) y‖₊ :=
        ContinuousLinearMap.le_op_nnnorm ..
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ := by simp [deriv_update, Pi.nnnorm_single]

-- /-- The Sobolev inequality for the Lebesgue l=integral(?) -/
-- theorem lintegral_pow_le :
--     ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) ≤
--       (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) :=
--   by sorry

end Sobolev
