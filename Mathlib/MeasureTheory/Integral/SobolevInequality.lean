/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ContDiff_aux
import Mathlib.Data.Finset.Interval
import Mathlib.MeasureTheory.Integral.Bochner_aux
import Mathlib.MeasureTheory.Integral.IntegralEqImproper_aux
import Mathlib.MeasureTheory.Integral.MeanInequalities_aux

/-!
# Gagliardo-Nirenberg-Sobolev inequality
-/


open scoped Classical BigOperators ENNReal NNReal
open Function Finset MeasureTheory
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}

section RPow

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

theorem NNReal.rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
  x ^ (y + z) = x ^ y * x ^ z := by
  by_cases h : y + z = 0
  · obtain rfl : y = 0 := by linarith
    obtain rfl : z = 0 := by linarith
    simp [h]
  · exact rpow_add' _ h

theorem ENNReal.rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

end RPow

section NormedAddCommGroup

variable [Fintype ι] {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)]

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

end NormedAddCommGroup


variable [Fintype ι] {π : ι → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
  [∀ i, SigmaFinite (μ i)] (u : (ι → ℝ) → ℝ) {f : (∀ i, π i) → ℝ≥0∞}


local prefix:max "#" => Fintype.card

/-! ## The grid-lines lemma -/

section GridLines

/-- The function that is central in the inductive proof of the Sobolev inequality.

An operation on a function `F (∀ i, π i) → ℝ≥0∞` which is implicitly assumed to vary only in the
variables whose indices are in `s`. -/
def T (p : ℝ) (F : (∀ i, π i) → ℝ≥0∞) (s : Finset ι) : (∀ i, π i) → ℝ≥0∞ :=
  ∫⋯∫_s, F ^ (1 - (s.card - 1 : ℝ) * p) * ∏ i in s, (∫⋯∫_{i}, F ∂μ) ^ p ∂μ

lemma T_univ (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    T μ p f univ x
    = ∫⁻ (x : ∀ i, π i), (f x ^ (1 - (#ι - 1 : ℝ) * p) * ∏ i : ι, (∫⁻ t : π i, f (update x i t) ∂(μ i)) ^ p) ∂(Measure.pi μ) := by
  simp [T, marginal_univ, marginal_singleton, card_univ]

lemma T_empty (p : ℝ) (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    T μ p f ∅ x = f x ^ (1 + p) := by
  simp [T, marginal_univ, Finset.card_univ]

set_option maxHeartbeats 500000 in
/-- The main inductive step -/
theorem marginal_singleton_T_le {p : ℝ} (hp1 : 0 ≤ p) (F : (∀ i, π i) → ℝ≥0∞) (hF : Measurable F)
    (u : Finset ι) (hp2 : (u.card : ℝ) * p ≤ 1) (i : ι) (hi : i ∉ u) :
    T μ p F (insert i u) ≤ T μ p (∫⋯∫_{i}, F ∂μ) u := by
  calc T μ p F (insert i u)
      = ∫⋯∫_insert i u, F ^ (1 - (u.card : ℝ) * p) * ∏ j in (insert i u), (∫⋯∫_{j}, F ∂μ) ^ p ∂μ := by
          simp_rw [T, card_insert_of_not_mem hi]
          congr!
          push_cast
          ring
    _ = ∫⋯∫_u, (fun x ↦ ∫⁻ (t : π i), (F (update x i t) ^ (1 - (u.card : ℝ) * p) * ∏ j in (insert i u), (∫⋯∫_{j}, F ∂μ) (update x i t) ^ p)  ∂ (μ i)) ∂μ := by
          rw [marginal_insert' _ _ hi]
          · congr! with x t
            simp only [Pi.mul_apply, Pi.pow_apply, prod_apply]
          · change Measurable (fun x ↦ _)
            simp only [Pi.mul_apply, Pi.pow_apply, prod_apply]
            exact (hF.pow_const _).mul <| Finset.measurable_prod _ fun _ _ ↦ hF.marginal μ |>.pow_const _
    _ ≤ T μ p (∫⋯∫_{i}, F ∂μ) u := marginal_mono (fun x ↦ ?_)
  simp only [Pi.mul_apply, Pi.pow_apply, prod_apply]
  have hF₁ : ∀ {j : ι}, Measurable fun t ↦ (∫⋯∫_{j}, F ∂μ) (update x i t) :=
    fun {_} ↦ hF.marginal μ |>.comp <| measurable_update _
  have hF₀ : Measurable fun t ↦ F (update x i t) := hF.comp <| measurable_update _
  let k : ℝ := u.card
  have hk' : 0 ≤ 1 - k * p := by linarith only [hp2]
  let X := update x i
  calc ∫⁻ t, F (X t) ^ (1 - k * p)
          * ∏ j in (insert i u), (∫⋯∫_{j}, F ∂μ) (X t) ^ p ∂ (μ i)
      = ∫⁻ t, (∫⋯∫_{i}, F ∂μ) (X t) ^ p * (F (X t) ^ (1 - k * p)
          * ∏ j in u, ((∫⋯∫_{j}, F ∂μ) (X t) ^ p)) ∂(μ i) := by
              -- rewrite integrand so that `(∫⋯∫_insert i s, f ∂μ) ^ p` comes first
              clear_value X
              congr! 2 with t
              simp_rw [prod_insert hi]
              ring_nf
    _ = (∫⋯∫_{i}, F ∂μ) x ^ p *
          ∫⁻ t, F (X t) ^ (1 - k * p) * ∏ j in u, ((∫⋯∫_{j}, F ∂μ) (X t)) ^ p ∂(μ i) := by
              -- pull out this constant factor
              have : ∀ t, (∫⋯∫_{i}, F ∂μ) (X t) = (∫⋯∫_{i}, F ∂μ) x
              · intro t
                rw [marginal_update_of_mem]
                exact Iff.mpr Finset.mem_singleton rfl
              simp_rw [this]
              rw [lintegral_const_mul]
              exact (hF₀.pow_const _).mul <| Finset.measurable_prod _ fun _ _ ↦ hF₁.pow_const _
    _ ≤ (∫⋯∫_{i}, F ∂μ) x ^ p *
          ((∫⁻ t, F (X t) ∂μ i) ^ (1 - k * p)
          * ∏ j in u, (∫⁻ t, (∫⋯∫_{j}, F ∂μ) (X t) ∂μ i) ^ p) := by
              -- apply Hölder's inequality
              gcongr
              apply ENNReal.lintegral_mul_prod_norm_pow_le
              · exact hF₀.aemeasurable
              · intros
                exact hF₁.aemeasurable
              · simp only [sum_const, nsmul_eq_mul]
                ring
              · exact hk'
              · exact fun _ _ ↦ hp1
    _ = (∫⋯∫_{i}, F ∂μ) x ^ p *
          ((∫⋯∫_{i}, F ∂μ) x ^ (1 - k * p) * ∏ j in u, (∫⋯∫_{i, j}, F ∂μ) x ^ p) := by
              -- absorb the newly-created integrals into `∫⋯∫`
              dsimp only
              congr! 2
              · rw [marginal_singleton]
              refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ ({j} : Finset ι)
              · simp only [Finset.mem_singleton, Finset.mem_insert, Finset.mem_compl] at hj ⊢
                exact fun h ↦ hi (h ▸ hj)
              rw [marginal_insert _ hF hi']
    _ = (∫⋯∫_{i}, F ∂μ) x ^ (p + (1 - k * p)) *  ∏ j in u, (∫⋯∫_{i, j}, F ∂μ) x ^ p := by
              -- combine two `(∫⋯∫_insert i s, f ∂μ) x` terms
              rw [ENNReal.rpow_add_of_nonneg]
              · ring
              · exact hp1
              · exact hk'
    _ ≤ (∫⋯∫_{i}, F ∂μ) x ^ (1 - (u.card - 1 : ℝ) * p) *
          ∏ j in u, (∫⋯∫_{j}, (∫⋯∫_{i}, F ∂μ) ∂μ) x ^ p := by
              -- identify the result with the RHS integrand
              congr! 2 with j hj
              · push_cast
                ring_nf
              · congr! 1
                rw [← marginal_union μ F hF]
                · congr
                  rw [Finset.union_comm]
                  rfl
                · rw [Finset.disjoint_singleton]
                  simp only [Finset.mem_insert, Finset.mem_compl] at hj
                  exact fun h ↦ hi (h ▸ hj)

theorem marginal_T_monotone {p : ℝ} (hp1 : 0 ≤ p) (hp2 : (#ι - 1 : ℝ) * p ≤ 1)
    (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) :
    Monotone (fun s ↦ T μ p (∫⋯∫_s, f ∂μ) sᶜ) := by
  rw [Finset.monotone_iff']
  intro s i hi
  convert marginal_singleton_T_le μ hp1 (∫⋯∫_s, f ∂μ) (hf.marginal μ) (insert i s)ᶜ ?_ i ?_ using 2
  · rw [insert_compl_insert hi]
  · rw [← marginal_union μ f hf]
    · rfl
    rwa [Finset.disjoint_singleton_left]
  · refine le_trans ?_ hp2
    gcongr
    suffices ((insert i s)ᶜ.card : ℝ) + 1 ≤ #ι by linarith
    rw [← (insert i s).card_add_card_compl, add_comm]
    norm_cast
    gcongr
    exact Iff.mpr card_pos (Finset.insert_nonempty i s)
  · rw [not_mem_compl]
    exact mem_insert_self i s

/-- The "grid-lines lemma" (not a standard name). -/
theorem lintegral_prod_lintegral_pow_le_aux {p : ℝ} (hp1 : 0 ≤ p)
    (hp2 : (#ι - 1 : ℝ) * p ≤ 1) (f) (hf : Measurable f) :
    ∫⁻ x, f x ^ (1 - (#ι - 1 : ℝ) * p) * ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ p ∂Measure.pi μ ≤
      (∫⁻ x, f x ∂Measure.pi μ) ^ (1 + p) := by
  cases isEmpty_or_nonempty (∀ i, π i)
  · simp_rw [lintegral_of_isEmpty]; refine' zero_le _
  inhabit ∀ i, π i
  have H : (∅ : Finset ι) ≤ Finset.univ := Finset.empty_subset _
  simpa [marginal_univ, T_empty, T_univ] using marginal_T_monotone μ hp1 hp2 f hf H default

/-- The "grid-lines lemma" (not a standard name). -/
theorem lintegral_prod_lintegral_pow_le [Nontrivial ι] (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂Measure.pi μ ≤
      (∫⁻ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  have : (1:ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have : (0:ℝ) < #ι - 1 := by linarith
  have hp1 : 0 ≤ ((1 : ℝ) / (#ι - 1 : ℝ)) := by positivity
  have hp2 : (#ι - 1 : ℝ) * ((1 : ℝ) / (#ι - 1 : ℝ)) ≤ 1 := by field_simp
  convert lintegral_prod_lintegral_pow_le_aux μ hp1 hp2 f hf using 2 <;> field_simp

end GridLines

/-! ## The Gagliardo-Nirenberg-Sobolev inequality -/

section Sobolev

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

end Sobolev
