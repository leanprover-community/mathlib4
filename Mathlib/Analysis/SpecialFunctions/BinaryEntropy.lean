/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of Shannon q-ary entropy and binary entropy functions

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1 - p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

More generally, the q-ary entropy function is the Shannon entropy of the random variable
with possible outcomes `{1, ..., q}`, where outcome `1` has probability `1 - p`
and all other outcomes are equally likely.

`qaryEntropy (q : ℕ) (p : ℝ) := p * log (q - 1) - p * log p - (1 - p) * log (1 - p)`

This file assumes that entropy is measured in Nats, hence the use of natural logarithms.
Most lemmas are also valid using a logarithm in a different base.

## Tags

entropy, Shannon, binary, nit, nepit
-/

namespace Real

/-- Shannon q-ary Entropy function (measured in Nats, i.e., using natural logs).

It's the Shannon entropy of a random variable with possible outcomes {1, ..., q}
where outcome `1` has probability `1 - p` and all other outcomes are equally likely.

Usual domain of definition is p ∈ [0,1], i.e., input is a probability.

This is a generalization of the binary entropy function `binEntropy`. -/
noncomputable def qaryEntropy (q : ℕ) (p : ℝ) : ℝ :=
  p * log (q - 1) - p * log p - (1 - p) * log (1 - p)

/-- The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1-p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`. -/
noncomputable def binEntropy := qaryEntropy 2

lemma binEntropy_eq : binEntropy = (fun p => -p * log p - (1 - p) * log (1 - p)) := by
  have : (2 : ℝ) - 1 = 1 := by norm_num
  ext
  simp [binEntropy, qaryEntropy, this]

lemma binEntropy_apply (p : ℝ) : binEntropy p = -p * log p - (1 - p) * log (1 - p) := by
  rw [binEntropy_eq]

@[simp] lemma qaryEntropy_zero {q : ℕ} : qaryEntropy q 0 = 0 := by
  simp only [qaryEntropy, zero_mul, log_zero, mul_zero, sub_self, sub_zero, log_one]

@[simp] lemma binEntropy_one : binEntropy 1 = 0 := by
  simp only [binEntropy_apply, log_one, mul_zero, sub_self, log_zero]

@[simp] lemma qaryEntropy_one {q : ℕ} : qaryEntropy q 1 = log (q - 1) := by
  unfold qaryEntropy
  simp only [log_one, mul_zero, sub_self, log_zero, one_mul, sub_zero]

@[simp] lemma binEntropy_two_inv : binEntropy 2⁻¹ = log 2 := by
  simp only [binEntropy_apply, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, log_inv]
  field_simp

/-- `binEntropy` is symmetric about 1/2. -/
@[simp] lemma binEntropy_one_sub (p : ℝ) :
    binEntropy (1 - p) = binEntropy p := by
  simp only [binEntropy_apply, neg_sub, sub_sub_cancel, neg_mul]
  ring

/-- `binEntropy` is symmetric about 1/2. -/
lemma binEntropy_two_inv_add (p : ℝ) :
    binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p) := by
  simp only [binEntropy_apply, neg_sub, sub_sub_cancel, neg_mul]
  ring_nf

lemma binEntropy_pos {p : ℝ} (pgt0 : 0 < p) (plt1 : p < 1) : 0 < binEntropy p := by
  simp only [binEntropy_apply]
  have pos_sum_pos_pos (a b : ℝ) (ha : 0 ≤ a) (hb : b < 0) : 0 < a - b := by linarith
  refine pos_sum_pos_pos (-p * log p) ((1 - p) * log (1 - p)) ?_ ?_
  · rw [show -p * log p = p * (-log p) by ring]
    exact (Real.mul_pos (by linarith) (by linarith [log_neg pgt0 plt1])).le
  · exact mul_neg_of_pos_of_neg (by linarith) (log_neg (by linarith) (by linarith))

lemma qaryEntropy_pos {q : ℕ} {p : ℝ} (pgt0 : 0 < p) (plt1 : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  have p_q_log_nonneg : 0 ≤ p * ((q : ℝ) - 1).log := by
    rw [mul_nonneg_iff_of_pos_left pgt0, show q - (1 : ℝ) = (q - 1 : ℤ) by norm_cast]
    exact Real.log_intCast_nonneg _
  have rest_is_pos : 0 < -(p * p.log) - (1 - p) * (1 - p).log := by
    simp only [← neg_mul, ← binEntropy_apply]
    exact binEntropy_pos pgt0 plt1
  linarith

/-- Outside usual range of `binEntropy`, it is negative. This is due to `log p = log |p|` -/
lemma binEntropy_neg_of_neg {p : ℝ} (hp : p < 0) : binEntropy p < 0 := by
  simp only [binEntropy_apply]
  suffices -p * log p < (1-p) * log (1-p) by linarith
  by_cases hp' : p < -1
  · have : log p < log (1 - p) := by
      rw [← log_neg_eq_log]
      exact log_lt_log (Left.neg_pos_iff.mpr hp) (by linarith)
    nlinarith [log_pos_of_lt_neg_one hp']
  · have : -p * log p ≤ 0 := by
      wlog h : -1 < p
      · simp only [show p = -1 by linarith, log_neg_eq_log, log_one, le_refl, mul_zero]
      · nlinarith [log_neg_of_lt_zero hp h]
    nlinarith [(log_pos (by linarith) : 0 < log (1 - p))]

/-- Outside usual range of `binEntropy`, it is negative. This is due to `log p = log |p|` -/
lemma binEntropy_neg_of_gt_one {p : ℝ} (hp : 1 < p) : binEntropy p < 0 := by
  let x := p - 2⁻¹
  rw [show p = 2⁻¹ + x by ring, binEntropy_two_inv_add]
  have : 2⁻¹ - x < 0 := by ring_nf; linarith
  exact binEntropy_neg_of_neg this

lemma binEntropy_eq_zero {p : ℝ} : binEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor <;> intro h
  · contrapose! h
    obtain hp₀ | hp₀ := h.1.lt_or_lt
    · exact (binEntropy_neg_of_neg hp₀).ne
    · obtain hp₁ | hp₁ := h.2.lt_or_lt.symm
      · exact (binEntropy_neg_of_gt_one hp₁).ne
      · exact (binEntropy_pos hp₀ hp₁).ne'
  · rw [binEntropy_apply]
    cases h <;> simp only [log_one, mul_zero, sub_self, log_zero, neg_zero, log_zero, mul_zero,
      sub_zero, log_one, sub_self, *]

/-- For probability `p < 0.5`, `binEntropy p < log 2`. -/
lemma binEntropy_lt_log2_of_lt_one_half {p : ℝ} (p_nonneg : 0 ≤ p) (p_lt : p < 1/2) :
    binEntropy p < log 2 := by
  -- Proof by concavity of log.
  rw [binEntropy_apply]
  rw [show -p * p.log = -(p * p.log) by ring]
  by_cases pz : p = 0
  · simp only [log_zero, mul_zero, neg_zero, sub_zero, log_one, sub_self, pz,
      show 0 < log 2 by positivity]
  · have invppos : 0 < 1/p := by positivity
    have : 0 < 1 - p := by linarith -- used implicitly by tactics.
    have sub1pinvpos : 0 < 1 / (1 - p) := by positivity
    have logConcave := (strictConcaveOn_log_Ioi.right (x := 1/p) (y := 1/(1-p)))
      (a := p) (b := 1-p) invppos sub1pinvpos (by norm_num; linarith) (by positivity)
      (by linarith) (by norm_num)
    have : p • (1 / p) + (1 - p) • (1 / (1 - p)) = 2 := by field_simp; norm_num
    rw [this] at logConcave
    have := calc -(p * log p) - (1 - p) * log (1 - p)
      _ = p * (-log p) + (1 - p) * (-log (1 - p)) := by ring
      _ = p * log (1/p) + (1 - p) * log (1 / (1 - p)) := by rw [← log_inv]; norm_num
    rw [this]
    exact logConcave

lemma binEntropy_lt_log2_of_gt_half {p : ℝ} (h : 1/2 < p) (h2 : p ≤ 1) :
    binEntropy p < log 2 := by
  rw [← binEntropy_one_sub]
  exact binEntropy_lt_log2_of_lt_one_half (by linarith) (by linarith)

lemma binEntropy_eq_log2_iff_eq_half {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binEntropy p = log 2 ↔ p = 1/2 := by
  constructor <;> intro h
  · by_cases h' : p < 1/2
    · linarith [binEntropy_lt_log2_of_lt_one_half pge0 h']
    · by_cases pgthalf : 1/2 < p
      · linarith [binEntropy_lt_log2_of_gt_half pgthalf ple1]
      · linarith
  · simp only [one_div, binEntropy_two_inv, h]

lemma binEntropy_le_log2 {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binEntropy p ≤ log 2 := by
  by_cases hh: p = 1/2
  · simp only [one_div, binEntropy_two_inv, le_refl, hh]
  · by_cases gg: binEntropy p = log 2
    · simp only [le_refl, gg]
    · by_cases hhh: p < 1/2
      · linarith [binEntropy_lt_log2_of_lt_one_half pge0 hhh]
      · have : 1/2 < p := by
          refine Ne.lt_of_le ?_ ?_
          · intro
            simp_all only [not_lt, not_true_eq_false]
          · simp_all only [one_div, not_lt]
        exact (binEntropy_lt_log2_of_gt_half this ple1).le

/-- The q-ary entropy function is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma qaryEntropy_continuous {q : ℕ} : Continuous (qaryEntropy q) := by
  refine Continuous.add ?_ (Continuous.neg ?_)
  · exact Continuous.sub (by fun_prop) continuous_mul_log
  · exact Continuous.comp continuous_mul_log (continuous_sub_left 1)

/-- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma binEntropy_continuous : Continuous binEntropy := qaryEntropy_continuous

/-! ### Derivatives of binary entropy function -/

lemma differentiableAt_binEntropy {p : ℝ} (xne0 : p ≠ 0) (gne1 : p ≠ 1) :
    DifferentiableAt ℝ binEntropy p := by
  simp only [binEntropy_eq]
  refine DifferentiableAt.sub (DifferentiableAt.mul (by fun_prop) ?_)
      (DifferentiableAt.mul (by fun_prop)
      (DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr gne1.symm)))
  exact DifferentiableAt.log differentiableAt_id' xne0

lemma differentiableAt_binEntropy_iff_ne_zero_one (p : ℝ) :
    DifferentiableAt ℝ binEntropy p ↔ p ≠ 0 ∧ p ≠ 1 := by
  refine ⟨?_, fun ne0Ne1 ↦ differentiableAt_binEntropy ne0Ne1.1 ne0Ne1.2⟩
  intro is_diff
  rw [binEntropy_eq] at is_diff
  by_cases is_x0 : p ≠ 0
  · constructor
    · assumption
    · intro xis1
      rw [xis1] at is_diff
      have as1 : DifferentiableAt ℝ (fun y ↦ -y * log y) 1 :=
        (hasDerivAt_negMulLog zero_ne_one.symm).differentiableAt
      have notTrue : DifferentiableAt ℝ (fun p ↦ -(1 - p) * log (1 - p)) 1 := by
        convert as1.add_iff_right.mp is_diff using 2
        ring
      have : ¬ DifferentiableAt ℝ (fun p ↦ -(1 - p) * log (1 - p)) 1 := by
        have h₁ : negMulLog = (fun p ↦ -(1 - p) * log (1 - p)) ∘ (fun x => 1 - x) := by
          ext; simp [negMulLog]
        have h₂ : DifferentiableAt ℝ negMulLog 0 := by
          rw [h₁]
          refine DifferentiableAt.comp _ ?_ (by fun_prop)
          simpa only [neg_sub, differentiableAt_id', differentiableAt_const, DifferentiableAt.sub,
            sub_zero] using notTrue
        rw [differentiableAt_negMulLog_iff] at h₂
        exact fun _ ↦ h₂ rfl
      contradiction
  · have : p = 0 := by simp_all only [neg_mul, false_implies, ne_eq, Decidable.not_not]
    rw [this] at is_diff
    have : DifferentiableAt ℝ (fun p ↦ -(1 - p) * log (1 - p)) 0 := by
      have := differentiableAt_negMulLog_iff.mpr (show (1 : ℝ) - 0 ≠ 0 by norm_num)
      exact DifferentiableAt.comp (0 : ℝ) this (by fun_prop)
    have : DifferentiableAt ℝ (fun p ↦ -p * log p) 0 := by
      apply this.add_iff_left.mp
      convert is_diff using 2
      ring
    have := differentiableAt_neg_iff.mpr this
    simp only [neg_mul, neg_neg, differentiableAt_id'] at this
    have := not_DifferentiableAt_log_mul_zero
    contradiction

private lemma deriv_log_one_sub {p : ℝ} : deriv (fun p' ↦ log (1 - p')) p = -(1 - p)⁻¹ := by
  by_cases xis1 : p = 1
  · have deriv_log_one_sub_at_1 : deriv (fun p ↦ log (1 - p)) 1 = 0 := by
      have : ¬ DifferentiableAt ℝ (fun p ↦ log (1 - p)) 1 := by
        by_contra h_contra
        have h₁ : ¬ DifferentiableAt ℝ log 0 := by simp [Real.differentiableAt_log_iff]
        have h₂ : DifferentiableAt ℝ log 0 := by
          rw [show Real.log = (fun p ↦ log (1 - p)) ∘ (fun x => 1 - x) by ext; simp]
          refine DifferentiableAt.comp _ ?_ (by fun_prop)
          simp only [sub_zero, h_contra]
        contradiction
      exact deriv_zero_of_not_differentiableAt this
    simp only [xis1, sub_self, inv_zero, neg_zero, deriv_log_one_sub_at_1]
  · rw [deriv.log]
    rw [deriv_const_sub 1, deriv_id'']
    field_simp
    fun_prop
    exact sub_ne_zero_of_ne fun a ↦ xis1 a.symm

/-- Binary entropy has derivative `log (1 - p) - log p`.
It's not differentiable at `0` or `1` but the junk values of `deriv` and `log` coincide there. -/
lemma deriv_binEntropy' {p : ℝ} :
    deriv (fun p' ↦ -p' * p'.log - (1 - p') * (1 - p').log) p = log (1 - p) - log p := by
  by_cases is_x_where_nondiff : p ≠ 0 ∧ p ≠ 1
  · obtain ⟨h, hh⟩ := is_x_where_nondiff
    have : DifferentiableAt ℝ (fun p' ↦ log (1 - p')) p :=
      DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr hh.symm)
    rw [deriv_sub ?_ (by fun_prop)]
    · simp only [← neg_mul_eq_neg_mul]
      rw [deriv.neg , deriv_mul_log h]
      simp only [mul_sub_right_distrib, one_mul]
      rw [deriv_sub this (by fun_prop), deriv_log_one_sub]
      rw [deriv_mul (by fun_prop) this, deriv_id'',
          deriv.log (by fun_prop) (sub_ne_zero_of_ne (hh.symm)), deriv_const_sub 1, deriv_id'']
      field_simp [one_mul, sub_ne_zero.mpr hh.symm]
      ring
    · exact (hasDerivAt_negMulLog h).differentiableAt
  -- pathological case where `deriv = 0` since function is not differentiable there
  · have : p = 0 ∨ p = 1 := Decidable.or_iff_not_and_not.mpr is_x_where_nondiff
    rw [← binEntropy_eq, deriv_zero_of_not_differentiableAt]
    · cases this with  -- surely this can be shortened?
        | inl xis0 => simp only [xis0, sub_zero, log_one, log_zero, sub_self]
        | inr xis1 => simp only [xis1, sub_zero, log_one, log_zero, sub_self]
    · intro h
      have := (differentiableAt_binEntropy_iff_ne_zero_one p).mp h
      simp_all only [ne_eq, not_true_eq_false, zero_ne_one, not_false_eq_true, and_true]

lemma deriv_qaryEntropy {q : ℕ} {p : ℝ} (h: p ≠ 0) (hh : p ≠ 1) :
    deriv (qaryEntropy q) p = log (q - 1) + log (1 - p) - log p := by
  unfold qaryEntropy
  have differentiable_const_minus {q : ℝ} (p : ℝ) :
    DifferentiableAt ℝ (fun p => q - p) p := by fun_prop
  have {a b c : ℝ} : a - b - c = a + (-b - c) := by ring
  simp_rw [this]
  rw [deriv_add]
  · rw [show log (q - 1) + (1 - p).log - p.log = log (q - 1) + ((1 - p).log - p.log) by
      exact add_sub_assoc (log (q - 1)) (1 - p).log p.log]
    congr! 1
    simp only [differentiableAt_id', differentiableAt_const, deriv_mul, deriv_id'', one_mul,
      deriv_const', mul_zero, add_zero]
    convert deriv_binEntropy' using 2
    simp only [neg_mul]
  · simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.mul]
  · apply DifferentiableAt.sub
    · exact DifferentiableAt.neg
        ((DifferentiableAt.mul differentiableAt_id') (DifferentiableAt.log differentiableAt_id' h))
    · exact DifferentiableAt.mul (differentiable_const_minus p)
        (DifferentiableAt.log (differentiable_const_minus p) (sub_ne_zero_of_ne hh.symm))

/-- Binary entropy has derivative `log (1 - p) - log p`.
It's not differentiable at `0` or `1` but the junk values of `deriv` and `log` coincide there. -/
lemma deriv_binEntropy {p : ℝ} :
    deriv binEntropy p = log (1 - p) - log p := by
  simp only [binEntropy_eq]
  exact deriv_binEntropy'

/-- Binary entropy has derivative `log (1 - p) - log p`. -/
lemma hasDerivAt_binEntropy {p : ℝ} (xne0: p ≠ 0) (xne1 : p ≠ 1) :
    HasDerivAt binEntropy (log (1 - p) - log p) p := by
  convert hasDerivAt_deriv_iff.mpr (differentiableAt_binEntropy xne0 xne1) using 1
  exact deriv_binEntropy.symm

lemma hasDerivAt_qaryEntropy {q : ℕ} {p : ℝ} (xne0: p ≠ 0) (gne1 : p ≠ 1) :
    HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - p) - log p) p := by
  have diffAt :
      DifferentiableAt ℝ (fun p => p * log (q - 1) - p * log p - (1 - p) * log (1 - p)) p := by
    have : (fun p => p * log (q - 1) - p * log p - (1 - p) * log (1 - p)) =
      (fun p => p * log (q - 1) + (-p * log p - (1 - p) * log (1 - p))) := by ext; ring
    rw [this]
    apply DifferentiableAt.add (by fun_prop)
    convert differentiableAt_binEntropy xne0 gne1 using 1
    exact binEntropy_eq.symm
  convert hasDerivAt_deriv_iff.mpr diffAt using 1
  exact (deriv_qaryEntropy xne0 gne1).symm

open Filter Topology Set

private lemma tendsto_log_one_sub_sub_log_nhdsWithin_atAtop :
    Tendsto (fun (p:ℝ) ↦ (1 - p).log - p.log) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1/2) : ℝ)
  · have h₁ : (0 : ℝ) < 1 / 2 := by norm_num
    filter_upwards [Ioc_mem_nhdsWithin_Ioi' h₁] with p hx
    gcongr
    linarith [hx.2]
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsWithin_zero_right

private lemma tendsto_log_one_sub_sub_log_nhdsWithin_one_atBot :
    Tendsto (fun (p:ℝ) ↦ (1 - p).log - p.log) (𝓝[<] 1) atBot := by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsWithin_zero_right
    apply Tendsto.comp (f:=(fun p ↦ 1 - p)) (g:=Real.log) this
    have contF : Continuous (fun (p:ℝ) ↦ 1 - p) := continuous_sub_left 1
    have : MapsTo (fun (p:ℝ) ↦ 1 - p)  (Iio 1) (Ioi 0) := by
      intro p hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert ContinuousWithinAt.tendsto_nhdsWithin (x:=(1:ℝ)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : ℝ) - (2 : ℝ)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsWithin_Iio' h₁] with p hx
    gcongr
    exact hx.1

lemma not_continuousAt_deriv_qaryEntropy_one {q : ℕ} :
    ¬ContinuousAt (deriv (qaryEntropy q)) 1 := by
  have tendstoBot : Tendsto (fun p ↦ log (q - 1) + log (1 - p) - log p) (𝓝[<] 1) atBot := by
    have : (fun (p:ℝ) ↦ log (q - 1) + (1 - p).log - p.log)
      = (fun p ↦ log (q - 1) + ((1 - p).log - p.log)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsWithin_one_atBot
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoBot) nhdsWithin_le_nhds
  simp only [disjoint_nhds_atBot_iff, not_isBot, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsWithin_Iio' (show 1 - 2⁻¹ < (1:ℝ) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  simp_all only [mem_Ioo, ne_eq]
  · linarith [show (1 : ℝ) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α:=ℝ)]

lemma not_continuousAt_deriv_qaryEntropy_zero {q : ℕ} :
    ¬ContinuousAt (deriv (qaryEntropy q)) 0 := by
  have tendstoTop : Tendsto (fun p ↦ log (q - 1) + log (1 - p) - log p) (𝓝[>] 0) atTop := by
    have : (fun (p:ℝ) ↦ log (q - 1) + (1 - p).log - p.log)
        = (fun p ↦ log (q - 1) + ((1 - p).log - p.log)) := by ext; ring
    rw [this]
    exact tendsto_atTop_add_const_left _ _ tendsto_log_one_sub_sub_log_nhdsWithin_atAtop
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoTop) nhdsWithin_le_nhds
  simp only [disjoint_nhds_atTop_iff, not_isTop, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (show (0:ℝ) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  simp_all only [zero_add, mem_Ioo, ne_eq]
  · linarith
  · simp_all only [zero_add, mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α:=ℝ)]

/-- Second derivative of q-ary entropy. -/
lemma deriv2_qaryEntropy {q : ℕ} {p : ℝ} :
    deriv^[2] (qaryEntropy q) p = -1 / (p * (1 - p)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : p ≠ 0 ∧ p ≠ 1  -- normal case
  · obtain ⟨xne0, xne1⟩ := is_x_where_nondiff
    suffices ∀ᶠ y in (𝓝 p),
        deriv (fun p ↦ (qaryEntropy q) p) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_sub ?_ (differentiableAt_log xne0)]
      · rw [deriv.log differentiableAt_id' xne0]
        simp only [deriv_id'', one_div]
        · have {q : ℝ} (p : ℝ) : DifferentiableAt ℝ (fun p => q - p) p := by fun_prop
          have d_oneminus (p : ℝ) : deriv (fun (y : ℝ) ↦ 1 - y) p = -1 := by
            rw [deriv_const_sub 1, deriv_id'']
          field_simp [sub_ne_zero_of_ne xne1.symm, this, d_oneminus]
          ring
      · apply DifferentiableAt.add
        simp only [ne_eq, differentiableAt_const]
        exact DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr xne1.symm)
    filter_upwards [eventually_ne_nhds xne0, eventually_ne_nhds xne1]
      with y xne0 h2 using deriv_qaryEntropy xne0 h2
  -- Pathological case where we use junk value (because function not differentiable)
  · have : p = 0 ∨ p = 1 := Decidable.or_iff_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    · simp_all only [ne_eq, not_and, Decidable.not_not]
      cases this <;> simp_all only [
        mul_zero, one_ne_zero, zero_ne_one, sub_zero, mul_one, div_zero, sub_self]
    · intro h
      have contAt := h.continuousAt
      cases this <;> simp_all [
        not_continuousAt_deriv_qaryEntropy_zero, not_continuousAt_deriv_qaryEntropy_one, contAt]

lemma deriv2_binEntropy {p : ℝ} : deriv^[2] binEntropy p = -1 / (p * (1 - p)) :=
  deriv2_qaryEntropy

/-! ### Strict Monotonicity of binary entropy -/

/-- Qary entropy is strictly increasing in the interval [0, 1 - q⁻¹]. -/
lemma qaryEntropy_strictMonoOn {q : ℕ} (qLe2: 2 ≤ q) :
    StrictMonoOn (qaryEntropy q) (Icc 0 (1 - 1/q)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1/(q:ℝ))) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have zero_le_qinv : 0 < (q : ℝ)⁻¹ := by positivity
    have : 0 < 1 - p  := by
      simp only [sub_pos, hp.2]
      have p_lt_1_minus_qinv : p < 1 - (q : ℝ)⁻¹ := by
        simp_all only [inv_pos, interior_Icc, mem_Ioo, one_div]
      linarith
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · field_simp
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr hp.1)
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left, show 0 < (q : ℝ) - 1 by linarith]
      · have qpos : 0 < (q : ℝ) := by positivity
        have : q * p < q - 1 := by
          convert (mul_lt_mul_left qpos).2 hp.2 using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : p < 1)).symm

/-- Qary entropy is strictly decreasing in the interval [1 - q⁻¹, 1]. -/
lemma qaryEntropy_strictAntiOn {q : ℕ} (qLe2: 2 ≤ q) :
    StrictAntiOn (qaryEntropy q) (Icc (1 - 1/q) 1) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 - 1/(q:ℝ)) 1) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have qinv_lt_1 : (q : ℝ)⁻¹ < 1 := inv_lt_one (by linarith)
    have zero_lt_1_sub_p : 0 < 1 - p := by simp_all only [sub_pos, hp.2, interior_Icc, mem_Ioo]
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · field_simp
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr (show 0 < (↑q - 1) * (1 - p) by nlinarith))
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left]
        linarith
      · have qpos : 0 < (q : ℝ) := by positivity
        ring_nf
        simp only [add_lt_iff_neg_right, neg_add_lt_iff_lt_add, add_zero, gt_iff_lt]
        have : (q:ℝ) - 1 < p * q := by
          have tmp := mul_lt_mul_of_pos_right hp.1 qpos
          simp at tmp
          have : (q : ℝ) ≠ 0 := (ne_of_lt qpos).symm
          have asdfasfd : (1 - (q : ℝ)⁻¹) * ↑q = q - 1 := by calc (1 - (q : ℝ)⁻¹) * ↑q
            _ = q - (q : ℝ)⁻¹ * (q : ℝ) := by ring
            _ = q - 1 := by simp_all only [ne_eq, isUnit_iff_ne_zero, Rat.cast_eq_zero,
              not_false_eq_true, IsUnit.inv_mul_cancel]
          rwa [asdfasfd] at tmp
        nlinarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp zero_lt_1_sub_p : p < 1)).symm

/-- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma binEntropy_strictMonoOn : StrictMonoOn binEntropy (Icc 0 2⁻¹) := by
  rw [show Icc (0:ℝ) 2⁻¹ = Icc 0 (1 - 1/2) by norm_num]
  exact qaryEntropy_strictMonoOn (by rfl)

/-- Binary entropy is strictly decreasing in interval [1/2, 1]. -/
lemma binEntropy_strictAntiOn : StrictAntiOn binEntropy (Icc 2⁻¹ 1) := by
  rw [show (Icc (2⁻¹ : ℝ) 1) = Icc (1/2) 1 by norm_num]
  convert qaryEntropy_strictAntiOn (by rfl) using 1
  norm_num

/-! ### Strict Concavity of binary and q-ary entropy functions -/

lemma strictConcaveOn_qaryEntropy {q : ℕ} : StrictConcaveOn ℝ (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro p hp
  rw [deriv2_qaryEntropy]
  · simp_all only [interior_Icc, mem_Ioo]
    apply div_neg_of_neg_of_pos
    norm_num [show 0 < log 2 by positivity]
    simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left, sub_pos, hp]

lemma strictConcave_binEntropy : StrictConcaveOn ℝ (Icc 0 1) binEntropy :=
  strictConcaveOn_qaryEntropy

end Real
