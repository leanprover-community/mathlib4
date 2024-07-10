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
`binaryEntropy p := - p * log p - (1 - p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

More generally, the q-ary entropy function is the Shannon entropy of the random variable
with possible outcomes `{1, ..., q}`, where outcome `1` has probability `(1 - p)`
and all other outcomes are equally likely.

`qaryEntropy (q : ℕ) (p : ℝ) := p * log (q - 1) - p * log p - (1 - p) * log (1 - p)`

This file assumes that entropy is measured in Nats, hence the use of natural logarithms.
Most lemmas are also valid using a logarithm in a different base.

## Tags

entropy, Shannon, binary
-/

open Real

/-- Shannon q-ary Entropy function (measured in Nats, i.e., using natural logs).

It's the Shannon entropy of a random variable with possible outcomes {1, ..., q}
where outcome `1` has probability `(1 - p)` and all other outcomes are equally likely.

Usual domain of definition is p ∈ [0,1], i.e., input is a probability.

This is a generalization of the binary entropy function `binaryEntropy`. -/
noncomputable def qaryEntropy (q : ℕ) (p : ℝ) : ℝ :=
  p * log (q - 1) - p * log p - (1 - p) * log (1 - p)

/-- The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binaryEntropy p := - p * log p - (1-p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`. -/
noncomputable def binaryEntropy := qaryEntropy 2

lemma binaryEntropy_eq : binaryEntropy = (fun p => -p * log p - (1 - p) * log (1 - p)) := by
  have : (2 : ℝ) - 1 = 1 := by norm_num
  ext
  simp [binaryEntropy, qaryEntropy, this]

lemma binaryEntropy_eq' {p : ℝ} : binaryEntropy p = -p * log p - (1 - p) * log (1 - p) := by
  rw [binaryEntropy_eq]

@[simp] lemma qaryEntropy_zero {q : ℕ} : qaryEntropy q 0 = 0 := by
  simp only [qaryEntropy, zero_mul, log_zero, mul_zero, sub_self, sub_zero, log_one]

@[simp] lemma binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp only [binaryEntropy_eq', log_one, mul_zero, sub_self, log_zero]

@[simp] lemma qaryEntropy_one {q : ℕ} : qaryEntropy q 1 = log (q - 1) := by
  unfold qaryEntropy
  simp only [log_one, mul_zero, sub_self, log_zero, one_mul, sub_zero]

@[simp] lemma binaryEntropy_onehalf : binaryEntropy 2⁻¹ = log 2 := by
  simp only [binaryEntropy_eq', show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, log_inv]
  field_simp

/-- `binaryEntropy` is symmetric about 1/2. -/
@[simp] lemma binaryEntropy_one_sub (p : ℝ) :
    binaryEntropy (1 - p) = binaryEntropy p := by
  simp only [binaryEntropy_eq', neg_sub, sub_sub_cancel, neg_mul]
  ring

/-- `binaryEntropy` is symmetric about 1/2. -/
lemma binaryEntropy_add_onehalf (p : ℝ) :
    binaryEntropy (2⁻¹ + p) = binaryEntropy (2⁻¹ - p) := by
  simp only [binaryEntropy_eq', neg_sub, sub_sub_cancel, neg_mul]
  ring_nf

lemma qaryEntropy_eq_log_mul_add_binaryEntropy {q : ℕ} {p : ℝ} :
    qaryEntropy q p = p * log (q - 1) + binaryEntropy p := by
  unfold binaryEntropy qaryEntropy
  simp only [show ((2:ℕ) - (1:ℝ)).log = 0 by norm_num]
  ring

lemma qaryEntropy_eq_log_mul_add_binaryEntropy' {q : ℕ} :
    qaryEntropy q = (fun p ↦ p * log (q - 1)) + binaryEntropy := by
  ext
  simp only [Pi.add_apply, qaryEntropy_eq_log_mul_add_binaryEntropy]

lemma binaryEntropy_pos {p : ℝ} (pgt0 : 0 < p) (ple1 : p < 1) : 0 < binaryEntropy p := by
  simp only [binaryEntropy_eq']
  have pos_sum_pos_pos (a b : ℝ) (ha : 0 ≤ a) (hb : b < 0) : 0 < a - b := by linarith
  refine pos_sum_pos_pos (-p * log p) ((1 - p) * log (1 - p)) ?_ ?_
  · rw [show -p * log p = p * (-log p) by ring]
    exact (Real.mul_pos (by linarith) (by linarith [log_neg pgt0 ple1])).le
  · exact mul_neg_of_pos_of_neg (by linarith) (log_neg (by linarith) (by linarith))

lemma qaryEntropy_pos {q : ℕ} {p : ℝ} (pgt0 : 0 < p) (ple1 : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  have p_q_log_nonneg : 0 ≤ p * ((q : ℝ) - 1).log := by
    rw [mul_nonneg_iff_of_pos_left pgt0, show q - (1 : ℝ) = (q - 1 : ℤ) by norm_cast]
    exact Real.log_intCast_nonneg _
  have rest_is_pos : 0 < -(p * p.log) - (1 - p) * (1 - p).log := by
    simp only [← neg_mul, ← binaryEntropy_eq']
    exact binaryEntropy_pos pgt0 ple1
  linarith

/- Outside usual range of `binaryEntropy`. This is due to `log x = log |x|` -/
lemma binaryEntropy_neg_of_neg {p : ℝ} (hp : p < 0) : binaryEntropy p < 0 := by
  simp only [binaryEntropy_eq']
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

/- Outside usual range of `binaryEntropy`. This is due to `log x = log |x|` -/
lemma binaryEntropy_neg_of_gt_one {p : ℝ} (hp : 1 < p) : binaryEntropy p < 0 := by
  let x := p - 2⁻¹
  rw [show p = 2⁻¹ + x by ring, binaryEntropy_add_onehalf]
  have : 2⁻¹ - x < 0 := by ring_nf; linarith
  exact binaryEntropy_neg_of_neg this

lemma binaryEntropy_zero_iff_zero_or_one {p : ℝ} : binaryEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor <;> intro h
  · by_cases plt0 : p < 0
    · linarith [binaryEntropy_neg_of_neg plt0]
    · by_cases pgt1 : p > 1
      · linarith [binaryEntropy_neg_of_gt_one pgt1]
      · by_cases pz : p = 0
        · left; assumption
        · by_cases pone : p = 1
          · right; assumption
          · have : 0 < binaryEntropy p := by
              apply binaryEntropy_pos (Ne.lt_of_le (fun a ↦ pz a.symm) (le_of_not_lt plt0))
              exact Ne.lt_of_le pone (le_of_not_lt pgt1)
            linarith
  · rw [binaryEntropy_eq']
    cases h <;> simp only [log_one, mul_zero, sub_self, log_zero, neg_zero, log_zero, mul_zero,
      sub_zero, log_one, sub_self, *]

/-- For probability `p < 0.5`, `binaryEntropy p < log 2`. -/
lemma binaryEntropy_lt_log2_of_lt_half {p : ℝ} (pge0 : 0 ≤ p) (plehalf : p < 1/2) :
    binaryEntropy p < log 2 := by
  -- Proof by concavity of log.
  rw [binaryEntropy_eq']
  rw [show -p * p.log = -(p * p.log) by ring]
  by_cases pz : p = 0
  · simp only [log_zero, mul_zero, neg_zero, sub_zero, log_one, sub_self, pz,
      show 0 < log 2 by positivity]
  · have invppos : 0 < 1/p := by positivity
    have : 0 < 1 - p := by linarith -- used implicitly by tactics.
    have sub1pinvpos : 0 < 1 / (1 - p) := by positivity
    have logConcave := (strictConcaveOn_log_Ioi.right
      (x := 1/p) (y := 1/(1-p))) (a := p) (b := 1-p)
      invppos sub1pinvpos (by norm_num; linarith) (by positivity)
      (by linarith) (by norm_num)
    have : p • (1 / p) + (1 - p) • (1 / (1 - p)) = 2 := by field_simp; norm_num
    rw [this] at logConcave
    have := calc -(p * log p) - (1 - p) * log (1 - p)
      _ = p * (-log p) + (1 - p) * (-log (1 - p)) := by ring
      _ = p * log (1/p) + (1 - p) * log (1 / (1 - p)) := by rw [← log_inv]; norm_num
    rw [this]
    exact logConcave

lemma binaryEntropy_lt_log2_of_gt_half {p : ℝ} (h : 1/2 < p) (h2 : p ≤ 1) :
    binaryEntropy p < log 2 := by
  rw [← binaryEntropy_one_sub]
  exact binaryEntropy_lt_log2_of_lt_half (by linarith) (by linarith)

lemma binaryEntropy_eq_log2_iff_eq_half {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binaryEntropy p = log 2 ↔ p = 1/2 := by
  constructor <;> intro h
  · by_cases h' : p < 1/2
    · linarith [binaryEntropy_lt_log2_of_lt_half pge0 h']
    · by_cases pgthalf : 1/2 < p
      · linarith [binaryEntropy_lt_log2_of_gt_half pgthalf ple1]
      · linarith
  · simp only [one_div, binaryEntropy_onehalf, h]

lemma binaryEntropy_le_log2 {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binaryEntropy p ≤ log 2 := by
  by_cases hh: p = 1/2
  · simp only [one_div, binaryEntropy_onehalf, le_refl, hh]
  · by_cases gg: binaryEntropy p = log 2
    · simp only [le_refl, gg]
    · by_cases hhh: p < 1/2
      · linarith [binaryEntropy_lt_log2_of_lt_half pge0 hhh]
      · have : 1/2 < p := by
          refine Ne.lt_of_le ?_ ?_
          · intro
            simp_all only [not_lt, not_true_eq_false]
          · simp_all only [one_div, not_lt]
        exact (binaryEntropy_lt_log2_of_gt_half this ple1).le

/-- The q-ary entropy function is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma qaryEntropy_continuous {q : ℕ} : Continuous (qaryEntropy q) := by
  refine Continuous.add ?_ (Continuous.neg ?_)
  · exact Continuous.sub (by fun_prop) continuous_mul_log
  · exact Continuous.comp continuous_mul_log (continuous_sub_left 1)

/-- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma binaryEntropy_continuous : Continuous binaryEntropy := qaryEntropy_continuous

/-! ### Derivatives of binary entropy function -/

section general

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : E → F}
variable {x : E}

lemma DifferentiableAt.iff_comp_mul_add
    {a b m : 𝕜} (hm : m ≠ 0) (f : 𝕜 → E) :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (m * x + b)) (m⁻¹ * (a - b)):= by
  constructor <;> intro h
  · apply DifferentiableAt.comp
    · have : (m * (m⁻¹ * (a - b)) + b) = a := by
        simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel_left,
          sub_add_cancel]
      rw [this]
      exact h
    · fun_prop
  · have : f = (fun x ↦ f (m * x + b)) ∘ (fun x => m⁻¹ * (x - b)) := by
      ext
      simp only [Function.comp_apply]
      field_simp
    rw [this]
    apply DifferentiableAt.comp _ ?_ (by fun_prop)
    exact h


end general

lemma differentiableAt_binaryEntropy {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    DifferentiableAt ℝ binaryEntropy x := by
  simp only [binaryEntropy_eq]
  refine DifferentiableAt.sub (DifferentiableAt.mul (by fun_prop) ?_)
      (DifferentiableAt.mul (by fun_prop)
      (DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr gne1.symm)))
  exact DifferentiableAt.log differentiableAt_id' xne0

lemma differentiableAt_binaryEntropy_iff_ne_zero_one (x : ℝ) :
    DifferentiableAt ℝ binaryEntropy x ↔ x ≠ 0 ∧ x ≠ 1 := by
  refine ⟨?_, fun ne0Ne1 ↦ differentiableAt_binaryEntropy ne0Ne1.1 ne0Ne1.2⟩
  intro is_diff
  rw [binaryEntropy_eq] at is_diff
  by_cases is_x0 : x ≠ 0
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
        intro h
        have : DifferentiableAt ℝ (fun (x : ℝ) ↦ (-1 * x + 1).negMulLog) ((-1)⁻¹ * (0 - 1)) := by
          convert h using 1
          · ext
            simp [negMulLog]
            ring_nf
          · ring
        have := (DifferentiableAt.iff_comp_mul_add
          (a:=(0:ℝ)) (b:=(1:ℝ)) (m:=(-1 : ℝ)) (show (-1 : ℝ) ≠ 0 by norm_num) negMulLog).mpr this
        unfold negMulLog at this
        have := differentiableAt_neg_iff.mpr this
        simp only [neg_mul, neg_neg, differentiableAt_id'] at this
        exact not_DifferentiableAt_log_mul_zero this
      contradiction
  · have : x = 0 := by simp_all only [neg_mul, false_implies, ne_eq, Decidable.not_not]
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

private lemma deriv_log_one_sub {x : ℝ} : deriv (fun p ↦ log (1 - p)) x = -(1-x)⁻¹ := by
  by_cases xis1 : x = 1
  · have deriv_log_one_sub_at_1 : deriv (fun p ↦ log (1 - p)) 1 = 0 := by
      have : ¬ DifferentiableAt ℝ (fun p ↦ log (1 - p)) 1 := by
        by_contra h_contra
        have h₁ : ¬ DifferentiableAt ℝ log 0 := by simp [Real.differentiableAt_log_iff]
        have h₂ : DifferentiableAt ℝ log 0 := by
          have : Real.log = (fun p ↦ log (1 - p)) ∘ (fun x => 1 - x) := by ext; simp
          rw [this]
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
lemma deriv_binaryEntropy' {x : ℝ} :
    deriv (fun p ↦ -p * p.log - (1 - p) * (1 - p).log) x = log (1 - x) - log x := by
  by_cases is_x_where_nondiff : x ≠ 0 ∧ x ≠ 1
  · obtain ⟨h, hh⟩ := is_x_where_nondiff
    have : DifferentiableAt ℝ (fun p ↦ log (1 - p)) x :=
      DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr hh.symm)
    rw [deriv_sub ?_ (by fun_prop)]
    simp only [← neg_mul_eq_neg_mul]
    rw [deriv.neg , deriv_mul_log h]
    simp only [mul_sub_right_distrib, one_mul]
    rw [deriv_sub this (by fun_prop), deriv_log_one_sub]
    · rw [deriv_mul (by fun_prop) this, deriv_id'']
      rw [deriv.log (by fun_prop) (sub_ne_zero_of_ne (hh.symm)), deriv_const_sub 1, deriv_id'']
      simp only [one_mul]
      field_simp [sub_ne_zero.mpr hh.symm]
      ring
    · exact (hasDerivAt_negMulLog h).differentiableAt
  -- pathological case where `deriv = 0` since function is not differentiable there
  · have : x = 0 ∨ x = 1 := Decidable.or_iff_not_and_not.mpr is_x_where_nondiff
    rw [← binaryEntropy_eq]
    rw [deriv_zero_of_not_differentiableAt]
    · cases this with  -- surely this can be shortened?
        | inl xis0 => simp only [xis0, sub_zero, log_one, log_zero, sub_self]
        | inr xis1 => simp only [xis1, sub_zero, log_one, log_zero, sub_self]
    · intro h
      have := (differentiableAt_binaryEntropy_iff_ne_zero_one x).mp h
      simp_all only [ne_eq, not_true_eq_false, zero_ne_one, not_false_eq_true, and_true]

lemma deriv_qaryEntropy {q : ℕ} {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) :
    deriv (qaryEntropy q) x = log (q - 1) + log (1 - x) - log x := by
  unfold qaryEntropy
  have differentiable_const_minus {q : ℝ} (p : ℝ) :
    DifferentiableAt ℝ (fun p => q - p) p := by fun_prop
  have {a b c : ℝ} : a - b - c = a + (-b - c) := by ring
  simp_rw [this]
  rw [deriv_add]
  · rw [show log (q - 1) + (1 - x).log - x.log = log (q - 1) + ((1 - x).log - x.log) by
      exact add_sub_assoc (log (q - 1)) (1 - x).log x.log]
    congr! 1
    simp only [differentiableAt_id', differentiableAt_const, deriv_mul, deriv_id'', one_mul,
      deriv_const', mul_zero, add_zero]
    convert deriv_binaryEntropy' using 2
    simp only [neg_mul]
  · simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.mul]
  · apply DifferentiableAt.sub
    · exact DifferentiableAt.neg
        ((DifferentiableAt.mul differentiableAt_id') (DifferentiableAt.log differentiableAt_id' h))
    · apply DifferentiableAt.mul (differentiable_const_minus x)
        (DifferentiableAt.log (differentiable_const_minus x) (sub_ne_zero_of_ne hh.symm))

/-- Binary entropy has derivative `log (1 - p) - log p`.
It's not differentiable at `0` or `1` but the junk values of `deriv` and `log` coincide there. -/
lemma deriv_binaryEntropy {x : ℝ} :
    deriv binaryEntropy x = log (1 - x) - log x := by
  simp only [binaryEntropy_eq]
  exact deriv_binaryEntropy'

/-- Binary entropy has derivative `log (1 - p) - log p`. -/
lemma hasDerivAt_binaryEntropy {x : ℝ} (xne0: x ≠ 0) (xne1 : x ≠ 1) :
    HasDerivAt binaryEntropy (log (1 - x) - log x) x := by
  convert hasDerivAt_deriv_iff.mpr (differentiableAt_binaryEntropy xne0 xne1) using 1
  exact deriv_binaryEntropy.symm

lemma hasDerivAt_qaryEntropy {q : ℕ} {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - x) - log x) x := by
  have diffAt :
      DifferentiableAt ℝ (fun p => p * log (q - 1) - p * log p - (1 - p) * log (1 - p)) x := by
    have : (fun p => p * log (q - 1) - p * log p - (1 - p) * log (1 - p)) =
      (fun p => p * log (q - 1) + (-p * log p - (1 - p) * log (1 - p))) := by ext; ring
    rw [this]
    apply DifferentiableAt.add (by fun_prop)
    convert differentiableAt_binaryEntropy xne0 gne1 using 1
    exact binaryEntropy_eq.symm
  convert hasDerivAt_deriv_iff.mpr diffAt using 1
  exact (deriv_qaryEntropy xne0 gne1).symm

open Filter Topology Set

private lemma tendsto_log_one_sub_sub_log_nhdsWithin_atAtop :
    Tendsto (fun (x:ℝ) ↦ (1 - x).log - x.log) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1/2) : ℝ)
  · have h₁ : (0 : ℝ) < 1 / 2 := by norm_num
    filter_upwards [Ioc_mem_nhdsWithin_Ioi' h₁] with x hx
    gcongr
    have : x ≤ 1/2 := hx.2
    linarith
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsWithin_zero_right

private lemma tendsto_log_one_sub_sub_log_nhdsWithin_one_atBot :
    Tendsto (fun (x:ℝ) ↦ (1 - x).log - x.log) (𝓝[<] 1) atBot := by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsWithin_zero_right
    apply Tendsto.comp (f:=(fun x ↦ 1 - x)) (g:=Real.log) this
    have contF : Continuous (fun (x:ℝ) ↦ 1 - x) := continuous_sub_left 1
    have : MapsTo (fun (x:ℝ) ↦ 1 - x)  (Iio 1) (Ioi 0) := by
      intro x hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert ContinuousWithinAt.tendsto_nhdsWithin (x:=(1:ℝ)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : ℝ) - (2 : ℝ)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsWithin_Iio' h₁] with x hx
    gcongr
    exact hx.1

lemma not_continuousAt_deriv_qaryEntropy_one {q : ℕ} :
    ¬ContinuousAt (deriv (qaryEntropy q)) 1 := by
  apply not_continuousAt_of_tendsto_nhdsWithin_Iio_atBot
  have tendstoBot : Tendsto (fun x ↦ log (q - 1) + log (1 - x) - log x) (𝓝[<] 1) atBot := by
    have : (fun (x:ℝ) ↦ log (q - 1) + (1 - x).log - x.log)
      = (fun x ↦ log (q - 1) + ((1 - x).log - x.log)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsWithin_one_atBot
  apply Filter.Tendsto.congr' _ tendstoBot
  filter_upwards [Ioo_mem_nhdsWithin_Iio' (show 1 - 2⁻¹ < (1:ℝ) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  simp_all only [mem_Ioo, ne_eq]
  · linarith [show (1 : ℝ) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α:=ℝ)]

lemma not_continuousAt_deriv_qaryEntropy_zero {q : ℕ} :
    ¬ContinuousAt (deriv (qaryEntropy q)) 0 := by
  apply not_continuousAt_of_tendsto_nhdsWithin_Ioi_atTop
  have asdf : Tendsto (fun x ↦ log (q - 1) + log (1 - x) - log x) (𝓝[>] 0) atTop := by
    have : (fun (x:ℝ) ↦ log (q - 1) + (1 - x).log - x.log)
      = (fun x ↦ log (q - 1) + ((1 - x).log - x.log)) := by
      ext
      ring
    rw [this]
    apply tendsto_atTop_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsWithin_atAtop
  apply Filter.Tendsto.congr' _ asdf
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (show (0:ℝ) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  simp_all only [zero_add, mem_Ioo, ne_eq]
  · linarith
  · simp_all only [zero_add, mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α:=ℝ)]

/-- Second derivative of q-ary entropy. -/
lemma deriv2_qaryEntropy {q : ℕ} {x : ℝ} :
    deriv^[2] (qaryEntropy q) x = -1 / (x * (1 - x)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : x ≠ 0 ∧ x ≠ 1  -- normal case
  · obtain ⟨xne0, xne1⟩ := is_x_where_nondiff
    suffices ∀ᶠ y in (𝓝 x),
        deriv (fun x ↦ (qaryEntropy q) x) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_sub ?_ (differentiableAt_log xne0)]
      · rw [deriv.log differentiableAt_id' xne0]
        simp only [deriv_id'', one_div]
        · have {q : ℝ} (p : ℝ) : DifferentiableAt ℝ (fun p => q - p) p := by fun_prop
          have d_oneminus (x : ℝ) : deriv (fun (y : ℝ) ↦ 1 - y) x = -1 := by
            rw [deriv_const_sub 1, deriv_id'']
          field_simp [sub_ne_zero_of_ne xne1.symm, this, d_oneminus]
          ring
      · apply DifferentiableAt.add
        simp only [ne_eq, differentiableAt_const]
        exact DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr xne1.symm)
    filter_upwards [eventually_ne_nhds xne0, eventually_ne_nhds xne1]
      with y xne0 h2 using deriv_qaryEntropy xne0 h2
  -- Pathological case where we use junk value (because function not differentiable)
  · have : x = 0 ∨ x = 1 := Decidable.or_iff_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    · simp_all only [ne_eq, not_and, Decidable.not_not]
      cases this <;> simp_all only [
        mul_zero, one_ne_zero, zero_ne_one, sub_zero, mul_one, div_zero, sub_self]
    · intro h
      have contAt := h.continuousAt
      cases this <;> simp_all [
        not_continuousAt_deriv_qaryEntropy_zero, not_continuousAt_deriv_qaryEntropy_one, contAt]

lemma deriv2_binaryEntropy {x : ℝ} : deriv^[2] binaryEntropy x = -1 / (x * (1-x)) :=
  deriv2_qaryEntropy

/-! ### Strict Monotonicity of binary entropy -/

/-- Qary entropy is strictly increasing in interval [0, 1 - q⁻¹]. -/
lemma qaryEntropy_strictMono {q : ℕ} (qLe2: 2 ≤ q) :
    StrictMonoOn (qaryEntropy q) (Icc 0 (1 - 1/q)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1/(q:ℝ))) _ _ hp1 hp2 p1le2
  · apply qaryEntropy_continuous.continuousOn
  · intro x hx
    have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have zero_le_qinv : 0 < (q : ℝ)⁻¹ := by positivity
    have : 1 - x ∈ Ioi 0 := by
      simp [mem_Ioi, sub_pos, hx.2]
      have x_lt_1_minus_qinv : x < 1 - (q : ℝ)⁻¹ := by
        simp_all only [inv_pos, interior_Icc, mem_Ioo, one_div]
      linarith
    simp only [one_div, interior_Icc, mem_Ioo] at hx
    rw [deriv_qaryEntropy (by linarith)]
    · field_simp
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr hx.1)
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left, show 0 < (q : ℝ) - 1 by linarith]
      · have qpos : 0 < (q : ℝ) := by positivity
        have : q * x < q - 1 := by
          convert (mul_lt_mul_left qpos).2 hx.2 using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : x < 1)).symm

/-- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma binaryEntropy_strictMono : StrictMonoOn binaryEntropy (Icc 0 2⁻¹) := by
  rw [show Icc (0:ℝ) 2⁻¹ = Icc 0 (1 - 1/2) by norm_num]
  exact qaryEntropy_strictMono (by rfl)

/-! ### Strict Concavity of binary and q-ary entropy functions -/

lemma strictConcave_qaryEntropy {q : ℕ} : StrictConcaveOn ℝ (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro x hx
  rw [deriv2_qaryEntropy]
  · simp_all only [interior_Icc, mem_Ioo]
    apply div_neg_of_neg_of_pos
    norm_num [show 0 < log 2 by positivity]
    simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left, sub_pos, hx]

lemma strictConcave_binaryEntropy : StrictConcaveOn ℝ (Icc 0 1) binaryEntropy :=
  strictConcave_qaryEntropy
