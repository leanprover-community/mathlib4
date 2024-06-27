/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of (Shannon) q-ary entropy and binary entropy functions

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binaryEntropy p := - p * log p - (1 - p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

More generally, the q-ary entropy function is the Shannon entropy of the random variable
with possible outcomes `{1, ..., q}`, where outcome `1` has probability `(1 - p)`
and all other outcomes are equally likely.

`qaryEntropy (q : ℕ) (p : ℝ) := p * log (q - 1) - p * log p - (1 - p) * log (1 - p)`

This file assumes that entropy is measured in Nats, hence the use of natural logarithms.
Most lemmas are also valid using a different-base logarithms.

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
  simp only [binaryEntropy_eq']
  have : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  simp only [this, log_inv]
  field_simp

/-- `binaryEntropy` is symmetric about 1/2, i.e., `binaryEntropy (1 - p) = binaryEntropy p` -/
@[simp] lemma binaryEntropy_one_sub (p : ℝ) :
    binaryEntropy (1 - p) = binaryEntropy p := by
  simp only [binaryEntropy_eq', neg_sub, sub_sub_cancel, neg_mul]
  ring

lemma qaryEntropy_eq_log_mul_add_binaryEntropy {q : ℕ} {p : ℝ} :
    qaryEntropy q p = p * log (q - 1) + binaryEntropy p := by
  unfold binaryEntropy qaryEntropy
  rw [show ((2:ℕ) - (1:ℝ)).log = 0 by norm_num]
  ring

lemma qaryEntropy_eq_log_mul_add_binaryEntropy' {q : ℕ} :
    qaryEntropy q = (fun p ↦ p * log (q - 1)) + binaryEntropy := by
  ext
  simp only [Pi.add_apply]
  exact qaryEntropy_eq_log_mul_add_binaryEntropy

lemma binaryEntropy_pos {p : ℝ} (pgt0 : 0 < p) (ple1 : p < 1) : 0 < binaryEntropy p := by
  simp only [binaryEntropy_eq']
  have pos_sum_pos_pos (a b : ℝ) (ha : 0 ≤ a) (hb : b < 0) : 0 < a - b := by linarith
  refine pos_sum_pos_pos (-p * log p) ((1 - p) * log (1 - p)) ?_ ?_
  · have : -p * log p = p * (-log p) := by ring
    rw [this]
    refine LT.lt.le (Real.mul_pos ?_ ?_)
    linarith
    linarith [log_neg pgt0 ple1]
  · have fac1 : 0 < 1 - p := by linarith
    have fac2 : log (1 - p) < 0 := log_neg fac1 (by linarith)
    exact mul_neg_of_pos_of_neg fac1 fac2

lemma qaryEntropy_pos {q : ℕ} {p : ℝ} (pgt0 : 0 < p) (ple1 : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  have p_q_log_nonneg : 0 ≤ p * ((q : ℝ) - 1).log := by
    rw [mul_nonneg_iff_of_pos_left pgt0]
    have : q - (1 : ℝ) = (q - 1 : ℤ) := by norm_cast
    rw [this]
    exact Real.log_intCast_nonneg _
  have rest_is_pos : 0 < -(p * p.log) - (1 - p) * (1 - p).log := by
    simp only [← neg_mul, ← binaryEntropy_eq']
    exact binaryEntropy_pos pgt0 ple1
  have (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < -b - c) : 0 < a - b - c := by linarith
  exact this (p * ((q : ℝ) - 1).log) (p * p.log) ((1 - p) * (1 - p).log) p_q_log_nonneg rest_is_pos

-- TODO assumptions not needed?
lemma binaryEntropy_zero_iff_zero_or_one {p : ℝ} (domup : p ≤ 1) (domun : 0 ≤ p) :
    binaryEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor <;> intro h
  · by_cases pz : p = 0
    · left; assumption
    · by_cases p_is_one : p = 1
      · right; assumption
      · have : 0 < binaryEntropy p := by
          apply binaryEntropy_pos (Ne.lt_of_le ?_ domun)
          refine Ne.lt_of_le ?_ ?_
          repeat assumption
          exact Iff.mp ne_comm pz
        simp_all only [lt_self_iff_false]
  · rw [binaryEntropy_eq']
    cases h <;> simp [*]

lemma zero_lt_log_two : 0 < log 2 := by
  exact (log_pos_iff zero_lt_two).mpr one_lt_two

/-- For probability `p < 0.5`, `binaryEntropy p < log 2`. -/
lemma binaryEntropy_lt_log2_of_lt_half {p : ℝ} (pge0 : 0 ≤ p) (plehalf : p < 1/2) :
    binaryEntropy p < log 2 := by
  -- Proof by concavity of log.
  rw [binaryEntropy_eq']
  rw [show -p * p.log = -(p * p.log) by ring]
  by_cases pz : p = 0
  · simp [*]; exact zero_lt_log_two
  · have invppos : 0 < 1/p := by positivity
    have : 0 < 1 - p := by norm_num; linarith -- used implicitly by tactics.
    have sub1pinvpos : 0 < 1 / (1 - p) := by positivity
    have logConcave := (strictConcaveOn_log_Ioi.right
      (x := 1/p) (y := 1/(1-p))) (a := p) (b := 1-p)
      invppos sub1pinvpos (by norm_num; linarith) (by positivity)
      (by norm_num; linarith) (by norm_num)
    have : p • (1 / p) + (1 - p) • (1 / (1 - p)) = 2 := by field_simp; norm_num
    rw [this] at logConcave
    have := calc -(p * log p) - (1 - p) * log (1 - p)
          _ = p * (-log p) + (1 - p) * (-log (1 - p)) := by ring
          _ = p * log (1/p) + (1 - p) * log (1 / (1 - p)) := by rw [← log_inv]; norm_num
    rw [this]
    exact logConcave

lemma binaryEntropy_lt_log2_of_gt_half {p : ℝ} : 1/2 < p → p ≤ 1 → binaryEntropy p < log 2 := by
  intros
  rw [← binaryEntropy_one_sub]
  exact binaryEntropy_lt_log2_of_lt_half (by linarith) (by linarith)

lemma binaryEntropy_eq_log2_iff_eq_half {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binaryEntropy p = log 2 ↔ p = 1/2 := by
  constructor <;> intro h
  · by_cases h' : p < 1/2
    · linarith [binaryEntropy_lt_log2_of_lt_half pge0 h']
    · by_cases pgthalf : 1/2 < p
      · have := binaryEntropy_lt_log2_of_gt_half pgthalf ple1
        linarith
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
          · simp only [not_lt] at hhh
            intro a
            simp_all only [not_true_eq_false]
          · simp_all only [one_div, not_lt]
        have := binaryEntropy_lt_log2_of_gt_half this ple1
        exact LT.lt.le this

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

@[simp] lemma deriv_one_minus (x : ℝ) : deriv (fun (y : ℝ) ↦ 1 - y) x = -1 := by
  have onem (y : ℝ) : 1 - y = -(y + -1) := by ring
  simp_rw [onem]
  simp only [neg_add_rev, neg_neg, differentiableAt_const, deriv_const_add', deriv_neg'']

@[simp] lemma differentiable_const_minus {q : ℝ} (p : ℝ) :
    DifferentiableAt ℝ (fun p => q - p) p := by
  have (p : ℝ) : q - p = -(p - q) := by ring
  simp_rw [this]
  apply differentiableAt_neg_iff.mpr
  apply DifferentiableAt.add_const
  exact differentiableAt_id'

section general

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f f₀ f₁ g : E → F}
variable {x : E}

-- TODO clean up, put somewhere else?
lemma not_DifferentiableAt_of_not_DifferentiableAt_add_DifferentiableAt_
    (hf : ¬ DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ¬ DifferentiableAt 𝕜 (fun y => f y + g y) x := by
  have f_eq_sum_sub_g: f = (fun y => f y + g y) - g := by
    ext
    simp only [Pi.sub_apply, add_sub_cancel_right]
  by_contra
  have : DifferentiableAt 𝕜 f x := by
    rw [f_eq_sum_sub_g]
    apply DifferentiableAt.sub
    · simp
      assumption
    · assumption
  contradiction

-- TODO clean up, put somewhere else?
lemma not_DifferentiableAt_of_DifferentiableAt_add_not_DifferentiableAt
    (hf : DifferentiableAt 𝕜 f x) (hg : ¬ DifferentiableAt 𝕜 g x) :
     ¬ DifferentiableAt 𝕜 (fun y => f y + g y) x := by
  rw [show (fun y ↦ f y + g y) = (fun y ↦ g y + f y) by ext; rw [add_comm]]
  exact not_DifferentiableAt_of_not_DifferentiableAt_add_DifferentiableAt_ hg hf

lemma differentiableAt_iff_differentiableAt_comp_mul_add
    {a b m : 𝕜} (hm : m ≠ 0) (f : 𝕜 → E) :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x => f (m * x + b)) (m⁻¹ * (a - b)):= by
  constructor <;> intro h
  · apply DifferentiableAt.comp
    have : (m * (m⁻¹ * (a - b)) + b) = a := by
      simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel_left,
        sub_add_cancel]
    rw [this]
    exact h
    apply DifferentiableAt.add
    · exact DifferentiableAt.mul (differentiableAt_const m) differentiableAt_id'
    · exact differentiableAt_const b
  · have diff_affine : DifferentiableAt 𝕜 (fun x => m⁻¹ * (x - b)) a := by
      apply DifferentiableAt.mul (differentiableAt_const m⁻¹)
      apply DifferentiableAt.sub_const differentiableAt_id'
    have : f = (fun x ↦ f (m * x + b)) ∘ (fun x => m⁻¹ * (x - b)) := by
        ext
        simp only [Function.comp_apply]
        field_simp
    rw [this]
    apply DifferentiableAt.comp
    exact h
    exact diff_affine

@[simp]
lemma fderiv_deriv' {f : 𝕜 → 𝕜} {x y : 𝕜} : (fderiv 𝕜 f x : 𝕜 → 𝕜) y = (deriv f x) * y := by
  rw [← deriv_fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

end general

lemma differentiableAt_binaryEntropy {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    DifferentiableAt ℝ (fun p => -p * log p - (1 - p) * log (1 - p)) x := by
  apply DifferentiableAt.sub
  apply DifferentiableAt.mul
  apply DifferentiableAt.neg
  exact differentiableAt_id'
  apply DifferentiableAt.log differentiableAt_id' xne0
  apply DifferentiableAt.mul
  apply DifferentiableAt.sub
  apply differentiableAt_const
  exact differentiableAt_id'
  apply DifferentiableAt.log
  apply DifferentiableAt.sub
  apply differentiableAt_const
  exact differentiableAt_id'
  exact sub_ne_zero.mpr gne1.symm

lemma differentiableAt_binaryEntropy' {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    DifferentiableAt ℝ binaryEntropy x := by
  simp only [binaryEntropy_eq]
  exact differentiableAt_binaryEntropy xne0 gne1

lemma differentiableAt_binaryEntropy_iff_ne_zero_one (x : ℝ) :
    DifferentiableAt ℝ binaryEntropy x ↔ x ≠ 0 ∧ x ≠ 1 := by
  refine ⟨?_, fun ne0Ne1 ↦ differentiableAt_binaryEntropy' ne0Ne1.1 ne0Ne1.2⟩
  by_contra h
  simp_all
  obtain ⟨is_diff, hx⟩ := h
  rw [binaryEntropy_eq] at is_diff
  by_cases is_x0 : x ≠ 0
  · rw[hx is_x0] at is_diff
    apply not_DifferentiableAt_of_DifferentiableAt_add_not_DifferentiableAt _ _ is_diff
    · apply DifferentiableAt.mul
       (DifferentiableAt.neg differentiableAt_id') (DifferentiableAt.log differentiableAt_id' _)
      simp only [ne_eq, one_ne_zero, not_false_eq_true]
    · have diff_of_aff := (differentiableAt_iff_differentiableAt_comp_mul_add
        (a:=(0:ℝ)) (b:=(1 : ℝ)) (m:=(-1:ℝ)) (show (-1 : ℝ) ≠ 0 by norm_num) negMulLog).mpr
      intro h
      have : DifferentiableAt ℝ (fun (x : ℝ) ↦ (-1 * x + 1).negMulLog) ((-1)⁻¹ * (0 - 1)) := by
        convert h using 1
        · ext
          simp [negMulLog]
          ring_nf
        · ring
      have := diff_of_aff this
      have := differentiableAt_negMulLog_iff.mp this
      contradiction
  · have : x = 0 := by simp_all only [neg_mul, false_implies, ne_eq, Decidable.not_not]
    rw [this] at is_diff
    apply not_DifferentiableAt_of_not_DifferentiableAt_add_DifferentiableAt_ _ _ is_diff
    · simp only [neg_mul, differentiableAt_neg_iff, not_DifferentiableAt_log_mul_zero,
        not_false_eq_true]
    · apply DifferentiableAt.neg
      apply DifferentiableAt.mul
      apply differentiable_const_minus
      apply DifferentiableAt.log
      exact differentiable_const_minus 0
      simp only [sub_zero, ne_eq, one_ne_zero, not_false_eq_true]

open Filter Real Topology Asymptotics

lemma deriv_log_one_sub_at_1 : deriv (fun p ↦ log (1 - p)) 1 = 0 := by
  have : ¬ DifferentiableAt ℝ (fun p ↦ log (1 - p)) 1 := by
    by_contra
    have : ¬ DifferentiableAt ℝ log 0 := by
      simp_all only [differentiable_const_minus, implies_true, differentiableAt_log_iff, ne_eq,
        not_true_eq_false, not_false_eq_true]
    have : DifferentiableAt ℝ log 0 := by
      have : Real.log = (fun p ↦ log (1 - p)) ∘ (fun x => 1 - x) := by
        ext
        simp only [Function.comp_apply, sub_sub_cancel]
      rw [this]
      apply DifferentiableAt.comp
      · simp only [sub_zero, differentiable_const_minus]
        assumption
      · exact differentiable_const_minus 0
    contradiction
  exact deriv_zero_of_not_differentiableAt this

lemma deriv_log_one_sub {x : ℝ} : deriv (fun p ↦ log (1 - p)) x = -(1-x)⁻¹ := by
  by_cases xis1 : x = 1
  · rw [xis1]
    simp only [sub_self, inv_zero, neg_zero]
    exact deriv_log_one_sub_at_1
  · rw [deriv.log]
    simp only [deriv_one_minus]
    field_simp
    exact differentiable_const_minus x
    exact sub_ne_zero_of_ne fun a ↦ xis1 a.symm

@[simp] lemma differentiableAt_log_const_neg {x c : ℝ} (h : x ≠ c) :
    DifferentiableAt ℝ (fun p ↦ log (c - p)) x := by
  apply DifferentiableAt.log
  apply DifferentiableAt.sub
  apply differentiableAt_const
  apply differentiableAt_id'
  exact sub_ne_zero.mpr h.symm

/-- Binary entropy has derivative `log (1 - p) - log p`.
It's not differentiable at `0` or `1` but the junk values of `deriv` and `log` coincide there. -/
lemma deriv_binaryEntropy' {x : ℝ} :
    deriv (fun p ↦ -p * p.log - (1 - p) * (1 - p).log) x = log (1 - x) - log x := by
  by_cases is_x_where_nondiff : x ≠ 0 ∧ x ≠ 1
  · obtain ⟨h, hh⟩ := is_x_where_nondiff
    rw [deriv_sub]
    simp_rw [← neg_mul_eq_neg_mul]
    rw [deriv.neg, deriv_mul_log h]
    simp_rw [mul_sub_right_distrib]
    simp only [one_mul]
    rw [deriv_sub, deriv_log_one_sub]
    · rw [deriv_mul, deriv_id'']
      rw [deriv.log]
      simp only [one_mul, deriv_one_minus]
      field_simp
      ring_nf
      calc -1 + (-log x - x * (1 - x)⁻¹) + (1 - x)⁻¹ + log (1 - x)
        _ = -log x + log (1 - x) := by
          field_simp [sub_ne_zero.mpr hh.symm]
          ring
      exact differentiable_const_minus x
      exact sub_ne_zero.mpr hh.symm
      apply differentiableAt_id'
      exact differentiableAt_log_const_neg hh
    · exact differentiableAt_log_const_neg hh
    · apply DifferentiableAt.mul
      apply differentiableAt_id'
      apply DifferentiableAt.log
      exact differentiable_const_minus x
      exact sub_ne_zero.mpr hh.symm
    · apply DifferentiableAt.mul
      apply DifferentiableAt.neg
      exact differentiableAt_id'
      exact differentiableAt_log h
    · apply DifferentiableAt.mul
      apply differentiable_const_minus
      exact differentiableAt_log_const_neg hh
  · have : x = 0 ∨ x = 1 := Decidable.or_iff_not_and_not.mpr is_x_where_nondiff
    rw [← binaryEntropy_eq]
    rw [deriv_zero_of_not_differentiableAt]
    · cases this with  -- surely this can be shortened?
        | inl xis0 => simp only [xis0, sub_zero, log_one, log_zero, sub_self]
        | inr xis1 => simp only [xis1, sub_zero, log_one, log_zero, sub_self]
    · intro h
      have := (differentiableAt_binaryEntropy_iff_ne_zero_one x).mp h
      simp_all only [ne_eq, not_true_eq_false, zero_ne_one, not_false_eq_true, and_true]

lemma deriv_qaryEntropy' {q : ℕ} {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) :
    deriv (fun p => p * log (q - 1) - p * log p - (1 - p) * log (1 - p)) x
       = log (q - 1) + log (1 - x) - log x := by
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
    apply DifferentiableAt.neg
    apply DifferentiableAt.mul
    apply differentiableAt_id'
    apply DifferentiableAt.log differentiableAt_id' h
    apply DifferentiableAt.mul
    apply differentiable_const_minus
    apply DifferentiableAt.log (differentiable_const_minus x) (sub_ne_zero_of_ne hh.symm)

lemma deriv_qaryEntropy {q : ℕ} {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) :
    deriv (qaryEntropy q) x = log (q - 1) + log (1 - x) - log x := by
  unfold qaryEntropy
  exact deriv_qaryEntropy' h hh

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
  exact binaryEntropy_eq
  exact (deriv_binaryEntropy').symm

lemma hasDerivAt_qaryEntropy {q : ℕ} {x : ℝ} (qnot1 : q ≠ 1) (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - x) - log x) x := by
  have diffAt :
      DifferentiableAt ℝ (fun p => p * log (q - 1) - p * log p - (1 - p) * log (1 - p)) x := by
    apply DifferentiableAt.sub
    apply DifferentiableAt.sub
    apply DifferentiableAt.mul
    exact differentiableAt_id'
    apply DifferentiableAt.log
    simp only [ne_eq, differentiableAt_const]
    exact sub_ne_zero_of_ne (Nat.cast_ne_one.mpr qnot1)
    apply DifferentiableAt.mul
    exact differentiableAt_id'
    apply DifferentiableAt.log differentiableAt_id' xne0
    apply DifferentiableAt.mul
    apply DifferentiableAt.sub
    apply differentiableAt_const
    exact differentiableAt_id'
    exact differentiableAt_log_const_neg gne1
  convert hasDerivAt_deriv_iff.mpr diffAt using 1
  exact Eq.symm (deriv_qaryEntropy' xne0 gne1)

open Filter Topology


-- TODO delete
lemma tendsto_nhdsWithin_of_eventuallyEq (f g : ℝ → ℝ) (x : ℝ) (l : Filter ℝ)
    (evEq : f =ᶠ[𝓝[>] x] g) (ftend: Tendsto f (𝓝[>] x) l) :
    Tendsto g (𝓝[>] x) l := Filter.Tendsto.congr' evEq ftend

lemma eventuallyEq_nhdsWithin_of_eqOn_interval
    (f g : ℝ → ℝ) (x ε : ℝ) (epsPos : 0 < ε) (h : ∀ y ∈ Set.Ioo x (x + ε), f y = g y) :
    f =ᶠ[𝓝[>] x] g := by
  apply eventuallyEq_nhdsWithin_iff.mpr
  apply Metric.eventually_nhds_iff.mpr
  use ε
  constructor
  · exact epsPos
  · intro y yclose ygex
    have : y ∈ Set.Ioo x (x + ε) := by
      simp_all only [Set.mem_Ioo, and_imp, Set.mem_Ioi, true_and]
      have : dist y x = y - x := by
        simp_all only [Real.dist_eq, abs_eq_self, sub_nonneg, le_of_lt ygex]
      linarith
    simp_all only [Set.mem_Ioo, and_imp, Set.mem_Ioi, true_and]

lemma eventuallyEq_nhdsWithin_of_eqOn_interval_left
    (f g : ℝ → ℝ) (x ε : ℝ) (epsPos : 0 < ε) (h : ∀ y ∈ Set.Ioo (x - ε) x, f y = g y) :
    f =ᶠ[𝓝[<] x] g := by
  apply eventuallyEq_nhdsWithin_iff.mpr
  apply Metric.eventually_nhds_iff.mpr
  use ε
  constructor
  · exact epsPos
  · intro y yclose ygex
    have : y ∈ Set.Ioo (x - ε) x := by
      simp_all only [Set.mem_Ioo, and_imp, Set.mem_Ioi, true_and]
      constructor
      · simp_all only [Set.mem_Iio]
        exact sub_lt_of_abs_sub_lt_left yclose
      · exact ygex
    simp_all only [Set.mem_Ioo, and_imp, Set.mem_Ioi, true_and]

-- TODO remove
lemma ne_one_of_lt_onehalf (x : ℝ) (hx : x < 2⁻¹) : x ≠ 1 := by
  linarith [two_inv_lt_one (α:=ℝ)]

lemma tendsto_atTop_if_tendsto_neg_atBot {f : ℝ → ℝ} {l : Filter ℝ} :
    Tendsto f l atBot ↔ Tendsto (fun x ↦ -f x) l atTop := by
  constructor
  · apply Tendsto.comp
    exact tendsto_neg_atBot_atTop
  · intro
    simp_all only [tendsto_neg_atTop_iff]

private lemma tendsto_log_one_sub_sub_log_nhdsWithin_atAtop :
    Tendsto (fun (x:ℝ) ↦ (1 - x).log - x.log) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1/2) : ℝ)
  · have : 𝓝[>] (0:ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
    apply Eventually.filter_mono this
    apply Metric.eventually_nhds_iff.mpr
    use 1/2
    constructor
    · norm_num
    · intro y hy
      suffices log (1 / 2) < (1 - y).log by linarith
      apply Real.strictMonoOn_log
      · norm_num
      · simp_all
        have : y < 2⁻¹ := lt_of_abs_lt hy
        linarith [two_inv_lt_one (α:=ℝ)]
      · simp_all
        have : (1 : ℝ) = 2⁻¹ + 2⁻¹ := by norm_num
        by_cases ypos : 0 < y
        · have : y < 2⁻¹ := lt_of_abs_lt hy
          linarith
        · have : (0 : ℝ) < 2⁻¹ := by simp_all only [not_lt, inv_pos, Nat.ofNat_pos]
          have : -2⁻¹ < y := neg_lt_of_abs_lt hy
          linarith
  · apply tendsto_atTop_if_tendsto_neg_atBot.mp tendsto_log_nhdsWithin_zero_right

private lemma tendsto_log_one_sub_sub_log_nhdsWithin_one_atBot :
    Tendsto (fun (x:ℝ) ↦ (1 - x).log - x.log) (𝓝[<] 1) atBot := by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsWithin_zero_right
    apply Tendsto.comp (f:=(fun x ↦ 1 - x)) (g:=Real.log) this
    have contF : Continuous (fun (x:ℝ) ↦ 1 - x) := by exact continuous_sub_left 1
    have : Set.MapsTo (fun (x:ℝ) ↦ 1 - x)  (Set.Iio 1) (Set.Ioi 0) := by
      intro x hx
      simp_all only [Set.mem_Iio, Set.mem_Ioi, sub_pos]
    convert ContinuousWithinAt.tendsto_nhdsWithin (x:=(1:ℝ)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have : 𝓝[<] (1:ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
    apply Eventually.filter_mono this
    apply Metric.eventually_nhds_iff.mpr
    use 2⁻¹
    simp_all only [Real.dist_eq]
    constructor
    · norm_num
    · intro y hy
      simp only [neg_le_neg_iff]
      suffices log (1 - 2⁻¹) < y.log by linarith
      apply strictMonoOn_log
      simp
      · norm_num
      · by_cases abspos : 0 ≤ y - 1
        · simp [abs_eq_self.mpr abspos] at hy
          have : 0 < y := by
            linarith
          exact this
        · have :  y - 1 ≤ 0 := by linarith
          simp [abs_eq_neg_self.mpr this] at hy
          have : 0 < y := by
            have : (1:ℝ) = 2⁻¹ + 2⁻¹ := by norm_num
            linarith
          exact this
      · by_cases abspos : 0 ≤ y - 1
        · simp [abs_eq_self.mpr abspos] at hy
          linarith
        · have : |y - 1| = 1 - y := by
            have :  y - 1 ≤ 0 := by linarith
            simp_all only [abs_eq_neg_self.mpr this]
            simp only [neg_sub]
          rw [this] at hy
          linarith


theorem extracted_1 {q : ℕ} {x : ℝ}
    (h : DifferentiableAt ℝ (deriv (qaryEntropy q)) x)
    (contAt : ContinuousAt (deriv (qaryEntropy q)) x) (xis1 : x = 1) :
    ¬ContinuousAt (deriv (qaryEntropy q)) x := by
  apply not_continuousAt_of_tendsto_nhdsWithin_Iio_atBot
  rw [xis1]
  have asdf : Tendsto (fun x ↦ log (q - 1) + log (1 - x) - log x) (𝓝[<] 1) atBot := by
    have : (fun (x:ℝ) ↦ log (q - 1) + (1 - x).log - x.log)
      = (fun x ↦ log (q - 1) + ((1 - x).log - x.log)) := by
      ext x
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsWithin_one_atBot
  apply Filter.Tendsto.congr' _ asdf
  apply eventuallyEq_nhdsWithin_of_eqOn_interval_left (fun x ↦ log (q - 1) + log (1 - x) - log x)
    (deriv (qaryEntropy q)) 1 2⁻¹
  · norm_num
  · intro y hy
    apply Eq.symm (deriv_qaryEntropy _ _)
    simp_all
    · have : (1 : ℝ) = 2⁻¹ + 2⁻¹ := by norm_num
      linarith
    · simp_all
      linarith [two_inv_lt_one (α:=ℝ)]

private lemma extracted_2 {q : ℕ} {x : ℝ}
  (h : DifferentiableAt ℝ (deriv (qaryEntropy q)) x)
  (contAt : ContinuousAt (deriv (qaryEntropy q)) x) (xis0 : x = 0) :
  ¬ContinuousAt (deriv (qaryEntropy q)) x := by
  apply not_continuousAt_of_tendsto_nhdsWithin_Ioi_atTop
  rw [xis0]
  have asdf : Tendsto (fun x ↦ log (q - 1) + log (1 - x) - log x) (𝓝[>] 0) atTop := by
    have : (fun (x:ℝ) ↦ log (q - 1) + (1 - x).log - x.log)
      = (fun x ↦ log (q - 1) + ((1 - x).log - x.log)) := by
      ext x
      ring
    rw [this]
    apply tendsto_atTop_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsWithin_atAtop
  apply Filter.Tendsto.congr' _ asdf
  apply eventuallyEq_nhdsWithin_of_eqOn_interval (fun x ↦ log (q - 1) + log (1 - x) - log x)
    (deriv (qaryEntropy q)) 0 2⁻¹
  · norm_num
  · intro y hy
    apply Eq.symm (deriv_qaryEntropy _ _)
    simp_all
    · linarith
    · simp_all
      linarith [two_inv_lt_one (α:=ℝ)]

/-- Second derivative of q-ary entropy. -/
lemma deriv2_qaryEntropy {q : ℕ} {x : ℝ} :
    deriv^[2] (qaryEntropy q) x = -1 / (x * (1 - x)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : x ≠ 0 ∧ x ≠ 1
  · obtain ⟨h, hh⟩ := is_x_where_nondiff
    suffices ∀ᶠ y in (𝓝 x),
        deriv (fun x ↦ (qaryEntropy q) x) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_sub]
      · repeat rw [deriv_div_const]
        repeat rw [deriv.log differentiableAt_id' h]
        simp only [deriv_one_minus, deriv_id'', one_div]
        · field_simp [sub_ne_zero_of_ne hh.symm]
          ring
      · apply DifferentiableAt.add
        simp_all only [ne_eq, differentiableAt_const]
        exact differentiableAt_log_const_neg hh
      · exact differentiableAt_log h
    filter_upwards [eventually_ne_nhds h, eventually_ne_nhds hh]
      with y h h2 using deriv_qaryEntropy h h2
  · have : x = 0 ∨ x = 1 := Decidable.or_iff_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    simp_all only [ne_eq, not_and, Decidable.not_not]
    · cases this with  -- surely this can be shortened?
      | inl xis0 => simp_all only [zero_ne_one, sub_zero, mul_one, div_zero]
      | inr xis1 => simp_all only [one_ne_zero, sub_self, mul_zero, div_zero]
    · intro h
      have contAt := h.continuousAt
      cases this with
      | inl xis0 =>
        have := extracted_2 h contAt xis0
        contradiction
      | inr xis1 =>
        have := extracted_1 h contAt xis1
        contradiction

lemma deriv2_binaryEntropy {x : ℝ} : deriv^[2] binaryEntropy x = -1 / (x * (1-x)) :=
  deriv2_qaryEntropy

/-! ### Strict Monotonicity of binary entropy -/

open Set

lemma aux {a b c : ℝ} (h : 0 < a) (hh : a * b < a * c) : b < c := by
  exact (mul_lt_mul_left h).mp hh

/-- Qary entropy is strictly increasing in interval [0, 1 - q⁻¹]. -/
lemma qaryEntropy_strictMono {q : ℕ} (qLe2: 2 ≤ q) :
    StrictMonoOn (qaryEntropy q) (Set.Icc 0 (1 - 1/q)) := by
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
      have : log (q - 1) + log (1 - x) = log ((q - 1)*(1 - x)) := by
        rw [← log_mul]
        linarith
        linarith
      rw [this]
      apply Real.strictMonoOn_log
      · exact mem_Ioi.mpr hx.1
      · have : 0 < (q : ℝ) - 1 := by linarith
        simp_all only [mem_Ioi, mul_pos_iff_of_pos_left]
      · have qpos : 0 < (q : ℝ) := by positivity
        have : q * x < q - 1 := by
          convert (mul_lt_mul_left qpos).2 hx.2 using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : x < 1)).symm

/-- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma binaryEntropy_strictMono : StrictMonoOn binaryEntropy (Set.Icc 0 2⁻¹) := by
  unfold binaryEntropy
  have : Icc (0:ℝ) 2⁻¹ = Icc 0 (1 - 1/2) := by norm_num
  rw [this]
  apply qaryEntropy_strictMono (by rfl)

/-! ### Strict Concavity of binary and q-ary entropy functions -/

lemma strictConcave_qaryEntropy {q : ℕ} : StrictConcaveOn ℝ (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro x hx
  rw [deriv2_qaryEntropy]
  · simp_all
    apply div_neg_of_neg_of_pos
    norm_num [zero_lt_log_two]
    simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left, sub_pos, hx, zero_lt_log_two]

lemma strictConcave_binaryEntropy :
    StrictConcaveOn ℝ (Icc 0 1) binaryEntropy := strictConcave_qaryEntropy
