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

namespace Entropy

open Real

/-- Shannon q-ary Entropy function (measured in Nats, i.e., using natural logs).

It's the Shannon entropy of a random variable with possible outcomes {1, ..., q}
where outcome `1` has probability `(1 - p)` and all other outcomes are equally likely.

Usual domain of definition is p ∈ [0,1], i.e., input is a probability.

This is a generalization of the binary entropy function `binaryEnrtopy`. -/
noncomputable def qaryEntropy (q : ℕ) (p : ℝ) : ℝ :=
    p * log (q - 1) - p * log p - (1 - p) * log (1 - p)

/-- The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binaryEntropy p := - p * log p - (1-p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`. -/
noncomputable abbrev binaryEntropy := qaryEntropy 2

lemma binaryEntropy_eq : binaryEntropy = (fun p => -p * log p - (1 - p) * log (1 - p)) := by
  unfold binaryEntropy qaryEntropy
  funext p
  rw [Nat.cast_two]
  have : (2 - 1 : ℝ).log = 0 := by
    simp only [log_eq_zero, sub_eq_neg_self, OfNat.ofNat_ne_zero, or_false]
    right
    ring
  rw [this, mul_zero, zero_sub, neg_mul]

lemma binaryEntropy_eq' {p : ℝ} : binaryEntropy p = -p * log p - (1 - p) * log (1 - p) := by
  rw [binaryEntropy_eq]

@[simp] lemma qaryEntropy_zero {q : ℕ} : qaryEntropy q 0 = 0 := by
  unfold qaryEntropy
  simp only [zero_mul, log_zero, mul_zero, sub_self, sub_zero, log_one]

@[simp] lemma binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp only [binaryEntropy_eq', log_one, mul_zero, sub_self, log_zero]

@[simp] lemma qaryEntropy_one {q : ℕ} : qaryEntropy q 1 = log (q - 1) := by
  unfold qaryEntropy
  simp only [log_one, mul_zero, sub_self, log_zero, one_mul, sub_zero]

@[simp] lemma binaryEntropy_onehalf : binaryEntropy (1/2) = log 2 := by
  simp only [binaryEntropy_eq']
  norm_num
  simp only [one_div, log_inv]
  field_simp

/-- `binaryEntropy` is symmetric about 1/2, i.e.,

`binaryEntropy (1 - p) = binaryEntropy q p` -/
@[simp] lemma binaryEntropy_eq_binaryEntropy_one_minus (p : ℝ) :
    binaryEntropy (1 - p) = binaryEntropy p := by
  simp only [binaryEntropy_eq', neg_sub, sub_sub_cancel, neg_mul]
  ring

protected lemma nonneg_reallog_sub_one (n : ℕ) : 0 ≤ Real.log (n - 1) := by
  have : (n : ℝ) - 1 = -1 ∨ (n : ℝ) - 1 = 0 ∨ 1 ≤ (n : ℝ) - 1 := by
    by_cases hzero : n = 0
    · left
      simp only [hzero, Nat.cast_zero, zero_sub]
    · by_cases hzero : n = 1
      · right; left
        simp only [hzero, Nat.cast_one, sub_self]
      · right; right
        have : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr (show 2 ≤ n by omega)
        have := add_le_add_right this (-1)
        convert this using 1
        norm_num
  rcases this with n_negone | n_zero | n_big
  · rw [n_negone]; norm_num
  · rw [n_zero]; norm_num
  · exact log_nonneg n_big

lemma qaryEntropy_gt_0 {q : ℕ} {p : ℝ} (pgt0 : 0 < p) (ple1 : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  have p_q_log_nonneg : 0 ≤ p * ((q : ℝ) - 1).log := by
    rw [mul_nonneg_iff_of_pos_left pgt0]
    exact Entropy.nonneg_reallog_sub_one q
  have rest_is_pos : 0 < -(p * p.log) - (1 - p) * (1 - p).log := by
    have pos_sum_pos_pos (a b : ℝ) (ha : 0 ≤ a) (hb : b < 0) : 0 < a - b := by linarith
    refine pos_sum_pos_pos (-(p * log p)) ((1 - p) * log (1 - p)) ?_ ?_
    · have : -(p * log p) = p * (-log p) := by ring
      rw [this]
      refine LT.lt.le (Real.mul_pos ?_ ?_)
      linarith
      linarith [log_neg pgt0 ple1]
    · have fac1 : 0 < 1 - p := by linarith
      have fac2 : log (1 - p) < 0 := log_neg fac1 (by linarith)
      exact mul_neg_of_pos_of_neg fac1 fac2
  have (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < -b - c) : 0 < a - b - c := by linarith
  exact this (p * ((q : ℝ) - 1).log) (p * p.log) ((1 - p) * (1 - p).log) p_q_log_nonneg rest_is_pos

lemma binaryEntropy_gt_0 {p : ℝ} (pge0 : 0 < p) (ple1 : p < 1) : 0 < binaryEntropy p := by
  exact qaryEntropy_gt_0 pge0 ple1

/-- TODO assumptions not needed? -/
lemma binaryEntropy_zero_iff_zero_or_one {p : ℝ} (domup : p ≤ 1) (domun : 0 ≤ p) :
    binaryEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor <;> intro h
  · by_cases pz : p = 0
    · left; assumption
    · by_cases p_is_one : p = 1
      · right; assumption
      · have : 0 < binaryEntropy p := by
          apply binaryEntropy_gt_0 (Ne.lt_of_le ?_ domun)
          refine Ne.lt_of_le ?_ ?_
          repeat assumption
          exact Iff.mp ne_comm pz
        simp_all only [lt_self_iff_false]
  · rw [binaryEntropy_eq']
    cases h <;> simp [*]

lemma zero_lt_log_two : 0 < log 2 := by
  exact (log_pos_iff zero_lt_two).mpr one_lt_two

/-- For probability p < 0.5,

 binaryEntropy p < log 2.
-/
lemma binaryEntropy_lt_log2_of_gt_half {p : ℝ} (pge0 : 0 ≤ p) (plehalf : p < 1/2) :
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

lemma binaryEntropy_lt_one_of_gt_log2 {p : ℝ} : 1/2 < p → p ≤ 1 → binaryEntropy p < log 2 := by
  intros
  rw [← binaryEntropy_eq_binaryEntropy_one_minus]
  exact binaryEntropy_lt_log2_of_gt_half (by linarith) (by linarith)

lemma binaryEntropy_one_iff_eq_half {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binaryEntropy p = log 2 ↔ p = 1/2 := by
  constructor <;> intro h
  · by_cases h' : p < 1/2
    · linarith [binaryEntropy_lt_log2_of_gt_half pge0 h']
    · by_cases pgthalf : 1/2 < p
      · have := binaryEntropy_lt_one_of_gt_log2 pgthalf ple1
        linarith
      · linarith
  · simp only [h, binaryEntropy_onehalf]

lemma binaryEntropy_le_log_2 {p : ℝ} (pge0 : 0 ≤ p) (ple1 : p ≤ 1) :
    binaryEntropy p ≤ log 2 := by
  by_cases hh: p = 1/2
  · simp only [hh, binaryEntropy_onehalf, le_refl]
  · by_cases gg: binaryEntropy p = log 2
    · simp only [le_refl, gg]
    · by_cases hhh: p < 1/2
      · linarith [binaryEntropy_lt_log2_of_gt_half pge0 hhh]
      · have : 1/2 < p := by
          refine Ne.lt_of_le ?_ ?_
          · simp only [not_lt] at hhh
            intro a
            simp_all only [not_true_eq_false]
          · simp_all only [one_div, not_lt]
        have := binaryEntropy_lt_one_of_gt_log2 this ple1
        exact LT.lt.le this

/- The q-ary entropy function is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
lemma qaryEntropy_continuous {q : ℕ} : Continuous (qaryEntropy q) := by
  unfold qaryEntropy
  apply Continuous.add
  apply Continuous.add
  exact continuous_mul_right (log (q - 1))
  · apply Continuous.neg
    exact continuous_mul_log
  · apply Continuous.neg
    exact Continuous.comp continuous_mul_log (continuous_sub_left 1)

/- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
lemma binaryEntropy_continuous : Continuous binaryEntropy := qaryEntropy_continuous

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
  simp only [differentiableAt_id']

-- TODO don't need assumptions
lemma deriv_log_one_sub {x : ℝ} (hh : x ≠ 1): deriv (fun p ↦ log (1 - p)) x = -(1-x)⁻¹ := by
  rw [deriv.log]
  simp only [deriv_one_minus]
  field_simp
  exact differentiable_const_minus x
  exact sub_ne_zero.mpr hh.symm

@[simp] lemma differentiableAt_log_const_neg {x c : ℝ} (h : x ≠ c) :
    DifferentiableAt ℝ (fun p ↦ log (c - p)) x := by
  apply DifferentiableAt.log
  apply DifferentiableAt.sub
  apply differentiableAt_const
  apply differentiableAt_id'
  exact sub_ne_zero.mpr (id (Ne.symm h))

-- TODO don't need assumptions
lemma deriv_binaryEntropy' {x : ℝ} (h : x ≠ 0) (hh : x ≠ 1) :
    deriv (fun p ↦ -p * p.log - (1 - p) * (1 - p).log) x = log (1 - x) - log x := by
  rw [deriv_sub]
  simp_rw [← neg_mul_eq_neg_mul]
  rw [deriv.neg, deriv_mul_log h]
  simp_rw [mul_sub_right_distrib]
  simp only [one_mul]
  rw [deriv_sub, deriv_log_one_sub hh]
  · rw [deriv_mul, deriv_id'']
    rw [deriv.log]
    simp only [one_mul, deriv_one_minus]
    field_simp
    ring_nf
    calc -1 + (-log x - x * (1 - x)⁻¹) + (1 - x)⁻¹ + log (1 - x)
      _ = -1 + (1 - x) * (1 - x)⁻¹ + log (1 - x) - log x := by ring
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

-- TODO don't need assumptions
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
    convert Entropy.deriv_binaryEntropy' h hh using 2
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

-- TODO don't need assumptions
lemma deriv_binaryEntropy {x : ℝ} (h: x ≠ 0) (hh : x ≠ 1) :
    deriv binaryEntropy x = log (1 - x) - log x := by
  unfold binaryEntropy
  rw [deriv_qaryEntropy h hh]
  simp only [sub_left_inj, add_left_eq_self, log_eq_zero]
  right
  norm_num

/- Binary entropy has derivative `log (1 - p) - log p`. -/
lemma hasDerivAt_binaryEntropy {x : ℝ} (xne0: x ≠ 0) (gne1 : x ≠ 1) :
    HasDerivAt binaryEntropy (log (1 - x) - log x) x := by
  have diffAt : DifferentiableAt ℝ (fun p => -p * log p - (1 - p) * log (1 - p)) x := by
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
  convert hasDerivAt_deriv_iff.mpr diffAt using 1
  exact binaryEntropy_eq
  exact (deriv_binaryEntropy' xne0 gne1).symm

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

/- Second derivative.
TODO Assumptions not needed (use junk value after proving that `¬DifferentiableAt` there) ?!-/
lemma deriv2_qaryEntropy {q : ℕ} {x : ℝ} (h : x ≠ 0) (hh : 1 ≠ x) :
    deriv^[2] (qaryEntropy q) x = -1 / (x * (1-x)) := by
  simp only [Function.iterate_succ]
  suffices ∀ᶠ y in (𝓝 x),
      deriv (fun x ↦ (qaryEntropy q) x) y = log (q - 1) + log (1 - y) - log y by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_sub]
    · repeat rw [deriv_div_const]
      repeat rw [deriv.log differentiableAt_id' h]
      simp only [deriv_one_minus, deriv_id'', one_div]
      · field_simp [sub_ne_zero_of_ne hh]
        ring
    · apply DifferentiableAt.add
      simp_all only [ne_eq, differentiableAt_const]
      exact differentiableAt_log_const_neg hh.symm
    · exact differentiableAt_log h
  filter_upwards [eventually_ne_nhds h, eventually_ne_nhds hh.symm]
    with y h h2 using deriv_qaryEntropy h h2

lemma deriv2_binaryEntropy {x : ℝ} (h : x ≠ 0) (hh : 1 ≠ x) :
    deriv^[2] binaryEntropy x = -1 / (x * (1-x)) := deriv2_qaryEntropy h hh

/-! ### Strict Monotonicity of binary entropy -/

open Set

lemma aux {a b c : ℝ} (h : 0 < a) (hh : a * b < a * c) : b < c := by
  exact (mul_lt_mul_left h).mp hh

lemma inequality_with_conversion {q : ℕ} (qNot0 : 2 ≤ q) {x : ℝ}
    (hx : x < 1 - (↑q)⁻¹) :
    x < (q - 1) * (1 - x) := by
  have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qNot0
  have qnonz : (q : ℝ) ≠ 0 := by linarith
  have zero_le_qinv : 0 < (q : ℝ)⁻¹ := by positivity
  rw [show ((q:ℝ) - 1) * (1 - x) = q - q*x - 1 + x by ring]
  simp only [lt_add_iff_pos_left, lt_neg_add_iff_add_lt, add_zero]
  apply aux zero_le_qinv
  rw [mul_zero]
  have : (q:ℝ)⁻¹ * ((q:ℝ) - (q:ℝ) * x - 1) = 1 - x - (q:ℝ)⁻¹ := by
    calc (q:ℝ)⁻¹ * ((q:ℝ) - (q:ℝ) * x - 1)
      _ = (q:ℝ)⁻¹ * (q:ℝ) - (q:ℝ)⁻¹ * (q:ℝ) * x - (q:ℝ)⁻¹ := by ring
      _ = 1 - x - (q:ℝ)⁻¹ := by
        rw [inv_mul_cancel qnonz]
        simp only [one_mul]
  rw [this]
  linarith

/- Qary entropy is strictly increasing in interval [0, 1 - q⁻¹]. -/
lemma qaryEntropy_strictMono {q : ℕ} (qLe2: 2 ≤ q) :
    StrictMonoOn (qaryEntropy q) (Set.Icc 0 (1 - 1/q)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1/(q:ℝ))) _ _ hp1 hp2 p1le2
  · apply qaryEntropy_continuous.continuousOn
  · intro x hx
    have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have qnonz : (q : ℝ) ≠ 0 := by linarith
    have zero_le_qinv : 0 < (q : ℝ)⁻¹ := by positivity
    have : (q : ℝ)⁻¹ ≠ 0 := inv_ne_zero qnonz
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
      · apply inequality_with_conversion qLe2 hx.2
    exact (ne_of_gt (show x < 1 by exact lt_add_neg_iff_lt.mp this)).symm

/- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma binaryEntropy_strictMono : StrictMonoOn binaryEntropy (Set.Icc 0 (1/2)) := by
  unfold binaryEntropy
  have : Icc (0:ℝ) (1 / 2) = Icc 0 (1 - 1/2) := by norm_num
  rw [this]
  apply qaryEntropy_strictMono (by rfl)


/-! ### Strict Concavity of binary entropy -/

lemma strictConcave_qaryEntropy {q : ℕ} : StrictConcaveOn ℝ (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro x hx
  rw [deriv2_qaryEntropy]
  · simp_all
    apply div_neg_of_neg_of_pos
    norm_num [zero_lt_log_two]
    simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left, sub_pos, hx, zero_lt_log_two]
  · simp_all only [interior_Icc, mem_Ioo]
    exact ne_of_gt hx.1
  · simp_all only [interior_Icc, mem_Ioo]
    exact (ne_of_lt (hx.2)).symm

lemma strictConcave_binaryEntropy :
    StrictConcaveOn ℝ (Icc 0 1) binaryEntropy := strictConcave_qaryEntropy
