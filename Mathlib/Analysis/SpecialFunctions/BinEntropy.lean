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

/-- Binary entropy has derivative `log (1 - p) - log p`. -/
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

-- TODO Assumptions not needed (use junk value after proving that ¬DifferentiableAt there)
/-- Second derivative of q-ary entropy. -/
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
  · simp_all only [interior_Icc, mem_Ioo]
    exact ne_of_gt hx.1
  · simp_all only [interior_Icc, mem_Ioo]
    exact (ne_of_lt (hx.2)).symm

lemma strictConcave_binaryEntropy :
    StrictConcaveOn ℝ (Icc 0 1) binaryEntropy := strictConcave_qaryEntropy
