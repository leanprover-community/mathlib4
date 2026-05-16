/-
Copyright (c) 2026 Ben Milligan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Milligan
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.ENNReal.Real

/-!
# Advantage from half: signed bias of a `PMF Bool` away from 1/2

This file defines `PMF.advantageFromHalf : PMF Bool → ℝ`, the signed gap of the
`true`-probability of a Boolean probability mass function away from `1/2`,
rescaled to the interval `[-1, 1]`.

The notion appears in computational-complexity formalizations as the *advantage*
of a heuristic decision algorithm `H` over a uniform input distribution: when
`H : α → Bool` is post-composed with `PMF.uniformOfFintype α` via `PMF.map`,
the resulting `PMF Bool` carries the advantage of `H` on `α` as its
`advantageFromHalf` value.  In particular, Hirahara 2018 (FOCS,
arXiv:1808.06974) Theorem 1.1's worst-case-to-average-case reduction for
Gap-MCSP requires expressing the heuristic algorithm's advantage
`ε(n) = 1/poly(n)` over the uniform truth-table distribution; the current
Mathlib `PMF` library supports `PMF.uniformOfFintype` but lacks the
bias-from-half notion at this signature.

## Main definitions

* `PMF.advantageFromHalf` — the advantage from half of a `PMF Bool`,
  defined as `2 * (p true).toReal - 1`.

## Main results

* `PMF.advantageFromHalf_le_one`     — `p.advantageFromHalf ≤ 1`.
* `PMF.advantageFromHalf_neg_one_le` — `-1 ≤ p.advantageFromHalf`.
* `PMF.advantageFromHalf_eq_zero_iff_half`
    — `p.advantageFromHalf = 0 ↔ (p true).toReal = 1/2`.
* `PMF.advantageFromHalf_map_tsum`   — composition with `PMF.map`.

## Tags

probability mass function, PMF, advantage, bias, Bernoulli, decision algorithm
-/

@[expose] public section

namespace PMF

open ENNReal

/-- The **advantage from half** of a `Bool`-valued probability mass function:
the signed gap of the `true`-probability away from `1/2`, scaled to `[-1, 1]`.

For a heuristic decision algorithm `H : α → Bool` applied to a `PMF α` via
`PMF.map`, this is the advantage of `H` as a decision procedure (Hirahara 2018
FOCS, arXiv:1808.06974, Theorem 1.1). -/
noncomputable def advantageFromHalf (p : PMF Bool) : ℝ :=
  2 * (p true).toReal - 1

@[simp]
theorem advantageFromHalf_le_one (p : PMF Bool) :
    advantageFromHalf p ≤ 1 := by
  unfold advantageFromHalf
  have hle : (p true).toReal ≤ 1 := by
    have h1 : (p true) ≤ 1 := p.coe_le_one true
    have h2 : (p true).toReal ≤ (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by norm_num) h1
    simpa using h2
  linarith

@[simp]
theorem advantageFromHalf_neg_one_le (p : PMF Bool) :
    -1 ≤ advantageFromHalf p := by
  unfold advantageFromHalf
  have hnn : (0 : ℝ) ≤ (p true).toReal := ENNReal.toReal_nonneg
  linarith

theorem advantageFromHalf_eq_zero_iff_half (p : PMF Bool) :
    advantageFromHalf p = 0 ↔ (p true).toReal = 1 / 2 := by
  unfold advantageFromHalf
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- The advantage of a `PMF Bool` produced by `PMF.map`, expressed as a `tsum`
over the source `PMF`.  Convenient form for downstream decision-algorithm
formalizations. -/
theorem advantageFromHalf_map_tsum {α : Type*} (q : PMF α) (f : α → Bool) :
    advantageFromHalf (q.map f) =
      2 * (∑' a, @ite ℝ≥0∞ (true = f a) (Classical.propDecidable _) (q a) 0).toReal - 1 := by
  unfold advantageFromHalf
  rw [PMF.map_apply f q true]

/-- **Zero-advantage:** the uniform `PMF Bool` has advantage `0`. -/
theorem advantageFromHalf_uniformBool :
    advantageFromHalf (PMF.uniformOfFintype Bool) = 0 := by
  unfold advantageFromHalf
  rw [PMF.uniformOfFintype_apply (α := Bool) true]
  rw [Fintype.card_bool, ENNReal.toReal_inv]
  norm_num

/-- **Upper extremal:** `pure true` has advantage `1`. -/
theorem advantageFromHalf_pure_true :
    advantageFromHalf (PMF.pure true) = 1 := by
  unfold advantageFromHalf
  rw [PMF.pure_apply_self true]
  norm_num

/-- **Lower extremal:** `pure false` has advantage `-1`. -/
theorem advantageFromHalf_pure_false :
    advantageFromHalf (PMF.pure false) = -1 := by
  unfold advantageFromHalf
  rw [PMF.pure_apply_of_ne false true (by decide)]
  simp

end PMF
