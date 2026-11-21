/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAlg

/-!
# Gelfond-Schneider Theorem: arithmetic of the parameters `m`, `n` and `q`

This file collects the elementary arithmetic facts relating the parameters `m = 2h + 2`,
`n = q² / (2m)` and the free parameter `q`, under the divisibility hypothesis `2m ∣ q²`.
They are used in the analytic size estimates for the auxiliary function.

## Main results

* `q_sq_eq_two_mn`: `q ^ 2 = 2 * m * n`.
* `q_sq_le_two_mn`, `q_le_two_mn`: `q ^ 2 ≤ 2 * m * n` and `q ≤ 2 * m * n`.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

@[expose] public section

open NumberField

noncomputable section

namespace GelfondSchneider

variable {K : Type*} [Field K] [NumberField K] (q : ℕ) (h2mq : 2 * m K ∣ q ^ 2)

include h2mq in
lemma q_sq_eq_two_mn : q ^ 2 = 2 * m K * n K q :=
  ((mul_assoc 2 (m K) (n K q)).trans (two_mul_m_mul_n_eq_sq q h2mq)).symm

include h2mq in
lemma q_sq_le_two_mn : q ^ 2 ≤ 2 * m K * n K q := (q_sq_eq_two_mn q h2mq).le

include h2mq in
lemma q_le_two_mn : q ≤ 2 * m K * n K q :=
  (Nat.le_pow Nat.zero_lt_two).trans (q_sq_le_two_mn q h2mq)

end GelfondSchneider
