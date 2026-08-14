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
They are used when bounding the order of vanishing of the auxiliary function.

## Main results

* `q_sq_eq_two_mn`: `q ^ 2 = 2 * m * n`.
* `m_mul_n_pos`: `0 < m * n`.
* `m_mul_n_lt_q_mul_q`: `m * n < q * q`, so the linear system is underdetermined.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

namespace GelfondSchneider

variable {K : Type} [Field K] [NumberField K] (q : ℕ) (hq0 : 0 < q) (h2mq : 2 * m K ∣ q ^ 2)

include h2mq in
lemma q_sq_eq_two_mn : q ^ 2 = 2 * m K * n K q := Eq.symm (Nat.mul_div_cancel' h2mq)

include hq0 h2mq in
lemma m_mul_n_pos : 0 < m K * n K q :=
  Nat.mul_pos (one_le_m K) <| by simpa [n, Nat.div_pos_iff] using
    ⟨Nat.zero_lt_succ (2 * h K + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩

include hq0 h2mq in
lemma m_mul_n_lt_q_mul_q : m K * n K q < q * q :=
  lt_of_lt_of_eq (by grind [m_mul_n_pos q hq0 h2mq]) <|
  (q_sq_eq_two_mn q h2mq).symm.trans (pow_two q)

end GelfondSchneider
