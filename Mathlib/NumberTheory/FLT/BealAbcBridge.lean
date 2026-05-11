/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.FLT.Beal

/-!
# Bridge: integer Beal counterexample implies high abc-quality

If a primitive integer Beal solution `a^p + b^q = c^r` with `p, q, r ≥ 3`
existed, the associated abc-triple `(a^p, b^q, c^r)` would have quality

  q = log(c^r) / log(radical(a^p · b^q · c^r)) ≥ pqr / (qr + rp + pq).

By Beal hyperbolicity (`qr + rp + pq ≤ pqr`, see `Beal.beal_hyperbolicity`),
this is ≥ 1, putting any Beal solution at the boundary of the abc conjecture.

Together with the abc conjecture (in any explicit form), this would either
exclude Beal counterexamples or bound them.

## Main definitions

* `abcQuality A B C` : log-ratio quantity associated to a triple of natural numbers.

## Main result (drafted, partial proof)

* `beal_solution_implies_abcQuality_bound` : the explicit lower bound on quality
  for a primitive Beal solution.

## Status

`[NUM-EVIDENCE]` This file is a **draft**. The central theorem statement is correct
(verified by hand) but the Lean proof uses `sorry` for the algebraic-inequality
steps that need detailed `nlinarith` / monotonicity machinery. To be filled in
in a follow-up pass.

The MATHEMATICAL bridge — that a Beal counterexample saturates abc — is established;
the FORMAL Lean proof is partial.
-/

@[expose] public section

open UniqueFactorizationMonoid Real

namespace Beal

/-- The abc-quality of a triple `(A, B, C)` of positive naturals.

For an abc-triple (one where `A + B = C` and `gcd(A,B,C) = 1`), the abc
conjecture (Masser-Oesterlé) asserts that for every `ε > 0`, only finitely
many such triples satisfy `abcQuality A B C > 1 + ε`.

The radical and max are computed at the `ℕ` level, then cast to `ℝ` for the log. -/
noncomputable def abcQuality (A B C : ℕ) : ℝ :=
  Real.log ((max A (max B C) : ℕ) : ℝ) / Real.log ((radical (A * B * C) : ℕ) : ℝ)

/-- Helper: under the Beal hypotheses, the prime-power factors are pairwise
coprime, so the radical of their product factors as a product. -/
lemma radical_beal_triple_eq
    {a b c p q r : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (h_pair_ab : Nat.Coprime a b)
    (h_pair_bc : Nat.Coprime b c)
    (h_pair_ca : Nat.Coprime c a) :
    radical (a^p * b^q * c^r) = radical a * radical b * radical c := by
  -- Coprimality lifts to powers
  have hab_pow : Nat.Coprime (a ^ p) (b ^ q) := (h_pair_ab.pow_left p).pow_right q
  have hbc_pow : Nat.Coprime (b ^ q) (c ^ r) := (h_pair_bc.pow_left q).pow_right r
  have hca_pow : Nat.Coprime (c ^ r) (a ^ p) := (h_pair_ca.pow_left r).pow_right p
  -- The product a^p * b^q is coprime to c^r
  have h_apbq_cr : Nat.Coprime (a ^ p * b ^ q) (c ^ r) :=
    Nat.Coprime.mul_left hca_pow.symm hbc_pow
  -- Translate to IsRelPrime over ℕ for radical_mul (works on UFDs)
  have hab_rel : IsRelPrime (a ^ p) (b ^ q) := Nat.coprime_iff_isRelPrime.mp hab_pow
  have h_abc_rel : IsRelPrime (a ^ p * b ^ q) (c ^ r) :=
    Nat.coprime_iff_isRelPrime.mp h_apbq_cr
  -- Compute the radical
  rw [radical_mul h_abc_rel, radical_mul hab_rel,
      radical_pow a hp, radical_pow b hq, radical_pow c hr]

/-- A primitive integer Beal solution gives an abc-triple of explicit quality
bound. Specifically, if `a^p + b^q = c^r` with all `p, q, r ≥ 3`, pairwise coprime
bases, and `a, b, c ≥ 2`, then the abc-quality of `(a^p, b^q, c^r)` is bounded
below by `pqr / (qr + rp + pq)`.

In the Beal-hyperbolicity regime (which holds when `p, q, r ≥ 3`, see
`Beal.beal_hyperbolicity`: `qr + rp + pq ≤ pqr`), the right-hand side is `≥ 1`,
which puts the triple at the abc-conjecture saturation boundary. -/
theorem beal_solution_implies_abcQuality_bound
    {a b c p q r : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h_pair_ab : Nat.Coprime a b)
    (h_pair_bc : Nat.Coprime b c)
    (h_pair_ca : Nat.Coprime c a)
    (heq : a ^ p + b ^ q = c ^ r) :
    abcQuality (a^p) (b^q) (c^r) ≥
      (p * q * r : ℝ) / ((q * r + r * p + p * q) : ℝ) := by
  -- Positivity basics
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have ha_pos : 0 < a := by omega
  have hb_pos : 0 < b := by omega
  have hc_pos : 0 < c := by omega
  -- Step 1: max(a^p, b^q, c^r) = c^r (in ℕ)
  have h_ap_le : a ^ p ≤ c ^ r := by rw [← heq]; exact Nat.le_add_right _ _
  have h_bq_le : b ^ q ≤ c ^ r := by rw [← heq]; exact Nat.le_add_left _ _
  have h_max : max (a^p) (max (b^q) (c^r)) = c^r := by
    rw [max_eq_right h_bq_le, max_eq_right h_ap_le]
  -- Step 2: radical factorisation
  have h_rad_eq : radical (a^p * b^q * c^r) = radical a * radical b * radical c :=
    radical_beal_triple_eq hp_ne hq_ne hr_ne h_pair_ab h_pair_bc h_pair_ca
  -- Step 3: arithmetic chain (a*b*c)^(pqr) ≤ (c^r)^(qr+rp+pq) in ℕ
  have h_ab_pq : (a * b) ^ (p * q) ≤ c ^ (r * (p + q)) := by
    have h_a_pq : a ^ (p * q) ≤ c ^ (r * q) := by
      calc a ^ (p * q) = (a ^ p) ^ q := by ring
        _ ≤ (c ^ r) ^ q := Nat.pow_le_pow_left h_ap_le q
        _ = c ^ (r * q) := by ring
    have h_b_pq : b ^ (p * q) ≤ c ^ (r * p) := by
      calc b ^ (p * q) = (b ^ q) ^ p := by ring
        _ ≤ (c ^ r) ^ p := Nat.pow_le_pow_left h_bq_le p
        _ = c ^ (r * p) := by ring
    calc (a * b) ^ (p * q) = a ^ (p * q) * b ^ (p * q) := by rw [Nat.mul_pow]
      _ ≤ c ^ (r * q) * c ^ (r * p) := Nat.mul_le_mul h_a_pq h_b_pq
      _ = c ^ (r * q + r * p) := by rw [← Nat.pow_add]
      _ = c ^ (r * (p + q)) := by ring_nf
  have h_abc_chain : (a * b * c) ^ (p * q * r) ≤ (c ^ r) ^ (q * r + r * p + p * q) := by
    have h_step : ((a * b) ^ (p * q)) ^ r ≤ (c ^ (r * (p + q))) ^ r :=
      Nat.pow_le_pow_left h_ab_pq r
    calc (a * b * c) ^ (p * q * r)
        = ((a * b) ^ (p * q)) ^ r * c ^ (p * q * r) := by
          rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ (c ^ (r * (p + q))) ^ r * c ^ (p * q * r) :=
          Nat.mul_le_mul_right _ h_step
      _ = c ^ ((r * (p + q)) * r) * c ^ (p * q * r) := by rw [← Nat.pow_mul]
      _ = c ^ ((r * (p + q)) * r + p * q * r) := by rw [← Nat.pow_add]
      _ = c ^ (r * (q * r + r * p + p * q)) := by ring_nf
      _ = (c ^ r) ^ (q * r + r * p + p * q) := by rw [Nat.pow_mul]
  -- Step 4: radical ≤ identity, transferring the chain
  have h_rad_le_abc : radical a * radical b * radical c ≤ a * b * c := by
    have h1 : radical a ≤ a := Nat.le_of_dvd ha_pos radical_dvd_self
    have h2 : radical b ≤ b := Nat.le_of_dvd hb_pos radical_dvd_self
    have h3 : radical c ≤ c := Nat.le_of_dvd hc_pos radical_dvd_self
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have h_rad_pow_le : (radical a * radical b * radical c) ^ (p * q * r) ≤
      (c ^ r) ^ (q * r + r * p + p * q) :=
    le_trans (Nat.pow_le_pow_left h_rad_le_abc _) h_abc_chain
  -- Step 5: positivity for the log step
  have h_rad_a_ge : 2 ≤ radical a := Nat.two_le_radical_iff.mpr ha
  have h_rad_b_ge : 2 ≤ radical b := Nat.two_le_radical_iff.mpr hb
  have h_rad_c_ge : 2 ≤ radical c := Nat.two_le_radical_iff.mpr hc
  have h_rad_prod_ge : 2 ≤ radical a * radical b * radical c := by
    have := Nat.mul_le_mul (Nat.mul_le_mul h_rad_a_ge h_rad_b_ge) h_rad_c_ge
    linarith
  have h_rad_prod_pos_R : (0 : ℝ) < ((radical a * radical b * radical c : ℕ) : ℝ) := by
    have : (0 : ℕ) < radical a * radical b * radical c := by linarith
    exact_mod_cast this
  have h_rad_prod_one_lt_R :
      (1 : ℝ) < ((radical a * radical b * radical c : ℕ) : ℝ) := by
    have : (1 : ℕ) < radical a * radical b * radical c := by linarith
    exact_mod_cast this
  have h_log_rad_pos : 0 < Real.log ((radical a * radical b * radical c : ℕ) : ℝ) :=
    Real.log_pos h_rad_prod_one_lt_R
  -- Step 6: cast the ℕ inequality to ℝ, take log
  have h_cast : ((radical a * radical b * radical c : ℕ) : ℝ) ^ (p * q * r) ≤
      ((c ^ r : ℕ) : ℝ) ^ (q * r + r * p + p * q) := by
    exact_mod_cast h_rad_pow_le
  have h_lhs_pos : (0 : ℝ) <
      ((radical a * radical b * radical c : ℕ) : ℝ) ^ (p * q * r) :=
    pow_pos h_rad_prod_pos_R _
  have h_log_le : Real.log (((radical a * radical b * radical c : ℕ) : ℝ) ^ (p * q * r)) ≤
      Real.log (((c ^ r : ℕ) : ℝ) ^ (q * r + r * p + p * q)) :=
    Real.log_le_log h_lhs_pos h_cast
  rw [Real.log_pow, Real.log_pow] at h_log_le
  -- Step 7: positivity for the denominator on the RHS, in Real form
  have h_sum_pos : (0 : ℝ) < (q : ℝ) * r + r * p + p * q := by
    have h_q_pos_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
    have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast hr_pos
    have h_p_pos_R : (0 : ℝ) < p := by exact_mod_cast hp_pos
    positivity
  -- Step 8: unfold abcQuality, simplify casts, divide
  unfold abcQuality
  rw [h_max, h_rad_eq]
  push_cast
  push_cast at h_log_le h_log_rad_pos
  rw [ge_iff_le, div_le_div_iff₀ h_sum_pos h_log_rad_pos]
  linarith [h_log_le]

/-- The looser corollary: Beal solutions have abc-quality `≥ 1`. -/
theorem beal_solution_implies_abcQuality_geq_one
    {a b c p q r : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h_pair_ab : Nat.Coprime a b)
    (h_pair_bc : Nat.Coprime b c)
    (h_pair_ca : Nat.Coprime c a)
    (heq : a ^ p + b ^ q = c ^ r) :
    abcQuality (a^p) (b^q) (c^r) ≥ 1 := by
  -- Reduce to the explicit bound + Beal hyperbolicity inequality.
  -- The chain is: abcQuality ≥ pqr/(qr+rp+pq) ≥ 1, the second by hyperbolicity.
  have h_bound := beal_solution_implies_abcQuality_bound hp hq hr ha hb hc
    h_pair_ab h_pair_bc h_pair_ca heq
  have h_hyp : q * r + r * p + p * q ≤ p * q * r := beal_hyperbolicity hp hq hr
  have h_pos : (0 : ℝ) < (q * r + r * p + p * q) := by
    have h_p_pos : 0 < p := by omega
    have h_q_pos : 0 < q := by omega
    have h_r_pos : 0 < r := by omega
    have : 0 < q * r + r * p + p * q := by positivity
    exact_mod_cast this
  have h_ratio_ge_one : (1 : ℝ) ≤ (p * q * r : ℝ) / (q * r + r * p + p * q) := by
    rw [le_div_iff₀ h_pos]
    rw [one_mul]
    exact_mod_cast h_hyp
  linarith [h_bound, h_ratio_ge_one]

-- Note (no theorem): the strong abc conjecture, applied to the bound above,
-- would imply Beal asymptotically (counterexamples bounded; for sufficiently
-- large exponents, excluded). abc is conjectural so this is not a theorem
-- we state in Lean; the implication is mathematical folklore.

end Beal
