/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Positivity of pair-difference sums of an antitone null sequence

For an antitone sequence `u : ℕ → ℝ` tending to `0`, the consecutive pair
differences `u (2k) - u (2k + 1)` are nonnegative, their partial sums are
the even partial sums of the alternating series `∑ (-1)^i u i`, and the
pair-difference sum is positive as soon as the first pair is strict.

The motivating instance is the Dirichlet eta series: for `σ > 0`, the
pair sum of `(n + 1) ^ (-σ)` is positive. This is the elementary
combinatorial core of the classical Siegel zero-repulsion argument.
-/

public section

open Filter Finset

/-- For an antitone sequence `u : ℕ → ℝ` tending to `0` whose first pair
is strict (`u 1 < u 0`), the sum of the consecutive pair differences
`u (2k) - u (2k + 1)` is positive. -/
theorem Antitone.tsum_pair_sub_pos {u : ℕ → ℝ} (hu : Antitone u)
    (hu0 : Tendsto u atTop (nhds 0)) (h01 : u 1 < u 0) :
    0 < ∑' k : ℕ, (u (2 * k) - u (2 * k + 1)) := by
  have hpair_nn : ∀ k, 0 ≤ u (2 * k) - u (2 * k + 1) :=
    fun k => sub_nonneg.mpr (hu (by omega))
  have hpair_partial : ∀ k : ℕ,
      ∑ j ∈ Finset.range k, (u (2 * j) - u (2 * j + 1)) =
      ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * u i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring,
          Finset.sum_range_succ (f := fun j => u (2 * j) - u (2 * j + 1)),
          Finset.sum_range_succ (f := fun i => (-1 : ℝ) ^ i * u i) (n := 2 * k + 1),
          Finset.sum_range_succ (f := fun i => (-1 : ℝ) ^ i * u i) (n := 2 * k), ← ih]
      have h1 : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
      have h2 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, h1]; ring
      simp only [h1, h2]; ring
  obtain ⟨l, hl⟩ := hu.tendsto_alternating_series_of_tendsto_zero hu0
  have hl_pair : Tendsto (fun k => ∑ j ∈ Finset.range k, (u (2 * j) - u (2 * j + 1)))
      atTop (nhds l) := by
    simp_rw [hpair_partial]
    exact hl.comp (tendsto_atTop_atTop.mpr fun n => ⟨n, fun k hk => by omega⟩)
  have hg_hs : HasSum (fun k => u (2 * k) - u (2 * k + 1)) l :=
    (hasSum_iff_tendsto_nat_of_nonneg hpair_nn l).mpr hl_pair
  exact hg_hs.tsum_eq ▸ hg_hs.summable.tsum_pos hpair_nn 0 (by simpa using sub_pos.mpr h01)

namespace SiegelElementary

open Real

/-- The eta term `(n + 1) ^ (-σ)`. -/
noncomputable def etaTerm (σ : ℝ) (n : ℕ) : ℝ := (n + 1 : ℝ) ^ (-σ)

/-- `(n+1)^(-σ)` is antitone in `n` for `σ > 0`. -/
lemma eta_antitone (σ : ℝ) (hσ : 0 < σ) : Antitone (etaTerm σ) := by
  intro m n hmn
  simp only [etaTerm]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  rw [Real.rpow_neg (le_of_lt hm), Real.rpow_neg (le_of_lt hn)]
  exact inv_anti₀ (Real.rpow_pos_of_pos hm σ)
    (Real.rpow_le_rpow (le_of_lt hm) hmn' (le_of_lt hσ))

/-- `(n+1)^(-σ) → 0` for `σ > 0`. -/
lemma eta_tends_zero (σ : ℝ) (hσ : 0 < σ) : Tendsto (etaTerm σ) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) atTop (nhds 0)
  exact (tendsto_rpow_neg_atTop hσ).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- Consecutive pair difference of eta terms:
`η₂ₖ − η₂ₖ₊₁ = (2k+1)^{−σ} − (2k+2)^{−σ}`. -/
noncomputable def etaPair (σ : ℝ) (k : ℕ) : ℝ :=
  etaTerm σ (2 * k) - etaTerm σ (2 * k + 1)

private lemma one_sub_half_pow_pos (σ : ℝ) (hσ : 0 < σ) : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by
  have h : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

private lemma etaPair_zero_pos (σ : ℝ) (hσ : 0 < σ) : 0 < etaPair σ 0 := by
  have h1 : etaTerm σ 0 = 1 := by simp [etaTerm, Real.one_rpow]
  have h2 : etaTerm σ 1 = (2 : ℝ) ^ (-σ) := by
    simp only [etaTerm, Nat.cast_one]; norm_num
  simp only [etaPair, mul_zero, zero_add, h1, h2]
  exact one_sub_half_pow_pos σ hσ

/-- The tsum of consecutive pair differences of the eta series is positive
for all `σ > 0`: the verified combinatorial core of the Siegel
zero-repulsion argument, as the `etaTerm` instance of
`Antitone.tsum_pair_sub_pos`. -/
theorem eta_pos (σ : ℝ) (hσ : 0 < σ) : 0 < ∑' k : ℕ, etaPair σ k := by
  apply Antitone.tsum_pair_sub_pos (eta_antitone σ hσ) (eta_tends_zero σ hσ)
  exact sub_pos.mp (by simpa only [etaPair, mul_zero, zero_add] using etaPair_zero_pos σ hσ)

end SiegelElementary
