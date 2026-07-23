/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus using Claude Code
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Borel Growth Lemma

This file proves Émile Borel's **Growth Lemma**: if `S : ℝ → ℝ` is monotone on `Set.Ici a` and
satisfies `1 ≤ S` there, then

`∀ᶠ r in volume.cofinite ⊓ atTop, S (r + (S r)⁻¹) ≤ 2 * S r`.

In other words: The inequality `S (r + (S r)⁻¹) ≤ 2 * S r` holds for all sufficiently large `r`
outside an exceptional set `E` of finite Lebesgue measure. In Value Distribution Theory, this
statement is central to the proof of the "Lemma on the Logarithmic Derivatives".

The proof here is simpler than the argument typically found in textbooks and does not make any
regularity assumption on `S`. It slices the exceptional set `E` into the dyadic pieces

`Eₙ = {r ∈ E | 2 ^ n * S a ≤ S r < 2 ^ (n + 1) * S a}`.

If `x ≤ y` both lie in `Eₙ`, then there are inequalities

`S (x + (S x)⁻¹) > 2 * S x ≥ 2 ^ (n + 1) * S a > S y`.

Monotonicity will then force `y - x < (S x)⁻¹ ≤ 2⁻ⁿ`.  As a consequence, each slice has diameter at
most `2⁻ⁿ`, so that `volume E` is bounded by `∑ 2⁻ⁿ = 2 < ∞`.

## References

- Lemma 2.4 in [Hayman, *Meromorphic functions*][MR164038].

- Lemma 3.7 in Section VI.3 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677]
-/

@[expose] public section

open Filter MeasureTheory Set

/--
**Borel's Growth Lemma**: if `S : ℝ → ℝ` is monotone on `Set.Ici a` and satisfies `1 ≤ S` there,
then the inequality `S (r + (S r)⁻¹) ≤ 2 * S r` holds for all sufficiently large `r` outside a set
of finite Lebesgue measure.
-/
theorem MonotoneOn.eventually_le_two_mul {S : ℝ → ℝ} {a : ℝ}
    (h₁ : MonotoneOn S (Set.Ici a)) (h₂ : ∀ r ∈ Set.Ici a, 1 ≤ S r) :
    ∀ᶠ r in volume.cofinite ⊓ atTop, S (r + (S r)⁻¹) ≤ 2 * S r := by
  classical
  -- The exceptional set `E` and its dyadic slices `En n`
  set E := {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹)} with hE_def
  set En := fun n ↦ {r ∈ E | 2 ^ n * S a ≤ S r ∧ S r < 2 ^ (n + 1) * S a}
    with hEn_def
  have hSa : 0 < S a := zero_lt_one.trans_le (h₂ a self_mem_Ici)
  have hS_pos : ∀ r ∈ Ici a, 0 < S r := fun r hr ↦ zero_lt_one.trans_le (h₂ r hr)
  -- The slices cover `E`
  have hcov : E ⊆ ⋃ n, En n := by
    intro r hr
    have h₃ : S a ≤ S r := h₁ self_mem_Ici hr.1 hr.1
    have h₄ : ∃ n : ℕ, S r < 2 ^ (n + 1) * S a := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (S r / S a) one_lt_two
      exact ⟨n, ((div_lt_iff₀ hSa).1 hn).trans_le
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two n.le_succ) hSa.le)⟩
    refine mem_iUnion.2 ⟨Nat.find h₄, hr, ?_, Nat.find_spec h₄⟩
    rcases Nat.eq_zero_or_pos (Nat.find h₄) with h₅ | h₅
    · simpa [h₅] using h₃
    · have h₆ := Nat.find_min h₄ (Nat.sub_lt h₅ one_pos)
      rw [show Nat.find h₄ - 1 + 1 = Nat.find h₄ by omega] at h₆
      exact not_lt.1 h₆
  -- Two points of a slice are at distance at most `(2 ^ n)⁻¹`
  have hkey : ∀ n, ∀ x ∈ En n, ∀ y ∈ En n, x ≤ y → y - x ≤ (2 ^ n)⁻¹ := by
    intro n x hx y hy hxy
    obtain ⟨⟨h₁x, h₂x⟩, h₃x, -⟩ := hx
    obtain ⟨⟨h₁y, -⟩, -, h₄y⟩ := hy
    -- `y` lies strictly below `x + (S x)⁻¹`…
    have h₆ : y < x + (S x)⁻¹ := by
      by_contra h₆
      have h₇ : S (x + (S x)⁻¹) ≤ S y := by
        apply h₁ _ h₁y (not_lt.1 h₆)
        exact mem_Ici.2 (h₁x.trans (le_add_of_nonneg_right (inv_nonneg.2 (hS_pos x h₁x).le)))
      have h₈ : (2 : ℝ) ^ (n + 1) * S a = 2 * (2 ^ n * S a) := by ring
      linarith
    -- …and `(S x)⁻¹` is at most `(2 ^ n)⁻¹`
    have h₇ : (S x)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
      gcongr
      exact le_trans (le_mul_of_one_le_right (by positivity) (h₂ a self_mem_Ici)) h₃x
    linarith
  -- Hence each slice has diameter at most `(2 ^ n)⁻¹`…
  have hdiam : ∀ n : ℕ, Metric.ediam (En n) ≤ ENNReal.ofReal ((2 ^ n)⁻¹) := by
    intro n
    apply Metric.ediam_le
    intro x hx y hy
    rw [edist_le_ofReal (by positivity)]
    rcases le_total x y with h | h
    · rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      exact hkey n x hx y hy h
    · rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      exact hkey n y hy x hx h
  -- …and `E` has finite volume
  have hvol : volume E < ⊤ := by
    have hsum : Summable fun n ↦ ((2 : ℝ) ^ n)⁻¹ := by
      simpa only [inv_pow] using
        summable_geometric_of_lt_one (r := 2⁻¹) (by norm_num) (by norm_num)
    have h₃ : ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) = ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun n ↦ ((2 : ℝ) ^ n)⁻¹)
        (fun n ↦ by positivity) hsum]
      congr 1
      simp only [← inv_pow]
      exact tsum_geometric_inv_two
    calc volume E
        ≤ ∑' n, volume (En n) := le_trans (measure_mono hcov) (measure_iUnion_le En)
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) :=
          ENNReal.tsum_le_tsum fun n ↦ le_trans (Real.volume_le_diam (En n)) (hdiam n)
      _ = ENNReal.ofReal 2 := h₃
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- Conclusion
  have hEc : Eᶜ ∈ volume.cofinite := by
    rw [Measure.mem_cofinite, compl_compl]
    exact hvol
  filter_upwards [mem_inf_of_left hEc, mem_inf_of_right (eventually_ge_atTop a)]
    with r h₃r h₄r
  by_contra h₅
  exact h₃r ⟨h₄r, not_le.1 h₅⟩
