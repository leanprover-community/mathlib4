/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Units
import Mathlib.Data.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Basic

#align_import number_theory.diophantine_approximation from "leanprover-community/mathlib"@"e25a317463bd37d88e33da164465d8c47922b1cd"

/-!
# Diophantine Approximation

The first part of this file gives proofs of various versions of
**Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2} \,.$$
The proof is based on the pigeonhole principle.

The second part of the file gives a proof of **Legendre's Theorem** on rational approximation,
which states that if $\xi$ is a real number and $x/y$ is a rational number such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{2y^2} \,,$$
then $x/y$ must be a convergent of the continued fraction expansion of $\xi$.

## Main statements

The main results are three variants of Dirichlet's approximation theorem:
* `Real.exists_int_int_abs_mul_sub_le`, which states that for all real `ξ` and natural `0 < n`,
  there are integers `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `Real.exists_nat_abs_mul_sub_round_le`, which replaces `j` by `round(k*ξ)` and uses
  a natural number `k`,
* `Real.exists_rat_abs_sub_le_and_den_le`, which says that there is a rational number `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.den)` and `q.den ≤ n`,

and
* `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, which states that
  for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.den^2}` is infinite.

We also show a converse,
* `Rat.finite_rat_abs_sub_lt_one_div_den_sq`, which states that the set above is finite
  when `ξ` is a rational number.

Both statements are combined to give an equivalence,
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.

There are two versions of Legendre's Theorem. One, `Real.exists_rat_eq_convergent`, uses
`Real.convergent`, a simple recursive definition of the convergents that is also defined
in this file, whereas the other, `Real.exists_continued_fraction_convergent_eq_rat`, uses
`GeneralizedContinuedFraction.convergents` of `GeneralizedContinuedFraction.of ξ`.

## Implementation notes

We use the namespace `Real` for the results on real numbers and `Rat` for the results
on rational numbers. We introduce a secondary namespace `real.contfrac_legendre`
to separate off a definition and some technical auxiliary lemmas used in the proof
of Legendre's Theorem. For remarks on the proof of Legendre's Theorem, see below.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>
<https://de.wikipedia.org/wiki/Kettenbruch> (The German Wikipedia page on continued
fractions is much more extensive than the English one.)

## Tags

Diophantine approximation, Dirichlet's approximation theorem, continued fraction
-/


namespace Real

section Dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.
-/


open Finset Int

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`,
with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`.

See also `Real.exists_nat_abs_mul_sub_round_le`. -/
theorem exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1) := by
  let f : ℤ → ℤ := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |↑k * ξ - ↑j| ≤ 1 / (↑n + 1)
  have hn : 0 < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos _
  -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |↑k * ξ - ↑j| ≤ 1 / (↑n + 1)
  have hfu := fun m : ℤ => mul_lt_of_lt_one_left hn <| fract_lt_one (ξ * ↑m)
  -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |↑k * ξ - ↑j| ≤ 1 / (↑n + 1)
  conv in |_| ≤ _ => rw [mul_comm, le_div_iff hn, ← abs_of_pos hn, ← abs_mul]
  -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
  let D := Icc (0 : ℤ) n
  -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
  by_cases H : ∃ m ∈ D, f m = n
  -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
  · obtain ⟨m, hm, hf⟩ := H
    -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
    have hf' : ((n : ℤ) : ℝ) ≤ fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        -- Porting note: was
        -- simp only [floor_eq_zero_iff, algebraMap.coe_zero, mul_zero, fract_zero,
        --   zero_mul, Set.left_mem_Ico, zero_lt_one]
        simp only [cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine' Ne.lt_of_le (fun h => n_pos.ne _) (mem_Icc.mp hm).1
      exact_mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine' ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, _⟩
    -- ⊢ |(ξ * ↑m - ↑(⌊ξ * ↑m⌋ + 1)) * (↑n + 1)| ≤ 1
    rw [cast_add, ← sub_sub, sub_mul, cast_one, one_mul, abs_le]
    -- ⊢ -1 ≤ (ξ * ↑m - ↑⌊ξ * ↑m⌋) * (↑n + 1) - (↑n + 1) ∧ (ξ * ↑m - ↑⌊ξ * ↑m⌋) * (↑n …
    refine'
      ⟨le_sub_iff_add_le.mpr _, sub_le_iff_le_add.mpr <| le_of_lt <| (hfu m).trans <| lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using hf'
    -- 🎉 no goals
  · -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5127): added `not_and`
    simp_rw [not_exists, not_and] at H
    -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
    have hD : (Ico (0 : ℤ) n).card < D.card := by rw [card_Icc, card_Ico]; exact lt_add_one n
    -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
    have hfu' : ∀ m, f m ≤ n := fun m => lt_add_one_iff.mp (floor_lt.mpr (by exact_mod_cast hfu m))
    -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    have : ∃ (x : ℤ) (_ : x ∈ D) (y : ℤ) (_ : y ∈ D), x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ := this
    -- ⊢ ∃ j k, 0 < k ∧ k ≤ ↑n ∧ |(ξ * ↑k - ↑j) * (↑n + 1)| ≤ 1
    refine'
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
        sub_le_iff_le_add.mpr <| le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, _⟩
    convert_to |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1
    -- ⊢ |(ξ * ↑(y - x) - ↑(⌊ξ * ↑y⌋ - ⌊ξ * ↑x⌋)) * (↑n + 1)| = |fract (ξ * ↑y) * (↑n …
    · congr; push_cast; simp only [fract]; ring
      -- ⊢ (ξ * ↑(y - x) - ↑(⌊ξ * ↑y⌋ - ⌊ξ * ↑x⌋)) * (↑n + 1) = fract (ξ * ↑y) * (↑n +  …
             -- ⊢ (ξ * (↑y - ↑x) - (↑⌊ξ * ↑y⌋ - ↑⌊ξ * ↑x⌋)) * (↑n + 1) = fract (ξ * ↑y) * (↑n  …
                        -- ⊢ (ξ * (↑y - ↑x) - (↑⌊ξ * ↑y⌋ - ↑⌊ξ * ↑x⌋)) * (↑n + 1) = (ξ * ↑y - ↑⌊ξ * ↑y⌋)  …
                                           -- 🎉 no goals
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le
    -- 🎉 no goals
#align real.exists_int_int_abs_mul_sub_le Real.exists_int_int_abs_mul_sub_le

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a natural number `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
theorem exists_nat_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  -- ⊢ ∃ k, 0 < k ∧ k ≤ n ∧ |↑k * ξ - ↑(round (↑k * ξ))| ≤ 1 / (↑n + 1)
  have hk := toNat_of_nonneg hk₀.le
  -- ⊢ ∃ k, 0 < k ∧ k ≤ n ∧ |↑k * ξ - ↑(round (↑k * ξ))| ≤ 1 / (↑n + 1)
  rw [← hk] at hk₀ hk₁ h
  -- ⊢ ∃ k, 0 < k ∧ k ≤ n ∧ |↑k * ξ - ↑(round (↑k * ξ))| ≤ 1 / (↑n + 1)
  exact ⟨k.toNat, coe_nat_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩
  -- 🎉 no goals
#align real.exists_nat_abs_mul_sub_round_le Real.exists_nat_abs_mul_sub_round_le

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.

See also `AddCircle.exists_norm_nsmul_le`. -/
theorem exists_rat_abs_sub_le_and_den_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.den) ∧ q.den ≤ n := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  -- ⊢ ∃ q, |ξ - ↑q| ≤ 1 / ((↑n + 1) * ↑q.den) ∧ q.den ≤ n
  have hk₀' : (0 : ℝ) < k := Int.cast_pos.mpr hk₀
  -- ⊢ ∃ q, |ξ - ↑q| ≤ 1 / ((↑n + 1) * ↑q.den) ∧ q.den ≤ n
  have hden : ((j / k : ℚ).den : ℤ) ≤ k := by
    convert le_of_dvd hk₀ (Rat.den_dvd j k)
    exact Rat.coe_int_div_eq_divInt
  refine' ⟨j / k, _, Nat.cast_le.mp (hden.trans hk₁)⟩
  -- ⊢ |ξ - ↑(↑j / ↑k)| ≤ 1 / ((↑n + 1) * ↑(↑j / ↑k).den)
  rw [← div_div, le_div_iff (Nat.cast_pos.mpr <| Rat.pos _ : (0 : ℝ) < _)]
  -- ⊢ |ξ - ↑(↑j / ↑k)| * ↑(↑j / ↑k).den ≤ 1 / (↑n + 1)
  refine' (mul_le_mul_of_nonneg_left (Int.cast_le.mpr hden : _ ≤ (k : ℝ)) (abs_nonneg _)).trans _
  -- ⊢ |ξ - ↑(↑j / ↑k)| * ↑k ≤ 1 / (↑n + 1)
  rwa [← abs_of_pos hk₀', Rat.cast_div, Rat.cast_coe_int, Rat.cast_coe_int, ← abs_mul, sub_mul,
    div_mul_cancel _ hk₀'.ne', mul_comm]
#align real.exists_rat_abs_sub_le_and_denom_le Real.exists_rat_abs_sub_le_and_den_le

end Dirichlet

section RatApprox

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/


open Set

/-- Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`. -/
theorem exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : ℝ} (hξ : Irrational ξ) (q : ℚ) :
    ∃ q' : ℚ, |ξ - q'| < 1 / (q'.den : ℝ) ^ 2 ∧ |ξ - q'| < |ξ - q| := by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  -- ⊢ ∃ q', |ξ - ↑q'| < 1 / ↑q'.den ^ 2 ∧ |ξ - ↑q'| < |ξ - ↑q|
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  -- ⊢ ∃ q', |ξ - ↑q'| < 1 / ↑q'.den ^ 2 ∧ |ξ - ↑q'| < |ξ - ↑q|
  have m_pos : (0 : ℝ) < m := (one_div_pos.mpr h).trans hm
  -- ⊢ ∃ q', |ξ - ↑q'| < 1 / ↑q'.den ^ 2 ∧ |ξ - ↑q'| < |ξ - ↑q|
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  -- ⊢ ∃ q', |ξ - ↑q'| < 1 / ↑q'.den ^ 2 ∧ |ξ - ↑q'| < |ξ - ↑q|
  have den_pos : (0 : ℝ) < q'.den := Nat.cast_pos.mpr q'.pos
  -- ⊢ ∃ q', |ξ - ↑q'| < 1 / ↑q'.den ^ 2 ∧ |ξ - ↑q'| < |ξ - ↑q|
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  -- ⊢ ∃ q', |ξ - ↑q'| < 1 / ↑q'.den ^ 2 ∧ |ξ - ↑q'| < |ξ - ↑q|
  refine'
    ⟨q', lt_of_le_of_lt hbd _,
      lt_of_le_of_lt hbd <|
        (one_div_lt md_pos h).mpr <|
          hm.trans <|
            lt_of_lt_of_le (lt_add_one _) <|
              (le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr <| by
                exact_mod_cast (q'.pos : 1 ≤ q'.den)⟩
  rw [sq, one_div_lt_one_div md_pos (mul_pos den_pos den_pos), mul_lt_mul_right den_pos]
  -- ⊢ ↑q'.den < ↑m + 1
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one
  -- 🎉 no goals
#align real.exists_rat_abs_sub_lt_and_lt_of_irrational Real.exists_rat_abs_sub_lt_and_lt_of_irrational

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : ℝ} (hξ : Irrational ξ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  refine' Or.resolve_left (Set.finite_or_infinite _) fun h => _
  -- ⊢ False
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  -- ⊢ False
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)
  -- 🎉 no goals
#align real.infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational

end RatApprox

end Real

namespace Rat

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/


open Set

/-- If `ξ` is rational, then the good rational approximations to `ξ` have bounded
numerator and denominator. -/
theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : ℚ}
    (h : |ξ - q| < 1 / (q.den : ℚ) ^ 2) :
    q.den ≤ ξ.den ∧ ⌈ξ * q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * q.den⌋ + 1 := by
  have hq₀ : (0 : ℚ) < q.den := Nat.cast_pos.mpr q.pos
  -- ⊢ q.den ≤ ξ.den ∧ ⌈ξ * ↑q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * ↑q.den⌋ + 1
  replace h : |ξ * q.den - q.num| < 1 / q.den
  -- ⊢ |ξ * ↑q.den - ↑q.num| < 1 / ↑q.den
  · rw [← mul_lt_mul_right hq₀] at h
    -- ⊢ |ξ * ↑q.den - ↑q.num| < 1 / ↑q.den
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    -- ⊢ |ξ * ↑q.den - ↑q.num| < 1 / ↑q.den
    rwa [sq, div_mul, mul_div_cancel_left _ hq₀.ne'] at h
    -- 🎉 no goals
  constructor
  -- ⊢ q.den ≤ ξ.den
  · rcases eq_or_ne ξ q with (rfl | H)
    -- ⊢ ξ.den ≤ ξ.den
    · exact le_rfl
      -- 🎉 no goals
    · have hξ₀ : (0 : ℚ) < ξ.den := Nat.cast_pos.mpr ξ.pos
      -- ⊢ q.den ≤ ξ.den
      rw [← Rat.num_div_den ξ, div_mul_eq_mul_div, div_sub' _ _ _ hξ₀.ne', abs_div, abs_of_pos hξ₀,
        div_lt_iff hξ₀, div_mul_comm, mul_one] at h
      refine' Nat.cast_le.mp ((one_lt_div hq₀).mp <| lt_of_le_of_lt _ h).le
      -- ⊢ 1 ≤ |↑ξ.num * ↑q.den - ↑ξ.den * ↑q.num|
      norm_cast
      -- ⊢ 1 ≤ |ξ.num * ↑q.den - ↑ξ.den * q.num|
      rw [mul_comm _ q.num]
      -- ⊢ 1 ≤ |ξ.num * ↑q.den - q.num * ↑ξ.den|
      exact Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
      -- 🎉 no goals
  · obtain ⟨h₁, h₂⟩ :=
      abs_sub_lt_iff.mp
        (h.trans_le <|
          (one_div_le zero_lt_one hq₀).mp <| (@one_div_one ℚ _).symm ▸ Nat.cast_le.mpr q.pos)
    rw [sub_lt_iff_lt_add, add_comm] at h₁ h₂
    -- ⊢ ⌈ξ * ↑q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * ↑q.den⌋ + 1
    rw [← sub_lt_iff_lt_add] at h₂
    -- ⊢ ⌈ξ * ↑q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * ↑q.den⌋ + 1
    norm_cast at h₁ h₂
    -- ⊢ ⌈ξ * ↑q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * ↑q.den⌋ + 1
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩
#align rat.denom_le_and_le_num_le_of_sub_lt_one_div_denom_sq Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq

/-- A rational number has only finitely many good rational approximations. -/
theorem finite_rat_abs_sub_lt_one_div_den_sq (ξ : ℚ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}.Finite := by
  let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  -- ⊢ Set.Finite {q | |ξ - q| < 1 / ↑q.den ^ 2}
  set s := {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}
  -- ⊢ Set.Finite s
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [Prod.mk.inj_iff] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  have H : f '' s ⊆ ⋃ (y : ℕ) (_ : y ∈ Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image, mem_setOf] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine' ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, _⟩
    simp only [prod_singleton, mem_image, mem_Icc, (congr_arg Prod.snd (Eq.symm hq₂)).trans rfl]
    exact ⟨q.num, hn, hq₂⟩
  refine' Finite.of_finite_image (Finite.subset _ H) (injOn_of_injective hinj s)
  -- ⊢ Set.Finite (⋃ (y : ℕ) (_ : y ∈ Ioc 0 ξ.den), Icc (⌈ξ * ↑y⌉ - 1) (⌊ξ * ↑y⌋ +  …
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)
  -- 🎉 no goals
#align rat.finite_rat_abs_sub_lt_one_div_denom_sq Rat.finite_rat_abs_sub_lt_one_div_den_sq

end Rat

/-- The set of good rational approximations to a real number `ξ` is infinite if and only if
`ξ` is irrational. -/
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : ℝ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite ↔ Irrational ξ := by
  refine'
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b H => Set.not_infinite.mpr _ h,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  convert Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : ℚ) / b) with q
  -- ⊢ |ξ - ↑q| < 1 / ↑q.den ^ 2 ↔ |↑a / ↑b - q| < 1 / ↑q.den ^ 2
  rw [H, (by (push_cast; rfl) : (1 : ℝ) / (q.den : ℝ) ^ 2 = (1 / (q.den : ℚ) ^ 2 : ℚ))]
  -- ⊢ |↑a / ↑b - ↑q| < ↑(1 / ↑q.den ^ 2) ↔ |↑a / ↑b - q| < 1 / ↑q.den ^ 2
  norm_cast
  -- 🎉 no goals
#align real.infinite_rat_abs_sub_lt_one_div_denom_sq_iff_irrational Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational

/-!
### Legendre's Theorem on Rational Approximation

We prove **Legendre's Theorem** on rational approximation: If $\xi$ is a real number and
$x/y$ is a rational number such that $|\xi - x/y| < 1/(2y^2)$,
then $x/y$ is a convergent of the continued fraction expansion of $\xi$.

The proof is by induction. However, the induction proof does not work with the
statement as given, since the assumption is too weak to imply the corresponding
statement for the application of the induction hypothesis. This can be remedied
by making the statement slightly stronger. Namely, we assume that $|\xi - x/y| < 1/(y(2y-1))$
when $y \ge 2$ and $-\frac{1}{2} < \xi - x < 1$ when $y = 1$.
-/


section Convergent

namespace Real

open Int

/-!
### Convergents: definition and API lemmas
-/


/-- We give a direct recursive definition of the convergents of the continued fraction
expansion of a real number `ξ`. The main reason for that is that we want to have the
convergents as rational numbers; the versions
`(GeneralizedContinuedFraction.of ξ).convergents` and
`(GeneralizedContinuedFraction.of ξ).convergents'` always give something of the
same type as `ξ`. We can then also use dot notation `ξ.convergent n`.
Another minor reason is that this demonstrates that the proof
of Legendre's theorem does not need anything beyond this definition.
We provide a proof that this definition agrees with the other one;
see `Real.continued_fraction_convergent_eq_convergent`.
(Note that we use the fact that `1/0 = 0` here to make it work for rational `ξ`.) -/
noncomputable def convergent : ℝ → ℕ → ℚ
  | ξ, 0 => ⌊ξ⌋
  | ξ, n + 1 => ⌊ξ⌋ + (convergent (fract ξ)⁻¹ n)⁻¹
#align real.convergent Real.convergent

/-- The zeroth convergent of `ξ` is `⌊ξ⌋`. -/
@[simp]
theorem convergent_zero (ξ : ℝ) : ξ.convergent 0 = ⌊ξ⌋ :=
  rfl
#align real.convergent_zero Real.convergent_zero

/-- The `(n+1)`th convergent of `ξ` is the `n`th convergent of `1/(fract ξ)`. -/
@[simp]
theorem convergent_succ (ξ : ℝ) (n : ℕ) :
    ξ.convergent (n + 1) = ⌊ξ⌋ + ((fract ξ)⁻¹.convergent n)⁻¹ :=
  -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5026): was
  -- by simp only [convergent]
  rfl
#align real.convergent_succ Real.convergent_succ

/-- All convergents of `0` are zero. -/
@[simp]
theorem convergent_of_zero (n : ℕ) : convergent 0 n = 0 := by
  induction' n with n ih
  -- ⊢ convergent 0 Nat.zero = 0
  · simp only [Nat.zero_eq, convergent_zero, floor_zero, cast_zero]
    -- 🎉 no goals
  · simp only [ih, convergent_succ, floor_zero, cast_zero, fract_zero, add_zero, inv_zero]
    -- 🎉 no goals
#align real.convergent_of_zero Real.convergent_of_zero

/-- If `ξ` is an integer, all its convergents equal `ξ`. -/
@[simp]
theorem convergent_of_int {ξ : ℤ} (n : ℕ) : convergent ξ n = ξ := by
  cases n
  -- ⊢ convergent (↑ξ) Nat.zero = ↑ξ
  · simp only [Nat.zero_eq, convergent_zero, floor_intCast]
    -- 🎉 no goals
  · simp only [convergent_succ, floor_intCast, fract_intCast, convergent_of_zero, add_zero,
      inv_zero]
#align real.convergent_of_int Real.convergent_of_int

/-!
Our `convergent`s agree with `GeneralizedContinuedFraction.convergents`.
-/


open GeneralizedContinuedFraction

/-- The `n`th convergent of the `GeneralizedContinuedFraction.of ξ`
agrees with `ξ.convergent n`. -/
theorem continued_fraction_convergent_eq_convergent (ξ : ℝ) (n : ℕ) :
    (GeneralizedContinuedFraction.of ξ).convergents n = ξ.convergent n := by
  induction' n with n ih generalizing ξ
  -- ⊢ convergents (GeneralizedContinuedFraction.of ξ) Nat.zero = ↑(convergent ξ Na …
  · simp only [Nat.zero_eq, zeroth_convergent_eq_h, of_h_eq_floor, convergent_zero,
      Rat.cast_coe_int]
  · rw [convergents_succ, ih (fract ξ)⁻¹, convergent_succ, one_div]
    -- ⊢ ↑⌊ξ⌋ + (↑(convergent (fract ξ)⁻¹ n))⁻¹ = ↑(↑⌊ξ⌋ + (convergent (fract ξ)⁻¹ n) …
    norm_cast
    -- 🎉 no goals
#align real.continued_fraction_convergent_eq_convergent Real.continued_fraction_convergent_eq_convergent

end Real

end Convergent

/-!
### The key technical condition for the induction proof
-/


namespace Real

open Int

-- this is not `private`, as it is used in the public `exists_rat_eq_convergent'` below.
/-- Define the technical condition to be used as assumption in the inductive proof. -/
def ContfracLegendre.Ass (ξ : ℝ) (u v : ℤ) : Prop :=
  IsCoprime u v ∧ (v = 1 → (-(1 / 2) : ℝ) < ξ - u) ∧
    |ξ - u / v| < ((v : ℝ) * (2 * v - 1))⁻¹
#align real.contfrac_legendre.ass Real.ContfracLegendre.Ass

-- ### Auxiliary lemmas
-- This saves a few lines below, as it is frequently needed.
private theorem aux₀ {v : ℤ} (hv : 0 < v) : (0 : ℝ) < v ∧ (0 : ℝ) < 2 * v - 1 :=
  ⟨cast_pos.mpr hv, by norm_cast; linarith⟩
                       -- ⊢ 0 < 2 * v - 1
                                  -- 🎉 no goals

-- In the following, we assume that `ass ξ u v` holds and `v ≥ 2`.
variable {ξ : ℝ} {u v : ℤ} (hv : 2 ≤ v) (h : ContfracLegendre.Ass ξ u v)

-- The fractional part of `ξ` is positive.
private theorem aux₁ : 0 < fract ξ := by
  have hv₀ : (0 : ℝ) < v := cast_pos.mpr (zero_lt_two.trans_le hv)
  -- ⊢ 0 < fract ξ
  obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv)
  -- ⊢ 0 < fract ξ
  obtain ⟨hcop, _, h⟩ := h
  -- ⊢ 0 < fract ξ
  refine' fract_pos.mpr fun hf => _
  -- ⊢ False
  rw [hf] at h
  -- ⊢ False
  have H : (2 * v - 1 : ℝ) < 1 := by
    refine'
      (mul_lt_iff_lt_one_right hv₀).mp ((inv_lt_inv hv₀ (mul_pos hv₁ hv₂)).mp (lt_of_le_of_lt _ h))
    have h' : (⌊ξ⌋ : ℝ) - u / v = (⌊ξ⌋ * v - u) / v := by field_simp
    rw [h', abs_div, abs_of_pos hv₀, ← one_div, div_le_div_right hv₀]
    norm_cast
    rw [← zero_add (1 : ℤ), add_one_le_iff, abs_pos, sub_ne_zero]
    rintro rfl
    cases isUnit_iff.mp (isCoprime_self.mp (IsCoprime.mul_left_iff.mp hcop).2) <;> linarith
  norm_cast at H
  -- ⊢ False
  linarith only [hv, H]
  -- 🎉 no goals

-- An auxiliary lemma for the inductive step.
private theorem aux₂ : 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v := by
  obtain ⟨hcop, _, h⟩ := h
  -- ⊢ 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v
  obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
  -- ⊢ 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v
  have hv₁ : 0 < 2 * v - 1 := by linarith only [hv]
  -- ⊢ 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v
  rw [← one_div, lt_div_iff (mul_pos hv₀ hv₀'), ← abs_of_pos (mul_pos hv₀ hv₀'), ← abs_mul, sub_mul,
    ← mul_assoc, ← mul_assoc, div_mul_cancel _ hv₀.ne', abs_sub_comm, abs_lt, lt_sub_iff_add_lt,
    sub_lt_iff_lt_add, mul_assoc] at h
  have hu₀ : 0 ≤ u - ⌊ξ⌋ * v := by
    -- Porting note: this abused the definitional equality `-1 + 1 = 0`
    -- refine' (zero_le_mul_right hv₁).mp ((lt_iff_add_one_le (-1 : ℤ) _).mp _)
    refine' (zero_le_mul_right hv₁).mp ?_
    rw [←sub_one_lt_iff, zero_sub]
    replace h := h.1
    rw [← lt_sub_iff_add_lt, ← mul_assoc, ← sub_mul] at h
    exact_mod_cast
      h.trans_le
        ((mul_le_mul_right <| hv₀').mpr <|
          (sub_le_sub_iff_left (u : ℝ)).mpr ((mul_le_mul_right hv₀).mpr (floor_le ξ)))
  have hu₁ : u - ⌊ξ⌋ * v ≤ v := by
    refine' le_of_mul_le_mul_right (le_of_lt_add_one _) hv₁
    replace h := h.2
    rw [← sub_lt_iff_lt_add, ← mul_assoc, ← sub_mul, ← add_lt_add_iff_right (v * (2 * v - 1) : ℝ),
      add_comm (1 : ℝ)] at h
    have :=
      (mul_lt_mul_right <| hv₀').mpr
        ((sub_lt_sub_iff_left (u : ℝ)).mpr <|
          (mul_lt_mul_right hv₀).mpr <| sub_right_lt_of_lt_add <| lt_floor_add_one ξ)
    rw [sub_mul ξ, one_mul, ← sub_add, add_mul] at this
    exact_mod_cast this.trans h
  have huv_cop : IsCoprime (u - ⌊ξ⌋ * v) v := by
    rwa [sub_eq_add_neg, ← neg_mul, IsCoprime.add_mul_right_left_iff]
  refine' ⟨lt_of_le_of_ne' hu₀ fun hf => _, lt_of_le_of_ne hu₁ fun hf => _⟩ <;>
  -- ⊢ False
    · rw [hf] at huv_cop
      -- ⊢ False
      -- ⊢ False
      -- ⊢ False
      simp only [isCoprime_zero_left, isCoprime_self, isUnit_iff] at huv_cop
      -- ⊢ False
                                              -- 🎉 no goals
                                              -- 🎉 no goals
      -- ⊢ False
      cases' huv_cop with huv_cop huv_cop <;> linarith only [hv, huv_cop]
      -- ⊢ False
                                              -- 🎉 no goals
                                              -- 🎉 no goals

-- The key step: the relevant inequality persists in the inductive step.
private theorem aux₃ :
    |(fract ξ)⁻¹ - v / (u - ⌊ξ⌋ * v)| < (((u : ℝ) - ⌊ξ⌋ * v) * (2 * (u - ⌊ξ⌋ * v) - 1))⁻¹ := by
  obtain ⟨hu₀, huv⟩ := aux₂ hv h
  -- ⊢ |(fract ξ)⁻¹ - ↑v / (↑u - ↑⌊ξ⌋ * ↑v)| < ((↑u - ↑⌊ξ⌋ * ↑v) * (2 * (↑u - ↑⌊ξ⌋  …
  have hξ₀ := aux₁ hv h
  -- ⊢ |(fract ξ)⁻¹ - ↑v / (↑u - ↑⌊ξ⌋ * ↑v)| < ((↑u - ↑⌊ξ⌋ * ↑v) * (2 * (↑u - ↑⌊ξ⌋  …
  set u' := u - ⌊ξ⌋ * v with hu'
  -- ⊢ |(fract ξ)⁻¹ - ↑v / (↑u - ↑⌊ξ⌋ * ↑v)| < ((↑u - ↑⌊ξ⌋ * ↑v) * (2 * (↑u - ↑⌊ξ⌋  …
  have hu'ℝ : (u' : ℝ) = u - ⌊ξ⌋ * v := by exact_mod_cast hu'
  -- ⊢ |(fract ξ)⁻¹ - ↑v / (↑u - ↑⌊ξ⌋ * ↑v)| < ((↑u - ↑⌊ξ⌋ * ↑v) * (2 * (↑u - ↑⌊ξ⌋  …
  rw [← hu'ℝ]
  -- ⊢ |(fract ξ)⁻¹ - ↑v / ↑u'| < (↑u' * (2 * ↑u' - 1))⁻¹
  replace hu'ℝ := (eq_sub_iff_add_eq.mp hu'ℝ).symm
  -- ⊢ |(fract ξ)⁻¹ - ↑v / ↑u'| < (↑u' * (2 * ↑u' - 1))⁻¹
  obtain ⟨Hu, Hu'⟩ := aux₀ hu₀
  -- ⊢ |(fract ξ)⁻¹ - ↑v / ↑u'| < (↑u' * (2 * ↑u' - 1))⁻¹
  obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv)
  -- ⊢ |(fract ξ)⁻¹ - ↑v / ↑u'| < (↑u' * (2 * ↑u' - 1))⁻¹
  have H₁ := div_pos (div_pos Hv Hu) hξ₀
  -- ⊢ |(fract ξ)⁻¹ - ↑v / ↑u'| < (↑u' * (2 * ↑u' - 1))⁻¹
  replace h := h.2.2
  -- ⊢ |(fract ξ)⁻¹ - ↑v / ↑u'| < (↑u' * (2 * ↑u' - 1))⁻¹
  have h' : |fract ξ - u' / v| < ((v : ℝ) * (2 * v - 1))⁻¹ := by
    rwa [hu'ℝ, add_div, mul_div_cancel _ Hv.ne', ← sub_sub, sub_right_comm] at h
  have H : (2 * u' - 1 : ℝ) ≤ (2 * v - 1) * fract ξ := by
    replace h := (abs_lt.mp h).1
    have : (2 * (v : ℝ) - 1) * (-((v : ℝ) * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v := by
      field_simp; ring
    rw [hu'ℝ, add_div, mul_div_cancel _ Hv.ne', ← sub_sub, sub_right_comm, self_sub_floor,
      lt_sub_iff_add_lt, ← mul_lt_mul_left Hv', this] at h
    refine' LE.le.trans _ h.le
    rw [sub_le_sub_iff_left, div_le_one Hv, add_comm]
    exact_mod_cast huv
  have help₁ : ∀ {a b c : ℝ}, a ≠ 0 → b ≠ 0 → c ≠ 0 → |a⁻¹ - b / c| = |(a - c / b) * (b / c / a)| :=
    by intros; rw [abs_sub_comm]; congr 1; field_simp; ring
  have help₂ :
    ∀ {a b c d : ℝ}, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → (b * c)⁻¹ * (b / d / a) = (d * c * a)⁻¹ := by
    intros; field_simp; ring
  calc
    |(fract ξ)⁻¹ - v / u'| = |(fract ξ - u' / v) * (v / u' / fract ξ)| :=
      help₁ hξ₀.ne' Hv.ne' Hu.ne'
    _ = |fract ξ - u' / v| * (v / u' / fract ξ) := by rw [abs_mul, abs_of_pos H₁, abs_sub_comm]
    _ < ((v : ℝ) * (2 * v - 1))⁻¹ * (v / u' / fract ξ) := ((mul_lt_mul_right H₁).mpr h')
    _ = (u' * (2 * v - 1) * fract ξ)⁻¹ := (help₂ hξ₀.ne' Hv.ne' Hv'.ne' Hu.ne')
    _ ≤ ((u' : ℝ) * (2 * u' - 1))⁻¹ := by
      rwa [inv_le_inv (mul_pos (mul_pos Hu Hv') hξ₀) <| mul_pos Hu Hu', mul_assoc,
        mul_le_mul_left Hu]

-- The conditions `ass ξ u v` persist in the inductive step.
private theorem invariant : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * v) := by
  refine' ⟨_, fun huv => _, by exact_mod_cast aux₃ hv h⟩
  -- ⊢ IsCoprime v (u - ⌊ξ⌋ * v)
  · rw [sub_eq_add_neg, ← neg_mul, isCoprime_comm, IsCoprime.add_mul_right_left_iff]
    -- ⊢ IsCoprime u v
    exact h.1
    -- 🎉 no goals
  · obtain hv₀' := (aux₀ (zero_lt_two.trans_le hv)).2
    -- ⊢ -(1 / 2) < (fract ξ)⁻¹ - ↑v
    have Hv : (v * (2 * v - 1) : ℝ)⁻¹ + (v : ℝ)⁻¹ = 2 / (2 * v - 1) := by
      field_simp; ring
    have Huv : (u / v : ℝ) = ⌊ξ⌋ + (v : ℝ)⁻¹ := by
      rw [sub_eq_iff_eq_add'.mp huv]; field_simp
    have h' := (abs_sub_lt_iff.mp h.2.2).1
    -- ⊢ -(1 / 2) < (fract ξ)⁻¹ - ↑v
    rw [Huv, ← sub_sub, sub_lt_iff_lt_add, self_sub_floor, Hv] at h'
    -- ⊢ -(1 / 2) < (fract ξ)⁻¹ - ↑v
    rwa [lt_sub_iff_add_lt', (by ring : (v : ℝ) + -(1 / 2) = (2 * v - 1) / 2),
      lt_inv (div_pos hv₀' zero_lt_two) (aux₁ hv h), inv_div]

/-!
### The main result
-/


/-- The technical version of *Legendre's Theorem*. -/
theorem exists_rat_eq_convergent' {v : ℕ} (h' : ContfracLegendre.Ass ξ u v) :
    ∃ n, (u / v : ℚ) = ξ.convergent n := by
  -- Porting note: `induction` got in trouble because of the irrelevant hypothesis `h`
  clear h; have h := h'; clear h'
  -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
           -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
                         -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
  induction v using Nat.strong_induction_on generalizing ξ u with | h v ih => ?_
  -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
  -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
  rcases lt_trichotomy v 1 with (ht | rfl | ht)
  · replace h := h.2.2
    -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
    simp only [Nat.lt_one_iff.mp ht, Nat.cast_zero, div_zero, tsub_zero, zero_mul,
      cast_zero, inv_zero] at h
    exact False.elim (lt_irrefl _ <| (abs_nonneg ξ).trans_lt h)
    -- 🎉 no goals
  · rw [Nat.cast_one, div_one]
    -- ⊢ ∃ n, ↑u = convergent ξ n
    obtain ⟨_, h₁, h₂⟩ := h
    -- ⊢ ∃ n, ↑u = convergent ξ n
    cases' le_or_lt (u : ℝ) ξ with ht ht
    -- ⊢ ∃ n, ↑u = convergent ξ n
    · use 0
      -- ⊢ ↑u = convergent ξ 0
      rw [convergent_zero, Rat.coe_int_inj, eq_comm, floor_eq_iff]
      -- ⊢ ↑u ≤ ξ ∧ ξ < ↑u + 1
      convert And.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2) <;> norm_num
      -- ⊢ ↑u = ↑u / ↑↑1
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
    · replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl)
      -- ⊢ ∃ n, ↑u = convergent ξ n
      have hξ₁ : ⌊ξ⌋ = u - 1 := by
        rw [floor_eq_iff, cast_sub, cast_one, sub_add_cancel]
        exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩
      cases' eq_or_ne ξ ⌊ξ⌋ with Hξ Hξ
      -- ⊢ ∃ n, ↑u = convergent ξ n
      · rw [Hξ, hξ₁, cast_sub, cast_one, ← sub_eq_add_neg, sub_lt_sub_iff_left] at h₁
        -- ⊢ ∃ n, ↑u = convergent ξ n
        exact False.elim (lt_irrefl _ <| h₁.trans one_half_lt_one)
        -- 🎉 no goals
      · have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1 := by
          rw [floor_eq_iff, cast_one, le_inv zero_lt_one (fract_pos.mpr Hξ), inv_one,
            one_add_one_eq_two, inv_lt (fract_pos.mpr Hξ) zero_lt_two]
          refine' ⟨(fract_lt_one ξ).le, _⟩
          rw [fract, hξ₁, cast_sub, cast_one, lt_sub_iff_add_lt', sub_add]
          convert h₁ using 1
          -- Porting note: added (`convert` handled this in lean 3)
          rw [sub_eq_add_neg]
          norm_num
        use 1
        -- ⊢ ↑u = convergent ξ 1
        simp [convergent, hξ₁, hξ₂, cast_sub, cast_one]
        -- 🎉 no goals
  · obtain ⟨huv₀, huv₁⟩ := aux₂ (Nat.cast_le.mpr ht) h
    -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
    have Hv : (v : ℚ) ≠ 0 := (Nat.cast_pos.mpr (zero_lt_one.trans ht)).ne'
    -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
    have huv₁' : (u - ⌊ξ⌋ * v).toNat < v := by zify; rwa [toNat_of_nonneg huv₀.le]
    -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
    have inv : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).toNat :=
      (toNat_of_nonneg huv₀.le).symm ▸ invariant (Nat.cast_le.mpr ht) h
    obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).toNat huv₁' inv
    -- ⊢ ∃ n, ↑u / ↑v = convergent ξ n
    use n + 1
    -- ⊢ ↑u / ↑v = convergent ξ (n + 1)
    rw [convergent_succ, ← hn,
      (by exact_mod_cast toNat_of_nonneg huv₀.le : ((u - ⌊ξ⌋ * v).toNat : ℚ) = u - ⌊ξ⌋ * v),
      cast_ofNat, inv_div, sub_div, mul_div_cancel _ Hv, add_sub_cancel'_right]
#align real.exists_rat_eq_convergent' Real.exists_rat_eq_convergent'

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This version uses `Real.convergent`. -/
theorem exists_rat_eq_convergent {q : ℚ} (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, q = ξ.convergent n := by
  refine' q.num_div_den ▸ exists_rat_eq_convergent' ⟨_, fun hd => _, _⟩
  · exact coprime_iff_nat_coprime.mpr (natAbs_ofNat q.den ▸ q.reduced)
    -- 🎉 no goals
  · rw [← q.den_eq_one_iff.mp (Nat.cast_eq_one.mp hd)] at h
    -- ⊢ -(1 / 2) < ξ - ↑q.num
    simpa only [Rat.coe_int_den, Nat.cast_one, one_pow, mul_one] using (abs_lt.mp h).1
    -- 🎉 no goals
  · obtain ⟨hq₀, hq₁⟩ := aux₀ (Nat.cast_pos.mpr q.pos)
    -- ⊢ |ξ - ↑q.num / ↑↑q.den| < (↑↑q.den * (2 * ↑↑q.den - 1))⁻¹
    replace hq₁ := mul_pos hq₀ hq₁
    -- ⊢ |ξ - ↑q.num / ↑↑q.den| < (↑↑q.den * (2 * ↑↑q.den - 1))⁻¹
    have hq₂ : (0 : ℝ) < 2 * (q.den * q.den) := mul_pos zero_lt_two (mul_pos hq₀ hq₀)
    -- ⊢ |ξ - ↑q.num / ↑↑q.den| < (↑↑q.den * (2 * ↑↑q.den - 1))⁻¹
    rw [cast_ofNat] at *
    -- ⊢ |ξ - ↑q.num / ↑q.den| < (↑q.den * (2 * ↑q.den - 1))⁻¹
    rw [(by norm_cast : (q.num / q.den : ℝ) = (q.num / q.den : ℚ)), Rat.num_div_den]
    -- ⊢ |ξ - ↑q| < (↑q.den * (2 * ↑q.den - 1))⁻¹
    exact h.trans (by rw [← one_div, sq, one_div_lt_one_div hq₂ hq₁, ← sub_pos]; ring_nf; exact hq₀)
    -- 🎉 no goals
#align real.exists_rat_eq_convergent Real.exists_rat_eq_convergent

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This is the version using `generalized_contined_fraction.convergents`. -/
theorem exists_continued_fraction_convergent_eq_rat {q : ℚ}
    (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, (GeneralizedContinuedFraction.of ξ).convergents n = q := by
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  -- ⊢ ∃ n, GeneralizedContinuedFraction.convergents (GeneralizedContinuedFraction. …
  exact ⟨n, hn.symm ▸ continued_fraction_convergent_eq_convergent ξ n⟩
  -- 🎉 no goals
#align real.exists_continued_fraction_convergent_eq_rat Real.exists_continued_fraction_convergent_eq_rat

end Real
