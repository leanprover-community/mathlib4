/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# L-series of functions on `ZMod N`

We show that if `N` is a positive integer and `Φ : ZMod N → ℂ`, then the L-series of `Φ` has
analytic continuation (away from a pole at `s = 1` if `∑ j, Φ j ≠ 0`). Assuming `Φ` is either
even or odd, we define completed L-series and show analytic continuation of these too.

The most familiar case is when `Φ` is a Dirichlet character, but the results here are valid
for general functions; for the specific case of Dirichlet characters see
`Mathlib.NumberTheory.LSeries.DirichletContinuation`.

## Main definitions

* `ZMod.LFunction Φ s`: the meromorphic continuation of the function `∑ n : ℕ, Φ n * n ^ (-s)`.
* `completedLFunction Φ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction Φ s * gammaFactor Φ s` where `gammaFactor Φ s`
  is the archimedean Gamma-factor.

Note that if `Φ` is not either even or odd, there is no natural definition of the completed
L-function; we arbitrarily declare that if `Φ` is not even, then `completedLFunction Φ` is the
completed L-function of the odd part of `Φ`.

## Main theorems

* `ZMod.LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive
  `LSeries`.
* `ZMod.differentiableAt_LFunction`: `ZMod.LFunction Φ` is differentiable at `s ∈ ℂ` if either
  `s ≠ 1` or `∑ j, Φ j = 0`.
* `ZMod.LFunction_one_sub`: the functional equation relating `LFunction Φ (1 - s)` to
  `LFunction (𝓕 Φ) s`, where `𝓕` is the Fourier transform.
* `ZMod.LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction Φ s = completedLFunction Φ s / gammaFactor Φ s`, unless `s = 0` and `Φ 0 ≠ 0`.
* `ZMod.differentiableAt_completedLFunction`: `ZMod.completedLFunction Φ` is differentiable at
  `s ∈ ℂ`, unless `s = 1` and `∑ j, Φ j ≠ 0`, or `s = 0` and `Φ 0 ≠ 0`.
-/

open HurwitzZeta Complex ZMod Finset Classical Topology Filter Set

open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- If `Φ` is a periodic function, then the L-series of `Φ` converges for `1 < re s`. -/
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
  let c := max' _ <| univ_nonempty.image (Complex.abs ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, Φ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries Φ`: they agree in the convergence range, but
`LSeries Φ s` is defined to be `0` if `re s ≤ 1`.
 -/
noncomputable def LFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s

/-- The L-function of a function on `ZMod 1` is a scalar multiple of the Riemann zeta function. -/
lemma LFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
    LFunction Φ s = Φ 0 * riemannZeta s := by
  simp only [LFunction, Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]

/-- For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet series. -/
lemma LFunction_eq_LSeries (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LFunction Φ s = LSeries (Φ ·) s := by
  rw [LFunction, LSeries, mul_sum, Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : (j.val / N : ℝ) ∈ Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
    (div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr <| Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAddCircle_apply, ← (hasSum_hurwitzZeta_of_one_lt_re this hs).tsum_eq, ← mul_assoc,
    ← tsum_mul_left]
  congr 1 with m
  -- The following manipulation is slightly delicate because `(x * y) ^ s = x ^ s * y ^ s` is
  -- false for general complex `x`, `y`, but it is true if `x` and `y` are non-negative reals, so
  -- we have to carefully juggle coercions `ℕ → ℝ → ℂ`.
  calc N ^ (-s) * Φ j * (1 / (m + (j.val / N : ℝ)) ^ s)
  _ = Φ j * (N ^ (-s) * (1 / (m + (j.val / N : ℝ)) ^ s)) := by
    rw [← mul_assoc, mul_comm _ (Φ _)]
  _ = Φ j * (1 / (N : ℝ) ^ s * (1 / ((j.val + N * m) / N : ℝ) ^ s)) := by
    simp only [cpow_neg, ← one_div, ofReal_div, ofReal_natCast, add_comm, add_div, ofReal_add,
      ofReal_mul, mul_div_cancel_left₀ (m : ℂ) (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ j / ((N : ℝ) * ((j.val + N * m) / N : ℝ)) ^ s := by -- this is the delicate step!
    rw [one_div_mul_one_div, mul_one_div, mul_cpow_ofReal_nonneg] <;> positivity
  _ = Φ j / (N * (j.val + N * m) / N) ^ s := by
    simp only [ofReal_natCast, ofReal_div, ofReal_add, ofReal_mul, mul_div_assoc]
  _ = Φ j / (j.val + N * m) ^ s := by
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ ↑(j.val + N * m) / (↑(j.val + N * m)) ^ s := by
    simp only [Nat.cast_add, Nat.cast_mul, natCast_zmod_val, natCast_self, zero_mul, add_zero]
  _ = LSeries.term (Φ ·) s (j.val + N * m) := by
    rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]

lemma differentiableAt_LFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (LFunction Φ) s := by
  apply (differentiable_neg.const_cpow (Or.inl <| NeZero.ne _) s).mul
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .sum fun j _ ↦ (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.sum (u := univ) fun j _ ↦
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, hs.neg_resolve_left rfl, zero_mul, sub_zero]

lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0) :
    Differentiable ℂ (LFunction Φ) :=
  fun s ↦ differentiableAt_LFunction Φ s (Or.inr hΦ)

/-- The L-function of `Φ` has a residue at `s = 1` equal to the average value of `Φ`. -/
lemma LFunction_residue_one (Φ : ZMod N → ℂ) :
    Tendsto (fun s ↦ (s - 1) * LFunction Φ s) (𝓝[≠] 1) (𝓝 (∑ j, Φ j / N)) := by
  simp only [sum_div, LFunction, mul_sum]
  refine tendsto_finset_sum _ fun j _ ↦ ?_
  rw [(by ring : Φ j / N = Φ j * (1 / N * 1)), one_div, ← cpow_neg_one]
  simp only [show ∀ a b c d : ℂ, a * (b * (c * d)) = c * (b * (a * d)) by intros; ring]
  refine tendsto_const_nhds.mul (.mul ?_ <| hurwitzZeta_residue_one _)
  exact ((continuous_neg.const_cpow (Or.inl <| NeZero.ne _)).tendsto _).mono_left
    nhdsWithin_le_nhds

local notation "𝕖" => stdAddChar

/--
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the standard additive
character, agrees with `expZeta (j / N)` on `1 < re s`. Private since it is a stepping-stone to
the more general result `LFunction_stdAddChar_eq_expZeta` below.
-/
private lemma LFunction_stdAddChar_eq_expZeta_of_one_lt_re (j : ZMod N) {s : ℂ} (hs : 1 < s.re) :
    LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  rw [toAddCircle_apply, ← (hasSum_expZeta_of_one_lt_re (j.val / N) hs).tsum_eq,
    LFunction_eq_LSeries _ hs, LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), ofReal_div, ofReal_natCast,
    ofReal_natCast, mul_assoc, div_mul_eq_mul_div, stdAddChar_apply]
  have := ZMod.toCircle_intCast (N := N) (j.val * n)
  conv_rhs at this => rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_assoc]
  rw [← this, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_zmod_val]

/--
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the standard additive
character, is `expZeta (j / N)`.

Note this is not at all obvious from the definitions, and we prove it by analytic continuation
from the convergence range.
-/
lemma LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : ℂ) (hjs : j ≠ 0 ∨ s ≠ 1) :
    LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  let U := if j = 0 then {z : ℂ | z ≠ 1} else univ -- region of analyticity of both functions
  let V := {z : ℂ | 1 < re z} -- convergence region
  have hUo : IsOpen U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using isOpen_compl_singleton
    · simp only [h, ↓reduceIte, isOpen_univ, U]
  let f := LFunction (fun k ↦ stdAddChar (j * k))
  let g := expZeta (toAddCircle j)
  have hU {u} : u ∈ U ↔ u ≠ 1 ∨ j ≠ 0 := by simp only [mem_ite_univ_right, U]; tauto
  -- hypotheses for uniqueness of analytic continuation
  have hf : AnalyticOn ℂ f U := by
    refine DifferentiableOn.analyticOn (fun u hu ↦ ?_) hUo
    refine (differentiableAt_LFunction _ _ ((hU.mp hu).imp_right fun h ↦ ?_)).differentiableWithinAt
    simp only [mul_comm j, AddChar.sum_mulShift _ (isPrimitive_stdAddChar _), h,
      ↓reduceIte, CharP.cast_eq_zero, or_true]
  have hg : AnalyticOn ℂ g U := by
    refine DifferentiableOn.analyticOn (fun u hu ↦ ?_) hUo
    refine (differentiableAt_expZeta _ _ ((hU.mp hu).imp_right fun h ↦ ?_)).differentiableWithinAt
    rwa [ne_eq, toAddCircle_eq_zero]
  have hUc : IsPreconnected U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using
        (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
    · simpa only [h, ↓reduceIte, U] using isPreconnected_univ
  have hV : V ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hUmem : 2 ∈ U := by simp [U]
  have hUmem' : s ∈ U := hU.mpr hjs.symm
  -- apply uniqueness result
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hUmem ?_ hUmem'
  -- now remains to prove equality on `1 < re s`
  filter_upwards [hV] with z using LFunction_stdAddChar_eq_expZeta_of_one_lt_re _

/-- Explicit formula for the L-function of `𝓕 Φ`, where `𝓕` is the discrete Fourier transform. -/
lemma LFunction_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s := by
  have (j : ZMod N) : Φ j * LFunction (fun k ↦ 𝕖 (-j * k)) s =
      Φ j * expZeta (toAddCircle (-j)) s := by
    by_cases h : -j ≠ 0 ∨ s ≠ 1
    · rw [LFunction_stdAddChar_eq_expZeta _ _ h]
    · simp only [neg_ne_zero, not_or, not_not] at h
      rw [h.1, show Φ 0 = 0 by tauto, zero_mul, zero_mul]
  simp only [LFunction, ← this, mul_sum]
  rw [dft_def, sum_comm]
  simp only [sum_mul, mul_sum, Circle.smul_def, smul_eq_mul, stdAddChar_apply, ← mul_assoc]
  congr 1 with j
  congr 1 with k
  rw [mul_assoc (Φ _), mul_comm (Φ _), neg_mul]

/-- Functional equation for `ZMod` L-functions, in terms of discrete Fourier transform. -/
theorem LFunction_one_sub (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction Φ (1 - s) = N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *
      (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s
       + cexp (-π * I * s / 2) * LFunction (𝓕 fun x ↦ Φ (-x)) s) := by
  rw [LFunction]
  have (j : ZMod N) :  Φ j * hurwitzZeta (toAddCircle j) (1 - s) = Φ j *
      ((2 * π) ^ (-s) * Gamma s * (cexp (-π * I * s / 2) *
      expZeta (toAddCircle j) s + cexp (π * I * s / 2) * expZeta (-toAddCircle j) s)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rcases hs' with hΦ | hs'
      · simp only [hΦ, zero_mul]
      · rw [hurwitzZeta_one_sub _ hs (Or.inr hs')]
    · rw [hurwitzZeta_one_sub _ hs (Or.inl <| toAddCircle_eq_zero.not.mpr hj)]
  simp only [this, mul_assoc _ _ (Gamma s)]
  -- get rid of Gamma terms and power of N
  generalize (2 * π) ^ (-s) * Gamma s = C
  simp_rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc,
    neg_sub]
  congr 2
  -- now gather sum terms
  rw [LFunction_dft _ hs', LFunction_dft _ (hs'.imp_left <| by simp only [neg_zero, imp_self])]
  conv_rhs => enter [2, 2]; rw [← (Equiv.neg _).sum_comp _ _ (by simp), Equiv.neg_apply]
  simp_rw [neg_neg, mul_sum, ← sum_add_distrib, ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
    ← mul_add, map_neg, add_comm]

section signed

variable {Φ : ZMod N → ℂ}

/--
If `Φ` is either even or odd, we can write `LFunction Φ s` using signed Hurwitz zeta functions.
Useful for comparison with `completedLFunction Φ s`.
-/
lemma LFunction_def_signed (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) :
    LFunction Φ s =
      if Φ.Even then N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s
      else N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, ← mul_ite, hurwitzZeta, mul_add, sum_add_distrib]
  rw [← mul_add]
  congr 1
  by_cases h : Φ.Even
  · simp only [h, ↓reduceIte, add_right_eq_self, ← sum_neg_distrib, ← neg_eq_self ℂ]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, h i, map_neg, hurwitzZetaOdd_neg, mul_neg]
  · simp only [h, ↓reduceIte, add_left_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, map_neg, hurwitzZetaEven_neg, (show Φ.Odd by tauto) i, neg_mul]

/-- Explicit formula for `LFunction Φ 0` when `Φ` is even. -/
lemma LFunction_apply_zero_of_even (hΦ : Φ.Even) :
    LFunction Φ 0 = -Φ 0 / 2 := by
  simp only [LFunction_def_signed (Or.inl hΦ), hΦ, ↓reduceIte, neg_zero, cpow_zero,
    hurwitzZetaEven_apply_zero, toAddCircle_eq_zero, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    one_mul, mul_div, mul_neg_one]

/-- The L-function of an even function vanishes at negative even integers. -/
lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : ℕ) :
    LFunction Φ (-2 * (n + 1)) = 0 := by
  simp only [LFunction_def_signed (Or.inl hΦ), hΦ, ↓reduceIte,
    hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero, sum_const_zero]

/-- The L-function of an odd function vanishes at negative odd integers. -/
lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : ℕ) :
    LFunction Φ (-2 * n - 1) = 0 := by
  by_cases hΦ' : Φ.Even
  · -- silly case: `Φ` is both even and odd, so it's zero
    have : Φ = 0 := funext fun j ↦ by rw [Pi.zero_apply, ← neg_eq_self ℂ, ← hΦ j, hΦ' j]
    simp [LFunction, this]
  · simp only [LFunction_def_signed (Or.inr hΦ), hΦ', ↓reduceIte,
      hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, sum_const_zero]

variable (Φ) in
/--
The completed L-function of a function mod `N`.

This is only mathematically meaningful if `Φ` is either even, or odd. We extend this to all `Φ`
as follows: if `Φ` is not even, then the completed L-series of `Φ` is the `L`-series of the odd
part of `Φ`.
-/
noncomputable def completedLFunction (s : ℂ) : ℂ :=
  if Φ.Even then N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  else N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

variable (Φ) in
/--
The completed L-function of a function mod `N`, modified by adding multiples of `N ^ (-s) / s` and
`N ^ (-s) / (1 - s)` to make it entire.

This is well-defined for all `Φ`, but is uninteresting unless `Φ` is either even or odd.
-/
noncomputable def completedLFunction₀ (s : ℂ) : ℂ :=
  if Φ.Even then N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  else N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

/--
The L-function a function mod 1 is a scalar multiple of the completed Riemann zeta function.
-/
lemma completedLFunction_modOne_eq {Φ : ZMod 1 → ℂ} (s : ℂ) :
    completedLFunction Φ s = Φ 1 * completedRiemannZeta s := by
  have : Φ.Even := fun j ↦ congr_arg Φ <| (Unique.eq_default (-j)).trans (Unique.eq_default j).symm
  simp [completedLFunction, this]
  change Φ 1 * completedHurwitzZetaEven (toAddCircle 0) s = _
  rw [map_zero, completedHurwitzZetaEven_zero]

variable (Φ) in
/-- The function `completedLFunction₀ Φ` is differentiable. -/
lemma differentiable_completedLFunction₀ : Differentiable ℂ (completedLFunction₀ Φ) := by
  unfold completedLFunction₀
  by_cases h : Φ.Even <;>
  simp only [h, reduceIte] <;>
  refine (differentiable_neg.const_cpow <| Or.inl <| NeZero.ne _).mul
    (.sum fun i _ ↦ .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]

lemma completedLFunction_eq (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) :
    completedLFunction Φ s =
      completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s) := by
  simp only [completedLFunction, completedLFunction₀]
  split_ifs with h
  · simp only [completedHurwitzZetaEven_eq, mul_sub, sum_sub_distrib]
    congr 1
    · simp only [toAddCircle_eq_zero, div_eq_mul_inv, ite_mul, one_mul, zero_mul, mul_ite,
        mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, mul_assoc]
    · rw [← sum_mul, mul_one_div, mul_div_assoc]
  · replace hΦ : Function.Odd Φ := by tauto
    have : Φ 0 = 0 := by rw [← neg_eq_self ℂ, ← hΦ 0, neg_zero]
    rw [this, mul_zero, zero_div, sub_zero]
    suffices ∑ j, Φ j = 0 by rw [this, mul_zero, zero_div, sub_zero]
    simp only [← neg_eq_self ℂ, ← sum_neg_distrib]
    exact Fintype.sum_equiv _ _ _ (fun i ↦ by rw [Equiv.neg_apply, hΦ])

/--
The completed L-function of a function mod `N` is differentiable, with the following
exceptions: at `s = 1` if `∑ j, Φ j ≠ 0`; and at `s = 0` if `Φ 0 ≠ 0`. (This result is optimal.)
-/
lemma differentiableAt_completedLFunction (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) (hs₀ : s ≠ 0 ∨ Φ 0 = 0)
    (hs₁ : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (completedLFunction Φ) s := by
  simp only [funext fun s ↦ completedLFunction_eq hΦ s, mul_div_assoc]
  -- We know `completedLFunction₀` is differentiable everywhere, so it suffices to show that the
  -- correction terms from `completedLFunction_eq` are differentiable at `s`.
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).sub ?_
  · -- term with `1 / s`
    refine ((differentiable_neg.const_cpow <| Or.inl <| NeZero.ne _) s).mul
      (?_ : DifferentiableAt ℂ (fun t ↦ Φ 0 / t) s)
    rcases hs₀ with h | h
    · exact (differentiableAt_const _).div differentiableAt_id h
    · simp only [h, zero_div, differentiableAt_const]
  · -- term with `1 / (1 - s)`
    apply ((differentiable_neg.const_cpow <| Or.inl <| NeZero.ne _) s).mul
    rcases hs₁ with h | h
    · exact (differentiableAt_const _).div (by fun_prop) (by rwa [sub_ne_zero, ne_comm])
    · simp only [h, zero_div, differentiableAt_const]

/--
Special case of `differentiableAt_completedLFunction` asserting differentiability everywhere
under suitable hypotheses.
-/
lemma differentiable_completedLFunction
    (hΦ₁ : Φ.Even ∨ Φ.Odd) (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
    Differentiable ℂ (completedLFunction Φ) :=
  fun s ↦ differentiableAt_completedLFunction hΦ₁ s (Or.inr hΦ₂) (Or.inr hΦ₃)

/-- The Archimedean Gamma factor: `Gammaℝ s` if `Φ` is even, and `Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
   if Φ.Even then Gammaℝ s else Gammaℝ (s + 1)

/--
Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well (except at `s = 0`, where it is genuinely
false if `Φ 0 ≠ 0`).
-/
lemma LFunction_eq_completed_div_gammaFactor (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
    LFunction Φ s = completedLFunction Φ s / gammaFactor Φ s := by
  rw [LFunction_def_signed hΦ, completedLFunction, gammaFactor]
  split_ifs with h
  · -- `Φ` even
    simp only [mul_div_assoc, sum_div]
    congr 2 with i
    rcases ne_or_eq i 0 with hi | rfl
    · rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inl (hi ∘ toAddCircle_eq_zero.mp))]
    · rcases hs with hs | hΦ'
      · rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs)]
      · simp only [hΦ', map_zero, zero_mul]
  · -- `Φ` not even
    simp only [hurwitzZetaOdd, mul_div_assoc, sum_div]

end signed

end ZMod
