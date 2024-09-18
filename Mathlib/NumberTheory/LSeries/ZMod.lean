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
* `ZMod.completedLFunction Φ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction Φ s` multiplied by an Archimedean Gamma-factor.

Note that `ZMod.completedLFunction Φ s` is only mathematically well-defined if `Φ` is either even
or odd. We have arbitrarily defined it to be the completed L-function of the odd part of `Φ`, if
`Φ` is not even.

## Main theorems

Results for non-completed L-functions:

* `ZMod.LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive
  `LSeries`.
* `ZMod.differentiableAt_LFunction`: `ZMod.LFunction Φ` is differentiable at `s ∈ ℂ` if either
  `s ≠ 1` or `∑ j, Φ j = 0`.
* `ZMod.LFunction_one_sub`: the functional equation relating `LFunction Φ (1 - s)` to
  `LFunction (𝓕 Φ) s`, where `𝓕` is the Fourier transform.

Results for completed L-functions:

* `ZMod.LFunction_eq_completed_div_gammaFactor_even` and
  `LFunction_eq_completed_div_gammaFactor_odd`: we have
  `LFunction Φ s = completedLFunction Φ s / Gammaℝ s` for `Φ` even, and
  `LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1)` for `Φ` odd. (We formulate it this way
  around so it is still valid at the poles of the Gamma factor.)
* `ZMod.differentiableAt_completedLFunction`: `ZMod.completedLFunction Φ` is differentiable at
  `s ∈ ℂ`, unless `s = 1` and `∑ j, Φ j ≠ 0`, or `s = 0` and `Φ 0 ≠ 0`.
* `ZMod.completedLFunction_one_sub`: the functional equation relating
  `completedLFunction Φ (1 - s)` to `completedLFunction (𝓕 Φ) s`.
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

lemma LFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_right_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaOdd_neg, mul_neg]

lemma LFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_left_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaEven_neg, neg_mul]

/-- Explicit formula for `LFunction Φ 0` when `Φ` is even. -/
@[simp] lemma LFunction_apply_zero_of_even (hΦ : Φ.Even) :
    LFunction Φ 0 = -Φ 0 / 2 := by
  simp only [LFunction_def_even hΦ, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_div, mul_neg_one, mul_zero, sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, one_mul]

/-- The L-function of an even function vanishes at negative even integers. -/
@[simp] lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : ℕ) :
    LFunction Φ (-(2 * (n + 1))) = 0 := by
  simp only [LFunction_def_even hΦ, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero, ← neg_mul]

/-- The L-function of an odd function vanishes at negative odd integers. -/
@[simp] lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : ℕ) :
    LFunction Φ (-(2 * n) - 1) = 0 := by
  simp only [LFunction_def_odd hΦ, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero,
    ← neg_mul, sum_const_zero]

variable (Φ) in
/--
The completed L-function of a function mod `N`.

This is only mathematically meaningful if `Φ` is either even, or odd. We extend this to all `Φ`
as follows: if `Φ` is not even, then the completed L-series of `Φ` is the `L`-series of the odd
part of `Φ`.
-/
noncomputable def completedLFunction (s : ℂ) : ℂ :=
  if Φ.Even then N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  else N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

@[simp] lemma completedLFunction_zero (s : ℂ) : completedLFunction (0 : ZMod N → ℂ) s = 0 := by
  simp only [completedLFunction, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, ite_self]

lemma completedLFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s := by
  simp only [completedLFunction, hΦ, ↓reduceIte]

lemma completedLFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s := by
  by_cases hΦ' : Φ.Even
    -- if `Φ = 0` we are in the "wrong" branch of the if-then, but it's OK because both sides are 0
  · simp only [Φ.zero_of_even_and_odd hΦ' hΦ, completedLFunction_zero, Pi.zero_apply, zero_mul,
      sum_const_zero, mul_zero]
  · simp only [completedLFunction, hΦ', ↓reduceIte]

/--
The completed L-function of a function `ZMod 1 → ℂ` is a scalar multiple of the completed Riemann
zeta function.
-/
lemma completedLFunction_modOne_eq {Φ : ZMod 1 → ℂ} (s : ℂ) :
    completedLFunction Φ s = Φ 1 * completedRiemannZeta s := by
  rw [completedLFunction_def_even (show Φ.Even from fun _ ↦ congr_arg Φ (Subsingleton.elim ..)),
    Nat.cast_one, one_cpow, one_mul, ← singleton_eq_univ 0, sum_singleton, map_zero,
    completedHurwitzZetaEven_zero, Subsingleton.elim 0 1]

variable (Φ) in
/--
The completed L-function of a function mod `N`, modified by adding multiples of `N ^ (-s) / s` and
`N ^ (-s) / (1 - s)` to make it entire.

This is well-defined for all `Φ`, but is uninteresting unless `Φ` is either even or odd.
-/
noncomputable def completedLFunction₀ (s : ℂ) : ℂ :=
  if Φ.Even then N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  else N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

variable (Φ) in
/-- The function `completedLFunction₀ Φ` is differentiable. -/
lemma differentiable_completedLFunction₀ : Differentiable ℂ (completedLFunction₀ Φ) := by
  unfold completedLFunction₀
  by_cases h : Φ.Even <;>
  simp only [h, reduceIte] <;>
  refine (differentiable_neg.const_cpow <| .inl <| NeZero.ne _).mul (.sum fun i _ ↦ .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]

lemma completedLFunction_eq (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) :
    completedLFunction Φ s =
      completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s) := by
  simp only [completedLFunction, completedLFunction₀]
  obtain hΦ | ⟨hΦ', hΦ⟩ : Φ.Even ∨ (¬Φ.Even ∧ Φ.Odd) := by tauto
  · simp only [hΦ, ite_true, completedHurwitzZetaEven_eq, mul_sub, sum_sub_distrib]
    congr 1
    · simp only [toAddCircle_eq_zero, div_eq_mul_inv, ite_mul, one_mul, zero_mul, mul_ite,
        mul_zero, sum_ite_eq', ite_true, Finset.mem_univ, mul_assoc]
    · rw [← sum_mul, mul_one_div, mul_div_assoc]
  · simp only [hΦ', ite_false, hΦ.map_zero, mul_zero, zero_div, sub_zero, hΦ.sum_eq_zero]

/--
The completed L-function of a function mod `N` is differentiable, with the following
exceptions: at `s = 1` if `∑ j, Φ j ≠ 0`; and at `s = 0` if `Φ 0 ≠ 0`.
-/
lemma differentiableAt_completedLFunction (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ Φ 0 = 0) (hs₁ : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (completedLFunction Φ) s := by
  simp only [funext (completedLFunction_eq hΦ), mul_div_assoc]
  -- We know `completedLFunction₀` is differentiable everywhere, so it suffices to show that the
  -- correction terms from `completedLFunction_eq` are differentiable at `s`.
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).sub ?_
  · -- term with `1 / s`
    refine ((differentiable_neg.const_cpow <| .inl <| NeZero.ne _) s).mul (hs₀.elim ?_ ?_)
    · exact fun h ↦ (differentiableAt_const _).div differentiableAt_id h
    · exact fun h ↦ by simp only [h, funext zero_div, differentiableAt_const]
  · -- term with `1 / (1 - s)`
    refine ((differentiable_neg.const_cpow <| .inl <| NeZero.ne _) s).mul (hs₁.elim ?_ ?_)
    · exact fun h ↦ (differentiableAt_const _).div (by fun_prop) (by rwa [sub_ne_zero, ne_comm])
    · exact fun h ↦ by simp only [h, zero_div, differentiableAt_const]

/--
Special case of `differentiableAt_completedLFunction` asserting differentiability everywhere
under suitable hypotheses.
-/
lemma differentiable_completedLFunction
    (hΦ₁ : Φ.Even ∨ Φ.Odd) (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
    Differentiable ℂ (completedLFunction Φ) :=
  fun s ↦ differentiableAt_completedLFunction hΦ₁ s (.inr hΦ₂) (.inr hΦ₃)

/--
Relation between the completed L-function and the usual one (even case).
We state it this way around so it holds at the poles of the gamma factor as well
(except at `s = 0`, where it is genuinely false if `Φ 0 ≠ 0`).
-/
lemma LFunction_eq_completed_div_gammaFactor_even (hΦ : Φ.Even) (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
    LFunction Φ s = completedLFunction Φ s / Gammaℝ s := by
  simp only [completedLFunction_def_even hΦ, LFunction_def_even hΦ, mul_div_assoc, sum_div]
  congr 2 with i
  rcases ne_or_eq i 0 with hi | rfl
  · rw [hurwitzZetaEven_def_of_ne_or_ne (.inl (hi ∘ toAddCircle_eq_zero.mp))]
  · rcases hs with hs | hΦ'
    · rw [hurwitzZetaEven_def_of_ne_or_ne (.inr hs)]
    · simp only [hΦ', map_zero, zero_mul]

/--
Relation between the completed L-function and the usual one (odd case).
We state it this way around so it holds at the poles of the gamma factor as well.
-/
lemma LFunction_eq_completed_div_gammaFactor_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1) := by
  simp only [LFunction_def_odd hΦ, completedLFunction_def_odd hΦ, hurwitzZetaOdd, mul_div_assoc,
    sum_div]

/--
Express `completedCosZeta` as the L-function of a function on `ZMod N`.

The formulation is not optimal (the result is actually true for all `s ∉ {0, 1}`), but suffices for
the proof of `completedLFunction_one_sub` below.
-/
lemma completedLFunction_cos_eq_completedCosZeta_of_one_lt
    (a : ZMod N) {s : ℂ} (hs : 1 < re s) :
    completedLFunction (fun b ↦ (𝕖 (a * b) + 𝕖 (-a * b)) / 2) s =
      completedCosZeta (toAddCircle a) s := by
  set Φ := fun b ↦ (𝕖 (a * b) + 𝕖 (-a * b)) / 2
  have hΦ : Φ.Even := fun b ↦ by simp only [neg_mul, mul_neg, neg_neg, add_comm, Φ]
  have h1 : (Gammaℝ s)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by linarith))
  have h2 : s ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  have h3 : cosZeta (toAddCircle a) s = completedCosZeta (toAddCircle a) s / s.Gammaℝ :=
    Function.update_noteq (ne_zero_of_one_lt_re hs) ..
  rw [← mul_left_inj' h1, ← div_eq_mul_inv, ← div_eq_mul_inv, ← h3, cosZeta_eq,
    ← LFunction_eq_completed_div_gammaFactor_even hΦ _ (.inl <| ne_zero_of_one_lt_re hs)]
  simp only [LFunction, add_div, add_mul, sum_add_distrib, Φ]
  simp only [div_mul_eq_mul_div, ← sum_div, mul_add, ← mul_div_assoc,
    ← LFunction_stdAddChar_eq_expZeta _ _ (.inr h2), LFunction, ← map_neg]

/--
Express `completedSinZeta` as the L-function of a function on `ZMod N`.

The formulation is not optimal (the result is actually true for all `s`), but suffices for
the proof of `completedLFunction_one_sub` below.
-/
lemma completedLFunction_sin_eq_completedSinZeta_of_one_lt
    (a : ZMod N) {s : ℂ} (hs : 1 < re s) :
    completedLFunction (fun b ↦ (𝕖 (a * b) - 𝕖 (-a * b)) / (2 * I)) s =
      completedSinZeta (toAddCircle a) s := by
  set Φ := fun b ↦ (𝕖 (a * b) - 𝕖 (-a * b)) / (2 * I)
  have hΦ : Φ.Odd := fun b ↦ by simp only [Φ, neg_mul, mul_neg, neg_neg, ← neg_div, neg_sub]
  have h1 : (Gammaℝ (s + 1))⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_re_pos <| by simp only [add_re, one_re]; linarith)
  have h2 : s ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  rw [← mul_left_inj' h1, ← div_eq_mul_inv, ← div_eq_mul_inv, ← sinZeta, sinZeta_eq,
    ← LFunction_eq_completed_div_gammaFactor_odd hΦ]
  simp only [LFunction, sub_div, sub_mul, sum_sub_distrib, Φ]
  simp only [mul_sub, LFunction, div_mul_eq_mul_div, ← sum_div, ← mul_div_assoc, ← map_neg,
    ← LFunction_stdAddChar_eq_expZeta _ _ (.inr h2)]

/--
First form of functional equation for completed L-functions. Private because it is superseded
by `completedLFunction_one_sub` below, which is valid for a much wider range of `s`.
-/
private lemma completedLFunction_one_sub_of_one_lt (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) (hs : 1 < re s) :
    completedLFunction Φ (1 - s) =
      N ^ (s - 1) * I ^ (if Φ.Even then 0 else 1) * completedLFunction (𝓕 Φ) s := by
  -- preliminary mini-lemmas:
  have he (x : ZMod N) : (fun b ↦ (𝕖 (x * b) + 𝕖 (-x * b)) / 2).Even := fun _ ↦ by
    simp only [mul_neg, neg_mul, neg_neg, add_comm]
  have ho (x : ZMod N) : (fun b ↦ (𝕖 (x * b) - 𝕖 (-x * b)) / (2 * I)).Odd := fun _ ↦ by
    simp only [mul_neg, neg_mul, neg_neg, ← neg_div, neg_sub]
  -- split into two mutually-exclusive cases:
  obtain hΦ | ⟨hΦ', hΦ⟩ : Φ.Even ∨ (¬Φ.Even ∧ Φ.Odd) := by tauto
  · -- even case
    -- drill down to the key computation:
    suffices ∑ x, Φ x * completedCosZeta (toAddCircle x) s = completedLFunction (𝓕 Φ) s by
      simp only [completedLFunction_def_even hΦ, neg_sub, completedHurwitzZetaEven_one_sub, this,
        hΦ, ite_true, pow_zero, mul_one]
    -- now calculate:
    let ζ (y : ZMod N) := completedHurwitzZetaEven (toAddCircle y)
    calc ∑ x, Φ x * completedCosZeta (toAddCircle x) s
    _ = ∑ x, ∑ y, Φ x * N ^ (-s) * ((𝕖 (x * y) + 𝕖 (-x * y)) / 2) * ζ y s := by
      simp only [← completedLFunction_cos_eq_completedCosZeta_of_one_lt _ hs,
        completedLFunction_def_even (he _), mul_sum, mul_assoc]
    _ = N ^ (-s) * ∑ y, (∑ x, Φ x * ((𝕖 (x * y) + 𝕖 (-x * y)) / 2)) * ζ y s := by
      rw [sum_comm]
      simp only [mul_sum, sum_mul, mul_assoc, mul_left_comm (Φ _)]
    _ = N ^ (-s) * (∑ y, (∑ x, Φ x * 𝕖 (x * y) + ∑ x, Φ x * 𝕖 (-x * y)) / 2 * ζ y s) := by
      simp only [← mul_div_assoc, ← sum_div, mul_add, sum_add_distrib]
    _ = N ^ (-s) * (∑ y, ((𝓕 Φ (-y) + 𝓕 Φ y) / 2) * ζ y s) := by
      simp only [dft_apply, mul_neg, neg_mul, neg_neg, smul_eq_mul, mul_comm (Φ _)]
    _ = N ^ (-s) * ∑ y, 𝓕 Φ y * ζ y s := by
      simp only [dft_even_iff.mpr hΦ _, add_div, add_halves]
    _ = completedLFunction (𝓕 Φ) s := by
      rw [completedLFunction_def_even (dft_even_iff.mpr hΦ)]
  · -- odd case
    -- drill down to the key computation:
    suffices ∑ x, Φ x * completedSinZeta (toAddCircle x) s = I * completedLFunction (𝓕 Φ) s by
      simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub, this, hΦ',
        ite_false, pow_one, mul_assoc]
    -- now calculate:
    let ζ (y : ZMod N) := completedHurwitzZetaOdd (toAddCircle y)
    calc ∑ x, Φ x * completedSinZeta (toAddCircle x) s
    _ = ∑ x, ∑ y, Φ x * N ^ (-s) * ((𝕖 (x * y) - 𝕖 (-x * y)) / (2 * I)) * ζ y s := by
      simp only [← completedLFunction_sin_eq_completedSinZeta_of_one_lt _ hs,
        completedLFunction_def_odd (ho _), mul_sum, mul_assoc]
    _ = N ^ (-s) * ∑ y, (∑ x, Φ x * ((𝕖 (x * y) - 𝕖 (-x * y)) / (2 * I))) * ζ y s := by
      rw [sum_comm]
      simp only [mul_sum, sum_mul, mul_assoc, mul_left_comm (Φ _)]
    _ = N ^ (-s) * (∑ y, (∑ x, Φ x * 𝕖 (x * y) - ∑ x, Φ x * 𝕖 (-x * y)) / (2 * I) * ζ y s) := by
      simp only [← mul_div_assoc, ← sum_div, mul_sub, sum_sub_distrib]
    _ = N ^ (-s) * (∑ y, ((𝓕 Φ (-y) - 𝓕 Φ y) / (2 * I)) * ζ y s) := by
      simp only [dft_apply, mul_neg, neg_mul, neg_neg, smul_eq_mul, mul_comm (Φ _)]
    _ = I * (N ^ (-s) * ∑ y, 𝓕 Φ y * ζ y s) := by
      simp only [dft_odd_iff.mpr hΦ _, sub_eq_add_neg, ← two_mul, ← div_div,
        mul_div_cancel_left₀ _ (two_ne_zero' ℂ), div_eq_mul_inv _ I, inv_I, neg_mul_neg]
      simp only [mul_comm _ I, mul_assoc, ← mul_sum, mul_left_comm]
    _ = I * completedLFunction (𝓕 Φ) s := by
      rw [completedLFunction_def_odd (dft_odd_iff.mpr hΦ)]

/--
Functional equation for completed L-functions, valid at all points of differentiability.
-/
theorem completedLFunction_one_sub
    (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0) (hs₁ : s ≠ 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) =
      N ^ (s - 1) * I ^ (if Φ.Even then 0 else 1) * completedLFunction (𝓕 Φ) s := by
  -- We prove this using `AnalyticOn.eqOn_of_preconnected_of_eventuallyEq`, so we need to
  -- gather up the ingredients for this big theorem.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * I ^ (if Φ.Even then 0 else 1) * completedLFunction (𝓕 Φ) t
  -- Set on which F, G are analytic:
  let U := {t : ℂ | (t ≠ 0 ∨ ∑ j, Φ j = 0) ∧ (t ≠ 1 ∨ Φ 0 = 0)}
  -- Properties of U:
  have hsU : s ∈ U := ⟨hs₀, hs₁⟩
  have h2U : 2 ∈ U := ⟨.inl two_ne_zero, .inl (OfNat.ofNat_ne_one _)⟩
  have hUo : IsOpen U := by
    refine .inter ?_ ?_ <;>
    exact (isOpen_compl_singleton.union isOpen_const)
  have hUp : IsPreconnected U := by
    -- need to write `U` as the complement of an obviously countable set
    let Uc : Set ℂ := (if ∑ j, Φ j = 0 then ∅ else {0}) ∪ (if Φ 0 = 0 then ∅ else {1})
    have : Uc.Countable := by
      apply Countable.union <;>
      split_ifs <;>
      simp only [countable_singleton, countable_empty]
    convert (this.isConnected_compl_of_one_lt_rank ?_).isPreconnected using 1
    · ext x
      by_cases h : Φ 0 = 0 <;>
      by_cases h' : ∑ j, Φ j = 0 <;>
      simp only [U, Uc, h, h', and_true, and_false, or_true, or_false, ↓reduceIte, mem_setOf,
        union_empty, true_and, empty_union, compl_empty, mem_univ,
        mem_compl_iff, mem_union, not_or, not_mem_singleton_iff]
    · simp only [rank_real_complex, Nat.one_lt_ofNat]
  -- Analyticity on U:
  have hF : AnalyticOn ℂ F U := by
    refine DifferentiableOn.analyticOn (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    refine (differentiableAt_completedLFunction hΦ (1 - t) ?_ ?_).comp t ?_
    · exact ht.2.imp_left (sub_ne_zero.mpr ∘ Ne.symm)
    · exact ht.1.imp_left sub_eq_self.not.mpr
    · exact differentiableAt_id.const_sub 1
  have hG : AnalyticOn ℂ G U := by
    refine DifferentiableOn.analyticOn (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    refine .mul (.mul ?_ <| differentiableAt_const _) ?_
    · exact (DifferentiableAt.sub_const differentiableAt_id 1).const_cpow (.inl (NeZero.ne _))
    · -- Differentiablity of completed L-function for `𝓕 Φ`.
      apply differentiableAt_completedLFunction
      · rwa [dft_even_iff, dft_odd_iff]
      · exact ht.1.imp_right fun h ↦ dft_apply_zero Φ ▸ h
      · refine ht.2.imp_right fun h ↦ ?_
        simp only [← dft_apply_zero, dft_dft, neg_zero, h, smul_zero]
  -- set where we know equality
  have hV : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := eventually_of_mem hV <| completedLFunction_one_sub_of_one_lt hΦ
  -- now apply the big hammer to finish
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUp h2U hFG hsU

end signed

end ZMod
