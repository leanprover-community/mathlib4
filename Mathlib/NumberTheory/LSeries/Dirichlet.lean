/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ZetaFunction

/-!
# L-series of Dirichlet characters and arithmetic functions

We collect some results on L-series of specific (arithmetic) functions, for example,
the Möbius function `μ` or the von Mangoldt function `Λ`. In particular, we show that
`L ↗Λ` is the negative of the logarithmic derivative of the Riemann zeta function
on `re s > 1`; see `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

We also prove some general results on L-series associated to Dirichlet characters
(i.e., Dirichlet L-series). For example, we show that the abscissa of absolute convergence
equals `1` (see `DirichletCharacter.absicssaOfAbsConv`) and that the L-series does not
vanish on the open half-plane `re s > 1` (see `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`).

We deduce results on the Riemann zeta function (which is `L 1` or `L ↗ζ` on `re s > 1`)
as special cases.

## Tags

Dirichlet L-series, Möbius function, von Mangoldt function, Riemann zeta function
-/

open scoped LSeries.notation

/-- `δ` is the function underlying the arithmetic function `1`. -/
lemma ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction ℂ) = δ := by
  ext
  simp only [one_apply, LSeries.delta]


section Moebius

/-!
### The L-series of the Möbius function

We show that `L μ s` converges absolutely if and only if `re s > 1`.
-/

namespace ArithmeticFunction

open LSeries Nat Complex

lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1 := by
  intro h
  refine not_summable_one_div_on_primes <| summable_ofReal.mp <| Summable.of_neg ?_
  simp only [← Pi.neg_def, Set.indicator_comp_of_zero ofReal_zero, ofReal_inv, ofReal_natCast]
  refine (h.indicator {n | n.Prime}).congr (fun n ↦ ?_)
  by_cases hn : n ∈ {p | p.Prime}
  · simp only [Pi.neg_apply, Set.indicator_of_mem hn, term_of_ne_zero hn.ne_zero,
      moebius_apply_prime hn, cpow_one, push_cast, neg_div]
  · simp only [one_div, Pi.neg_apply, Set.indicator_of_not_mem hn, ofReal_zero, neg_zero]

/-- The L-series of the Möbius function converges absolutely at `s` if and only if `re s > 1`. -/
lemma LSeriesSummable_moebius_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n _ ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_moebius_at_one <| LSeriesSummable.of_re_le_re h' H
  · rw [abs_intCast] -- not done by `norm_cast`
    norm_cast
    exact abs_moebius_le_one

/-- The abscissa of absolute convergence of the L-series of the Möbius function is `1`. -/
lemma abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_moebius_iff, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

end ArithmeticFunction

end Moebius


/-!
### L-series of Dirichlet characters
-/

open Nat

open scoped ArithmeticFunction.zeta in
lemma ArithmeticFunction.const_one_eq_zeta {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    (1 : ℕ → R) n = (ζ ·) n := by
  simp only [Pi.one_apply, zeta_apply, hn, ↓reduceIte, cast_one]

lemma LSeries.one_convolution_eq_zeta_convolution {R : Type*} [Semiring R] (f : ℕ → R):
    (1 : ℕ → R) ⍟ f = ((ArithmeticFunction.zeta ·) : ℕ → R) ⍟ f :=
  convolution_congr ArithmeticFunction.const_one_eq_zeta fun _ ↦ rfl

lemma LSeries.convolution_one_eq_convolution_zeta {R : Type*} [Semiring R] (f : ℕ → R):
    f ⍟ (1 : ℕ → R) = f ⍟ ((ArithmeticFunction.zeta ·) : ℕ → R) :=
  convolution_congr (fun _ ↦ rfl) ArithmeticFunction.const_one_eq_zeta

/-- `χ₁` is (local) notation for the (necessarily trivial) Dirichlet character modulo `1`. -/
local notation (name := Dchar_one) "χ₁" => (1 : DirichletCharacter ℂ 1)

namespace DirichletCharacter

open LSeries Nat Complex

/-- Twisting by a Dirichlet character `χ` distributes over convolution. -/
lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : ℕ} (χ : DirichletCharacter R n)
    (f g : ℕ → R) :
    (((χ ·) : ℕ → R) * f) ⍟ (((χ ·) : ℕ → R) * g) = ((χ ·) : ℕ → R) * (f ⍟ g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [(mem_divisorsAntidiagonal.mp hp).1.symm, cast_mul, map_mul]
  exact mul_mul_mul_comm ..

lemma mul_delta {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ * δ = δ :=
  LSeries.mul_delta <| by rw [cast_one, map_one]

lemma delta_mul {n : ℕ} (χ : DirichletCharacter ℂ n) : δ * ↗χ = δ :=
  mul_comm δ _ ▸ mul_delta ..

open ArithmeticFunction in
/-- The convolution of a Dirichlet character `χ` with the twist `χ * μ` is `δ`,
the indicator function of `{1}`. -/
lemma convolution_mul_moebius {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ ⍟ (↗χ * ↗μ) = δ := by
  have : (1 : ℕ → ℂ) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution, ← one_eq_delta]
    simp_rw [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one ↗χ]
  simpa only [mul_convolution_distrib χ 1 ↗μ, this] using mul_delta _

/-- The Dirichlet character mod `0` corresponds to `δ`. -/
lemma modZero_eq_delta {χ : DirichletCharacter ℂ 0} : ↗χ = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [cast_zero, χ.map_nonunit not_isUnit_zero, delta, if_false]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp only [cast_one, map_one, delta, ↓reduceIte]
  have : ¬ IsUnit (n : ZMod 0) := fun h ↦ hn' <| ZMod.eq_one_of_isUnit_natCast h
  simp only [χ.map_nonunit this, delta, hn', ↓reduceIte]

/-- The Dirichlet character mod `1` corresponds to the constant function `1`. -/
lemma modOne_eq_one {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 1} :
    ((χ ·) : ℕ → R) = 1 := by
  ext
  rw [χ.level_one, MulChar.one_apply (isUnit_of_subsingleton _), Pi.one_apply]

lemma LSeries_modOne_eq : L ↗χ₁ = L 1 :=
  congr_arg L modOne_eq_one

/-- The L-series of a Dirichlet character mod `N > 0` does not converge absolutely at `s = 1`. -/
lemma not_LSeriesSummable_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    ¬ LSeriesSummable ↗χ 1 := by
  refine fun h ↦ (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m ↦ Set.indicator_apply_nonneg (fun _ ↦ by positivity))
    (fun n ↦ ?_)
  rw [norm_term_eq, one_re, Real.rpow_one, Set.indicator]
  split_ifs with h₁ h₂
  · rw [h₂, cast_zero, div_zero]
  · rw [h₁, χ.map_one, norm_one]
  all_goals positivity

/-- The L-series of a Dirichlet character converges absolutely at `s` if `re s > 1`. -/
lemma LSeriesSummable_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗χ s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ ↦ χ.norm_le_one _) hs

/-- The L-series of a Dirichlet character mod `N > 0` converges absolutely at `s` if and only if
`re s > 1`. -/
lemma LSeriesSummable_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
    LSeriesSummable ↗χ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_one_lt_re χ⟩
  by_contra! h
  exact not_LSeriesSummable_at_one hN χ <| LSeriesSummable.of_re_le_re (by simp only [one_re, h]) H

/-- The abscissa of absolute convergence of the L-series of a Dirichlet character mod `N > 0`
is `1`. -/
lemma absicssaOfAbsConv_eq_one {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv ↗χ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_iff hn χ, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

/-- The L-series of the twist of `f` by a Dirichlet character converges at `s` if the L-series
of `f` does. -/
lemma LSeriesSummable_mul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
  refine .of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ norm_term_le s ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) <| norm_le_one ..

open scoped ArithmeticFunction.Moebius in
/-- The L-series of a Dirichlet character `χ` and of the twist of `μ` by `χ` are multiplicative
inverses. -/
lemma LSeries.mul_mu_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : L ↗χ s * L (↗χ * ↗μ) s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hs) <|
          LSeriesSummable_mul χ <| ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs,
    convolution_mul_moebius, LSeries_delta, Pi.one_apply]


/-!
### L-series of Dirichlet characters do not vanish on re s > 1
-/

/-- The L-series of a Dirichlet character does not vanish on the right half-plane `re s > 1`. -/
lemma LSeries_ne_zero_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L ↗χ s ≠ 0 :=
  fun h ↦ by simpa only [h, zero_mul, zero_ne_one] using LSeries.mul_mu_eq_one χ hs

end DirichletCharacter


section zeta

/-!
### The L-series of the constant sequence 1 / the arithmetic function ζ

Both give the same L-series (since the difference in values at zero has no effect;
see `ArithmeticFunction.LSeries_zeta_eq`), which agrees with the Riemann zeta function
on `re s > 1`. We state most results in two versions, one for `1` and one for `↗ζ`.
-/

open LSeries Nat Complex DirichletCharacter

/-- The abscissa of (absolute) convergence of the constant sequence `1` is `1`. -/
lemma LSeries.abscissaOfAbsConv_one : abscissaOfAbsConv 1 = 1 :=
  modOne_eq_one (χ := χ₁) ▸ absicssaOfAbsConv_eq_one one_ne_zero χ₁

/-- The `LSeries` of the constant sequence `1` converges at `s` if and only if `re s > 1`. -/
theorem LSeriesSummable_one_iff {s : ℂ} : LSeriesSummable 1 s ↔ 1 < s.re :=
  modOne_eq_one (χ := χ₁) ▸ LSeriesSummable_iff one_ne_zero χ₁


namespace ArithmeticFunction

/-- The `LSeries` of the arithmetic function `ζ` is the same as the `LSeries` associated
to the constant sequence `1`. -/
lemma LSeries_zeta_eq : L ↗ζ = L 1 := by
  ext s
  exact (LSeries_congr s const_one_eq_zeta).symm

/-- The `LSeries` associated to the arithmetic function `ζ` converges at `s` if and only if
`re s > 1`. -/
theorem LSeriesSummable_zeta_iff {s : ℂ} : LSeriesSummable (ζ ·) s ↔ 1 < s.re :=
  (LSeriesSummable_congr s const_one_eq_zeta).symm.trans <| LSeriesSummable_one_iff
#align nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re ArithmeticFunction.LSeriesSummable_zeta_iff
-- deprecated 2024-03-29
@[deprecated] alias zeta_LSeriesSummable_iff_one_lt_re := LSeriesSummable_zeta_iff

/-- The abscissa of (absolute) convergence of the arithmetic function `ζ` is `1`. -/
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ↗ζ = 1 := by
  rw [abscissaOfAbsConv_congr (g := 1) fun hn ↦ by simp [hn], abscissaOfAbsConv_one]

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s := by
  simp only [LSeries, natCoe_apply, zeta_apply, cast_ite, cast_zero, cast_one,
    zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero]
  · simp only [term_of_ne_zero hn, hn, ↓reduceIte, one_div]

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeriesHasSum_zeta {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ↗ζ s (riemannZeta s) :=
  LSeries_zeta_eq_riemannZeta hs ▸ (LSeriesSummable_zeta_iff.mpr hs).LSeriesHasSum

/-- The L-series of the arithmetic function `ζ` and of the Möbius function are inverses. -/
lemma LSeries_zeta_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs)
    (LSeriesSummable_moebius_iff.mpr hs)]
  simp only [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius, one_eq_delta,
    LSeries_delta, Pi.one_apply]

/-- The L-series of the arithmetic function `ζ` does not vanish on the right half-plane
`re s > 1`. -/
lemma LSeries_zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : L ↗ζ s ≠ 0 :=
  fun h ↦ by simpa only [h, zero_mul, zero_ne_one] using LSeries_zeta_mul_Lseries_moebius hs

end ArithmeticFunction

open ArithmeticFunction

/-- The L-series of the constant sequence `1` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeries_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L 1 s = riemannZeta s :=
  LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs

/-- The L-series of the constant sequence `1` equals the Riemann zeta function on its
domain of convergence `1 < re s`. -/
lemma LSeriesHasSum_one {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum 1 s (riemannZeta s) :=
  LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable_one_iff.mpr hs).LSeriesHasSum

/-- The L-series of the constant sequence `1` and of the Möbius function are inverses. -/
lemma LSeries_one_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L 1 s * L ↗μ s = 1 :=
  LSeries_zeta_eq ▸ LSeries_zeta_mul_Lseries_moebius hs

/-- The L-series of the constant sequence `1` does not vanish on the right half-plane
`re s > 1`. -/
lemma LSeries_one_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : L 1 s ≠ 0 :=
  LSeries_zeta_eq ▸ LSeries_zeta_ne_zero_of_one_lt_re hs

/-- The Riemann Zeta Function does not vanish on the half-plane `re s > 1`. -/
lemma riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero_of_one_lt_re hs

end zeta


section vonMangoldt

/-!
### The L-series of the von Mangoldt function
-/

open LSeries Nat Complex ArithmeticFunction

namespace ArithmeticFunction

/-- A translation of the relation `Λ * ↑ζ = log` of (real-valued) arithmetic functions
to an equality of complex sequences. -/
lemma convolution_vonMangoldt_zeta : ↗Λ ⍟ ↗ζ = ↗Complex.log := by
  ext n
  simpa only [zeta_apply, apply_ite, cast_zero, cast_one, LSeries.convolution_def, mul_zero,
    mul_one, mul_apply, natCoe_apply, ofReal_sum, ofReal_zero, log_apply, ofReal_log n.cast_nonneg]
    using congr_arg (ofReal' <| · n) vonMangoldt_mul_zeta

lemma convolution_vonMangoldt_const_one : ↗Λ ⍟ 1 = ↗Complex.log :=
  (convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta

/-- The L-series of the von Mangoldt function `Λ` converges at `s` when `re s > 1`. -/
lemma LSeriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) : LSeriesSummable ↗Λ s := by
  have hf := LSeriesSummable_logMul_of_lt_re
    (show abscissaOfAbsConv 1 < s.re by rw [abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_term_le s ?_) hf
  have hΛ : ‖↗Λ n‖ ≤ ‖Complex.log n‖ := by
    simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg vonMangoldt_nonneg,
      ← Complex.natCast_log, _root_.abs_of_nonneg <| Real.log_natCast_nonneg n]
    exact ArithmeticFunction.vonMangoldt_le_log
  exact hΛ.trans <| by simp only [norm_eq_abs, norm_mul, Pi.one_apply, norm_one, mul_one, le_refl]

end ArithmeticFunction

namespace DirichletCharacter

/-- A twisted version of the relation `Λ * ↑ζ = log` in terms of complex sequences. -/
lemma convolution_twist_vonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (↗χ * ↗Λ) ⍟ ↗χ = ↗χ * ↗Complex.log := by
  rw [← convolution_vonMangoldt_const_one, ← χ.mul_convolution_distrib, mul_one]

/-- The L-series of the twist of the von Mangoldt function `Λ` by a Dirichlet character `χ`
converges at `s` when `re s > 1`. -/
lemma LSeriesSummable_twist_vonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (↗χ * ↗Λ) s :=
  LSeriesSummable_mul χ <| LSeriesSummable_vonMangoldt hs

/-- The L-series of the twist of the von Mangoldt function `Λ` by a Dirichlet character `χ` at `s`
equals the negative logarithmic derivative of the L-series of `χ` when `re s > 1`. -/
lemma LSeries_twist_vonMangoldt_eq {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s = - deriv (L ↗χ) s / L ↗χ s := by
  rcases eq_or_ne N 0 with rfl | hN
  · simpa only [modZero_eq_delta, delta_mul_eq_smul_delta, vonMangoldt_apply_one, ofReal_zero,
      zero_smul, LSeries_zero, Pi.zero_apply, LSeries_delta, Pi.one_apply, div_one, zero_eq_neg]
      using deriv_const s 1
  -- now `N ≠ 0`
  have hχ : LSeriesSummable ↗χ s := (LSeriesSummable_iff hN χ).mpr hs
  have hs' : abscissaOfAbsConv ↗χ < s.re := by
    rwa [absicssaOfAbsConv_eq_one hN, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  have hΛ : LSeriesSummable (↗χ * ↗Λ) s := LSeriesSummable_twist_vonMangoldt χ hs
  rw [eq_div_iff <| LSeries_ne_zero_of_one_lt_re χ hs, ← LSeries_convolution' hΛ hχ,
    convolution_twist_vonMangoldt, LSeries_deriv hs', neg_neg]
  exact LSeries_congr s fun _ ↦ by simp only [Pi.mul_apply, mul_comm, logMul]

end DirichletCharacter

namespace ArithmeticFunction

open DirichletCharacter in
/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the L-series of the constant sequence `1` on its domain of convergence `re s > 1`. -/
lemma LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) : L ↗Λ s = - deriv (L 1) s / L 1 s := by
  refine (LSeries_congr s fun {n} _ ↦ ?_).trans <|
    LSeries_modOne_eq ▸ LSeries_twist_vonMangoldt_eq χ₁ hs
  simp only [Subsingleton.eq_one (n : ZMod 1), map_one, Pi.mul_apply, one_mul]

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the Riemann zeta function on its domain of convergence `re s > 1`. -/
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s := by
  suffices deriv (L 1) s = deriv riemannZeta s by
    rw [LSeries_vonMangoldt_eq hs, ← LSeries_one_eq_riemannZeta hs, this]
  refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    fun _ ↦ LSeries_one_eq_riemannZeta⟩
