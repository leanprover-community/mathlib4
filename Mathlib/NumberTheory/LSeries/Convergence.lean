/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Convergence of L-series

We define `LSeries.abscissaOfAbsConv f` (as an `EReal`) to be the infimum
of all real numbers `x` such that the L-series of `f` converges for complex arguments with
real part `x` and provide some results about it.

## Tags

L-series, abscissa of convergence
-/

open Complex

/-- The abscissa `x : EReal` of absolute convergence of the L-series associated to `f`:
the series converges absolutely at `s` when `re s > x` and does not converge absolutely
when `re s < x`. -/
noncomputable def LSeries.abscissaOfAbsConv (f : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | LSeriesSummable f x}

lemma LSeries.abscissaOfAbsConv_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr x h

open Filter in
/-- If `f` and `g` agree on large `n : ℕ`, then their `LSeries` have the same
abscissa of absolute convergence. -/
lemma LSeries.abscissaOfAbsConv_congr' {f g : ℕ → ℂ} (h : f =ᶠ[atTop] g) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr' x h

open LSeries

lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) : LSeriesSummable f s := by
  obtain ⟨y, hy, hys⟩ : ∃ a : ℝ, LSeriesSummable f a ∧ a < s.re := by
    simpa [abscissaOfAbsConv, sInf_lt_iff] using hs
  exact hy.of_re_le_re <| ofReal_re y ▸ hys.le

lemma LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) :
    ∃ x : ℝ, x < s.re ∧ LSeriesSummable f x := by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  exact ⟨x, by simpa using hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩

lemma LSeriesSummable.abscissaOfAbsConv_le {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    abscissaOfAbsConv f ≤ s.re :=
  sInf_le <| by simpa using h.of_re_le_re (by simp)

lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : ℕ → ℂ} {x : ℝ}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  refine sInf_le_iff.mpr fun y hy ↦ le_of_forall_gt_imp_ge_of_dense fun a ↦ ?_
  replace hy : ∀ (a : ℝ), LSeriesSummable f a → y ≤ a := by simpa [mem_lowerBounds] using hy
  cases a with
  | coe a₀ => exact_mod_cast fun ha ↦ hy a₀ (h a₀ ha)
  | bot => simp
  | top => simp

lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : ℕ → ℂ} {x : EReal}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  cases x with
  | coe => exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable <| mod_cast h
  | top => exact le_top
  | bot =>
    refine le_of_eq <| sInf_eq_bot.mpr fun y hy ↦ ?_
    cases y with
    | bot => simp at hy
    | coe y => exact ⟨_, ⟨_, h _ <| EReal.bot_lt_coe _, rfl⟩, mod_cast sub_one_lt y⟩
    | top => exact ⟨_, ⟨_, h _ <| EReal.bot_lt_coe 0, rfl⟩, EReal.zero_lt_top⟩

/-- If `‖f n‖` is bounded by a constant times `n^x`, then the abscissa of absolute convergence
of `f` is bounded by `x + 1`. -/
lemma LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ}
    (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ x) : abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false

open Filter in
/-- If `‖f n‖` is `O(n^x)`, then the abscissa of absolute convergence
of `f` is bounded by `x + 1`. -/
lemma LSeries.abscissaOfAbsConv_le_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ}
    (h : f =O[atTop] fun n ↦ (n : ℝ) ^ x) :
    abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_isBigO_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false

/-- If `f` is bounded, then the abscissa of absolute convergence of `f` is bounded above by `1`. -/
lemma LSeries.abscissaOfAbsConv_le_of_le_const {f : ℕ → ℂ} (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C) :
    abscissaOfAbsConv f ≤ 1 := by
  simpa using abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) (by simpa using h)

open Filter in
/-- If `f` is `O(1)`, then the abscissa of absolute convergence of `f` is bounded above by `1`. -/
lemma LSeries.abscissaOfAbsConv_le_one_of_isBigO_one {f : ℕ → ℂ} (h : f =O[atTop] fun _ ↦ (1 : ℝ)) :
    abscissaOfAbsConv f ≤ 1 := by
  simpa using abscissaOfAbsConv_le_of_isBigO_rpow (x := 0) (by simpa using h)

/-- If `f` is real-valued and `x` is strictly greater than the abscissa of absolute convergence
of `f`, then the real series `∑' n, f n / n ^ x` converges. -/
lemma LSeries.summable_real_of_abscissaOfAbsConv_lt {f : ℕ → ℝ} {x : ℝ}
    (h : abscissaOfAbsConv (f ·) < x) :
    Summable fun n : ℕ ↦ f n / (n : ℝ) ^ x := by
  have aux : term (f ·) x = fun n ↦ ↑(if n = 0 then 0 else f n / (n : ℝ) ^ x) := by
    ext n
    simp [term_def, apply_ite ((↑) : ℝ → ℂ), ofReal_cpow n.cast_nonneg]
  have := LSeriesSummable_of_abscissaOfAbsConv_lt_re (ofReal_re x ▸ h)
  simp only [LSeriesSummable, aux, summable_ofReal] at this
  refine this.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
    using if_neg (by simpa using hn)

/-- If `F` is a binary operation on `ℕ → ℂ` with the property that the `LSeries` of `F f g`
converges whenever the `LSeries` of `f` and `g` do, then the abscissa of absolute convergence
of `F f g` is at most the maximum of the abscissa of absolute convergence of `f`
and that of `g`. -/
lemma LSeries.abscissaOfAbsConv_binop_le {F : (ℕ → ℂ) → (ℕ → ℂ) → (ℕ → ℂ)}
    (hF : ∀ {f g s}, LSeriesSummable f s → LSeriesSummable g s → LSeriesSummable (F f g) s)
    (f g : ℕ → ℂ) :
    abscissaOfAbsConv (F f g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun x hx ↦ hF ?_ ?_
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ (le_max_left ..).trans_lt hx
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ (le_max_right ..).trans_lt hx
