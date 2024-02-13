/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Data.Finset.LocallyFinite.Box
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

open Finset

/-!
# Uniform convergence of Eisenstein series

We show that `eis` converges locally uniformly on `ℍ` to the Eisenstein series `E` of weight `k`
and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.
-/

lemma fun_ne_zero_cases (x : Fin 2 → ℤ) : x ≠ 0 ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  rw [Function.ne_iff]; exact Fin.exists_fin_two

lemma mem_box_ne_zero_iff_ne_zero (n : ℕ) (x : Fin 2 → ℤ) (hx : (x 0, x 1) ∈ box n) :
    x ≠ 0 ↔ n ≠ 0 := by
  constructor
  intro h h0
  simp only [h0, Nat.cast_zero, box_zero, mem_singleton, Prod.ext_iff] at hx
  rw [fun_ne_zero_cases, hx.1, hx.2] at h
  · simp at h
  rintro hn rfl
  simp [hn, eq_comm] at hx

noncomputable section

open Complex Filter UpperHalfPlane Set

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

namespace EisensteinSeries

section bounding_functions

/-- Auxilary function used for bounding Eisentein series-/
def r1 (z : ℍ) : ℝ := ((z.im ^ (2 : ℕ)) / (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)))

lemma r1' (z : ℍ) : r1 z = 1/((z.re / z.im) ^ (2 : ℕ) + 1) := by
  field_simp [r1, im_pos z]

theorem r1_pos (z : ℍ) : 0 < r1 z := by
  have H2 : 0 < (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)) := by
    apply_rules [pow_pos, add_pos_of_nonneg_of_pos, pow_two_nonneg, z.2]
  exact div_pos (pow_pos z.im_pos 2) H2

/-- This function is used to give an upper bound on Eisenstein series-/
def r (z : ℍ) : ℝ := min (z.im) (Real.sqrt (r1 z))

theorem r_pos (z : ℍ) : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

theorem r1_bound (z : ℍ) (δ : ℝ) {ε : ℝ} (hε : 1 ≤ ε^2) :
    (z.im ^ 2 ) / (z.re ^ 2 + z.im ^ 2) ≤ (δ * z.re + ε) ^ 2 + (δ * z.im) ^ 2 := by
  have H1 : (δ * z.re + ε) ^ 2 + (δ * z.im) ^ 2 =
        δ ^ 2 * (z.re ^ 2 + z.im ^ 2) + ε * 2 * δ * z.re + ε^2 := by ring
  have H4 : (δ ^ 2 * (z.re ^ 2 + z.im ^ 2) + ε * 2 * δ * z.re + ε^2) * (z.re ^ 2 + z.im ^ 2)
    - (z.im ^ 2) = (δ * (z.re ^ 2 + z.im ^ 2)+ ε * z.re)^2 + (ε^2 - 1)* (z.im)^2 := by ring
  rw [H1, div_le_iff, ← sub_nonneg, H4]
  · apply add_nonneg (pow_two_nonneg _) ?_
    apply mul_nonneg
    linarith
    apply pow_two_nonneg
  · apply_rules [add_pos_of_nonneg_of_pos, pow_two_nonneg, (pow_pos z.im_pos 2)]

theorem auxbound1 (z : ℍ) {δ : ℝ} (ε : ℝ) (hδ : 1 ≤ δ^2) : r z ≤ Complex.abs (δ * (z : ℂ) + ε) := by
  rw [r, Complex.abs]
  have H1 : (z : ℂ).im ≤
    Real.sqrt ((δ * (z : ℂ).re + ε) * (δ * (z : ℂ).re + ε) + (δ * z : ℂ).im * (δ * z : ℂ).im) := by
    have h1 : (δ * z : ℂ).im * (δ * z : ℂ).im = δ^2 * (z : ℂ).im * (z : ℂ).im := by
      simp only [mul_im, ofReal_re, coe_im, ofReal_im, coe_re, zero_mul, add_zero]
      ring
    rw [Real.le_sqrt', h1 ]
    nlinarith
    exact z.2
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, AbsoluteValue.coe_mk, MulHom.coe_mk,
    min_le_iff] at *
  left
  simp only [one_le_sq_iff_one_le_abs, mul_im, ofReal_re, coe_im, ofReal_im, coe_re, zero_mul,
    add_zero, normSq_apply, add_re, mul_re, sub_zero, add_im] at *
  exact H1

theorem auxbound2 (z : ℍ) (δ : ℝ) {ε : ℝ} (hε : 1 ≤ ε^2) : r z ≤ Complex.abs (δ * (z : ℂ) + ε) := by
  rw [r, Complex.abs, min_le_iff]
  have H1 : Real.sqrt (r1 z) ≤ Real.sqrt ((δ * (z : ℂ).re + ε) * (δ * (z : ℂ).re + ε ) +
      δ * (z : ℂ).im * (δ * (z : ℂ).im)) := by
    rw [r1, Real.sqrt_le_sqrt_iff, ← pow_two, ← pow_two]
    apply r1_bound z δ hε
    nlinarith
  right
  simp only [ne_eq, coe_re, coe_im, normSq_apply, AbsoluteValue.coe_mk, MulHom.coe_mk, add_re,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, int_cast_re, add_im, mul_im, add_zero,
    int_cast_im] at *
  exact H1

lemma ne_zero_if_max {x : Fin 2 → ℤ} (hx : x ≠ 0)
    (h : (max (x 0).natAbs (x 1).natAbs) = (x 0).natAbs) : (x 0) ≠ 0 := by
  intro h0
  rw [h0] at h
  simp only [ne_eq, Int.natAbs_zero, ge_iff_le, zero_le, max_eq_right, Int.natAbs_eq_zero] at *
  have : x = ![x 0, x 1] := List.ofFn_inj.mp rfl
  rw [h0, h] at this
  simp only [this, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self, not_true_eq_false] at hx

lemma ne_zero_if_max' {x : Fin 2 → ℤ} (hx : x ≠ 0)
    (h : (max (x 0).natAbs (x 1).natAbs) = (x 1).natAbs) : (x 1) ≠ 0 := by
  apply ne_zero_if_max (x :=![x 1, x 0]) ?_ (by simpa using h)
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and]
  intro h1 h0
  rw [fun_ne_zero_cases, h1, h0] at hx
  simp only [ne_eq, not_true_eq_false, or_self] at *

lemma div_max_sq_ge_one (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    (1 : ℝ) ≤ (x 0 / (max (x 0).natAbs (x 1).natAbs))^2 ∨
      (1 : ℝ) ≤ (x 1 / (max (x 0).natAbs (x 1).natAbs))^2 := by
  cases' (max_choice (x 0).natAbs (x 1).natAbs) with H1 H2
  · left
    rw [H1]
    have : (x 0 : ℝ) ≠ 0 := by
      simpa using (ne_zero_if_max hx H1)
    have h1 := one_le_sq_div_abs_sq this
    simp only [ne_eq, max_eq_left_iff, Int.cast_eq_zero, int_cast_abs, div_pow, ge_iff_le] at *
    convert h1
    norm_cast
    rw [complex_abs_of_int_eq_natAbs]
  · right
    rw [H2]
    have : (x 1 : ℝ) ≠ 0 := by
      simpa using (ne_zero_if_max' hx H2)
    have h1 := one_le_sq_div_abs_sq this
    simp only [ne_eq, max_eq_right_iff, Int.cast_eq_zero, int_cast_abs, div_pow, ge_iff_le] at *
    convert h1
    norm_cast
    rw [complex_abs_of_int_eq_natAbs]

/-This should work for complex `k` (with a condition on `k.re`) but last I checked we were missing
some lemmas about this -/
lemma bound (z : ℍ) (x : Fin 2 → ℤ) (hx : x ≠ 0) (k : ℕ) :
    ((r z) ^ k) * (max (x 0).natAbs (x 1).natAbs)^k ≤
      Complex.abs (((x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ)) ^ k) := by
  by_cases hk : k ≠ 0
  · let n := max (x 0).natAbs (x 1).natAbs
    have h1 : ((n : ℝ) : ℂ)^k ≠ 0 := by
      rw [pow_ne_zero_iff hk]
      norm_cast
      rw [mem_box_ne_zero_iff_ne_zero n x (by rw [Int.mem_box])] at hx
      exact hx
    have hc : Complex.abs ((n : ℝ)^k : ℂ) = n^k := by
      simp only [Nat.cast_max, map_pow, abs_ofReal, ge_iff_le, abs_nonneg, le_max_iff,
        Nat.cast_nonneg, or_self]
      congr
      simp only [abs_eq_self, le_max_iff, Nat.cast_nonneg, or_self]
    have h11 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
      (((x 0 : ℝ) / (n : ℝ) ) * (z : ℂ) + (x 1 : ℝ) /(n : ℝ)) ^ (k : ℤ) * ((n : ℝ)^ (k : ℤ)) := by
      simp only [Nat.cast_max] at h1
      field_simp
    cases' (div_max_sq_ge_one x hx) with H1 H2
    · norm_cast at *
      rw [h11]
      simp only [hc, map_pow, map_mul, abs_ofReal, Complex.abs_abs, ge_iff_le, zpow_coe_nat] at *
      apply mul_le_mul ?_ (by rfl)
      simp only [Nat.cast_pow, Nat.cast_max, ge_iff_le, le_max_iff, Nat.cast_nonneg, or_self,
        pow_nonneg]
      apply pow_nonneg (Complex.abs.nonneg _) k
      apply pow_le_pow_left (r_pos _).le (auxbound1 z (x 1 / n) H1)
    · norm_cast at *
      rw [h11]
      simp only [hc, map_pow, map_mul, abs_ofReal, Complex.abs_abs, ge_iff_le, zpow_coe_nat] at *
      apply mul_le_mul ?_ (by rfl)
      simp only [Nat.cast_pow, Nat.cast_max, ge_iff_le, le_max_iff, Nat.cast_nonneg, or_self,
        pow_nonneg]
      apply pow_nonneg (Complex.abs.nonneg _) k
      apply pow_le_pow_left (r_pos _).le (auxbound2 z (x 0 / n) H2)
  · simp only [ne_eq, not_not] at hk
    simp only [hk, pow_zero, Nat.cast_max, mul_one, map_one, le_refl]

theorem eis_is_bounded_on_box (k : ℕ) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ)
    (hx : (⟨x 0, x 1⟩ : ℤ × ℤ) ∈ box n) : (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ k))⁻¹ ≤
      (Complex.abs ((r z) ^ k * n ^ k))⁻¹ := by
  by_cases hn : n = 0
  · rw [hn] at hx
    simp only [box_zero, Finset.mem_singleton, Prod.mk_eq_zero] at hx
    by_cases hk : k = 0
    rw [hk] at *
    simp only [ pow_zero, map_one, inv_one, mul_one, le_refl]
    rw [hx.1, hx.2]
    have h1 : (0 : ℝ) ^ (k : ℕ) = 0 := by
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact hk
    simp only [Int.cast_zero, zero_mul, add_zero, map_pow, map_zero, h1, inv_zero, hn,
      CharP.cast_eq_zero, map_mul, abs_ofReal, mul_zero, le_refl]
  · have hx2 : x ≠ 0 := by
      rw [mem_box_ne_zero_iff_ne_zero n x hx]
      exact hn
    simp only [Int.mem_box] at hx
    rw [inv_le_inv]
    simp only [← hx, map_mul, map_pow, abs_ofReal, abs_natCast, Nat.cast_max, ge_iff_le]
    convert (bound z x hx2 k)
    apply abs_eq_self.mpr ((r_pos z).le )
    simp only [Nat.cast_max]
    simp only [map_pow]
    apply Complex.abs.pos (pow_ne_zero k (linear_ne_zero ![x 0, x 1] z ?_))
    simp only [ne_eq, Matrix.cons_eq_zero_iff, Int.cast_eq_zero, Matrix.zero_empty, and_true,
      not_and] at *
    intro hg h1
    have : x = ![x 0, x 1] := by
      exact List.ofFn_inj.mp rfl
    rw [this, hg,h1 ] at hx2
    simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self, not_true_eq_false] at *
    have := r_pos z
    apply Complex.abs.pos
    norm_cast
    positivity

lemma r_lower_bound_on_slice {A B : ℝ} (h : 0 < B) (z : upperHalfPlaneSlice A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z.1 := by
  have hz := z.2
  simp only [slice_mem_iff, abs_ofReal, ge_iff_le] at hz
  simp_rw [r]
  apply min_le_min
  · dsimp only
    convert hz.2
    have := abs_eq_self.mpr (UpperHalfPlane.im_pos z.1).le
    convert this.symm
  rw [Real.sqrt_le_sqrt_iff]
  simp only [r1', div_pow, one_div]
  rw [inv_le_inv, add_le_add_iff_right]
  apply div_le_div (sq_nonneg _)
  · simpa [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2
  · positivity
  · simpa [even_two.pow_abs] using pow_le_pow_left h.le hz.2 2
  · positivity
  · positivity
  · apply (r1_pos z).le

end bounding_functions

section summability

lemma summable_lemma (f : (Fin 2 → ℤ) → ℝ) (h : ∀ y : (Fin 2 → ℤ), 0 ≤ f y)
    (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ ι i) :
      Summable f ↔ Summable fun n : ℕ => ∑ x in ι n, f ![x.1, x.2] := by
  let h2 := Equiv.trans (Equiv.sigmaEquiv ι HI) (piFinTwoEquiv fun _ => ℤ).symm
  have h22 : ∀ y : Σ s : ℕ, (ι s), 0 ≤ (f ∘ h2) y := by
    intro y
    apply h
  have h4 : Summable f ↔ Summable (f ∘ h2) := by rw [Equiv.summable_iff]
  rw [h4, summable_sigma_of_nonneg h22]
  constructor
  · intro H
    convert H.2
    rw [← Finset.tsum_subtype]
    rfl
  · intro H
    constructor
    · intro x
      simp only [Finset.coe_sort_coe, Equiv.coe_trans, Function.comp_apply, Equiv.sigmaEquiv]
      convert (Finset.summable (ι x) (f ∘ (piFinTwoEquiv fun _ => ℤ).symm))
    · convert H
      rw [← Finset.tsum_subtype]
      rfl

lemma summable_r_pow {k : ℤ} (z : ℍ) (h : 3 ≤ k) :
    Summable fun n : ℕ => 8 / (r z) ^ k * ((n : ℝ) ^ (k - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by
    norm_cast at *
    linarith
  have nze : (8 / (r z) ^ k : ℝ) ≠ 0 := by
    apply div_ne_zero
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    apply zpow_ne_zero k (ne_of_gt (r_pos z))
  rw [← (summable_mul_left_iff nze).symm]
  convert (Real.summable_nat_rpow_inv.2 hk)
  norm_cast

lemma summable_over_box {k : ℤ} (z : ℍ) (h : 3 ≤ k):
    Summable (fun n : ℕ => ∑ v in (box n : Finset (ℤ × ℤ)), (1 / (r z) ^ k) * ((n : ℝ) ^ k)⁻¹) := by
  simp only [one_div, Finset.sum_const, nsmul_eq_mul]
  apply Summable.congr (summable_r_pow z h)
  intro b
  by_cases b0 : b = 0
  · rw [b0]
    have hk0 : k ≠ 0 := by linarith
    have hk1 : k - 1 ≠ 0 := by linarith
    norm_cast
    rw [zero_zpow k hk0, zero_zpow (k - 1) hk1]
    simp only [inv_zero, mul_zero, box_zero, Finset.card_singleton, Nat.cast_one]
  · rw [Int.card_box b0, zpow_sub_one₀ (a:= ( b: ℝ)) (Nat.cast_ne_zero.mpr b0) k]
    simp only [mul_inv_rev, inv_inv, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf

lemma summable_upper_bound {k : ℤ} (h : 3 ≤ k) (z : ℍ) : Summable fun (x : Fin 2 → ℤ) =>
    (1 / (r z) ^ k) * ((max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹ := by
  rw [summable_lemma _ _ (fun (n : ℕ) => box n) Int.existsUnique_mem_box]
  · have : ∀ n : ℕ, ∑ v in (box n : Finset (ℤ × ℤ)),
      (1 / (r z) ^ k) * ((max v.1.natAbs v.2.natAbs: ℝ) ^ k)⁻¹ =
        ∑ v in box n, (1 / (r z) ^ k) * ((n : ℝ)^k)⁻¹ := by
      intro n
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Int.mem_box] at hx
      congr
      norm_cast
    apply Summable.congr (summable_over_box z h)
    intro b
    apply (this b).symm
  · intro y
    apply mul_nonneg
    · simp only [one_div, inv_nonneg]
      apply zpow_nonneg (r_pos z).le
    · simp only [inv_nonneg, ge_iff_le, le_max_iff, Nat.cast_nonneg, or_self, zpow_nonneg]

end summability

theorem eisensteinSeries_TendstoLocallyUniformlyOn {k : ℤ} (hk : 3 ≤ k) (N : ℕ)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
      (fun (z : ℍ) => ∑ x in s, eisSummand k x z))
        ( fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) Filter.atTop ⊤ := by
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact, eisensteinSeries_SIF]
  simp only [Set.top_eq_univ, Set.subset_univ, eisensteinSeries, forall_true_left]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩:= subset_slice_of_isCompact hK
  have hu : Summable fun x : (gammaSet N a ) =>
    (1/(r ⟨⟨A, B⟩, hB⟩) ^ k) * ((max (x.1 0).natAbs (x.1 1).natAbs : ℝ) ^ k)⁻¹ := by
    apply (Summable.subtype (summable_upper_bound hk ⟨⟨A, B⟩, hB⟩) (gammaSet N a )).congr
    intro v
    simp only [zpow_coe_nat, one_div, Function.comp_apply]
  apply tendstoUniformlyOn_tsum hu
  intro v x hx
  have := eis_is_bounded_on_box k x (max (v.1 0).natAbs (v.1 1).natAbs ) v
  simp only [Nat.cast_max, Int.coe_natAbs, iff_true, zpow_coe_nat, one_div, map_pow,
    map_mul, abs_ofReal, abs_natCast, mul_inv_rev, eisSummand, norm_inv, norm_pow, norm_eq_abs,
    ge_iff_le] at *
  apply le_trans (this ?_)
  rw [mul_comm]
  apply mul_le_mul _ (by rfl)
  repeat {simp only [inv_nonneg, ge_iff_le, le_max_iff, Nat.cast_nonneg, or_self, pow_nonneg,
    inv_nonneg, pow_nonneg (r_pos _).le]}
  rw [inv_le_inv]
  apply pow_le_pow_left (r_pos _).le
  rw [abs_of_pos (r_pos _)]
  · exact r_lower_bound_on_slice hB ⟨x, HABK hx⟩
  · apply pow_pos (abs_pos.mpr (ne_of_gt (r_pos x)))
  · apply pow_pos (r_pos _)
  · simp only [Int.mem_box]
  · simp only [Set.top_eq_univ, isOpen_univ]
