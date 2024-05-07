/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Order.Interval.Finset.Box
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# Uniform convergence of Eisenstein series

We show that the sum of `eisSummand` converges locally uniformly on `ℍ` to the Eisenstein series
of weight `k` and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.
-/

noncomputable section

open Complex UpperHalfPlane Set Finset

open scoped BigOperators Matrix UpperHalfPlane Complex

namespace EisensteinSeries

section bounding_functions

/-- Auxiliary function used for bounding Eisenstein series. -/
def r1 (z : ℍ) : ℝ := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

lemma r1' (z : ℍ) : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  field_simp [r1, im_pos z]

theorem r1_pos (z : ℍ) : 0 < r1 z := by
  dsimp only [r1]
  positivity

/-- This function is used to give an upper bound on Eisenstein series. -/
def r (z : ℍ) : ℝ := min z.im (Real.sqrt (r1 z))

lemma r_pos (z : ℍ) : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

lemma r1_aux_bound (z : ℍ) (δ : ℝ) {ε : ℝ} (hε : 1 ≤ ε^2) :
    (z.im ^ 2) / (z.re ^ 2 + z.im ^ 2) ≤ (δ * z.re + ε) ^ 2 + (δ * z.im) ^ 2 := by
  have H1 : (δ * z.re + ε) ^ 2 + (δ * z.im) ^ 2 =
        δ ^ 2 * (z.re ^ 2 + z.im ^ 2) + ε * 2 * δ * z.re + ε^2 := by ring
  have H2 : (δ ^ 2 * (z.re ^ 2 + z.im ^ 2) + ε * 2 * δ * z.re + ε^2) * (z.re ^ 2 + z.im ^ 2)
    - (z.im ^ 2) = (δ * (z.re ^ 2 + z.im ^ 2)+ ε * z.re)^2 + (ε^2 - 1)* (z.im)^2 := by ring
  rw [H1, div_le_iff, ← sub_nonneg, H2]
  · apply add_nonneg (pow_two_nonneg _) ?_
    apply mul_nonneg
    · linarith
    · apply pow_two_nonneg
  · positivity

lemma auxbound1 (z : ℍ) {δ : ℝ} (ε : ℝ) (hδ : 1 ≤ δ ^ 2) : r z ≤ Complex.abs (δ * (z : ℂ) + ε) := by
  rw [r, Complex.abs]
  have H1 : (z : ℂ).im ≤
    Real.sqrt ((δ * (z : ℂ).re + ε) * (δ * (z : ℂ).re + ε) + (δ * z : ℂ).im * (δ * z : ℂ).im) := by
    have h1 : (δ * z : ℂ).im * (δ * z : ℂ).im = δ ^ 2 * (z : ℂ).im * (z : ℂ).im := by
      simp only [mul_im, ofReal_re, coe_im, ofReal_im, coe_re, zero_mul, add_zero]
      ring
    rw [Real.le_sqrt', h1]
    · nlinarith
    · exact z.2
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, AbsoluteValue.coe_mk, MulHom.coe_mk,
    min_le_iff] at *
  left
  simp only [one_le_sq_iff_one_le_abs, mul_im, ofReal_re, coe_im, ofReal_im, coe_re, zero_mul,
    add_zero, normSq_apply, add_re, mul_re, sub_zero, add_im] at *
  exact H1

lemma auxbound2 (z : ℍ) (δ : ℝ) {ε : ℝ} (hε : 1 ≤ ε ^ 2) : r z ≤ Complex.abs (δ * (z : ℂ) + ε) := by
  rw [r, Complex.abs, min_le_iff]
  have H1 : Real.sqrt (r1 z) ≤ Real.sqrt ((δ * (z : ℂ).re + ε) * (δ * (z : ℂ).re + ε) +
      δ * (z : ℂ).im * (δ * (z : ℂ).im)) := by
    rw [r1, Real.sqrt_le_sqrt_iff, ← pow_two, ← pow_two]
    apply r1_aux_bound z δ hε
    nlinarith
  right
  simp only [ne_eq, coe_re, coe_im, normSq_apply, AbsoluteValue.coe_mk, MulHom.coe_mk, add_re,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_im, mul_im, add_zero] at *
  exact H1

lemma ne_zero_if_max {x : Fin 2 → ℤ} (hx : x ≠ 0)
    (h : max (x 0).natAbs (x 1).natAbs = (x 0).natAbs) : x 0 ≠ 0 := by
  contrapose! hx
  ext x
  fin_cases x <;> aesop

/-This proof is faster than the one above, but longer. -/
lemma ne_zero_if_max' {x : Fin 2 → ℤ} (hx : x ≠ 0)
    (h : (max (x 0).natAbs (x 1).natAbs) = (x 1).natAbs) : (x 1) ≠ 0 := by
  apply ne_zero_if_max (x := ![x 1, x 0]) ?_ (by simpa only [Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, max_eq_left_iff, max_eq_right_iff] using h)
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and]
  intro h1 h0
  rw [Function.ne_iff, Fin.exists_fin_two, h1, h0] at hx
  simp only [Pi.zero_apply, ne_eq, not_true_eq_false, or_self] at *

lemma div_max_sq_ge_one (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    (1 : ℝ) ≤ (x 0 / (max (x 0).natAbs (x 1).natAbs)) ^ 2 ∨
      (1 : ℝ) ≤ (x 1 / (max (x 0).natAbs (x 1).natAbs)) ^ 2 := by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H1 => ?_) (fun H2 => ?_)
  · simp only [Fin.isValue, H1, Int.cast_natAbs, Int.cast_abs, div_pow, _root_.sq_abs, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, ne_zero_if_max hx H1,
    div_self, le_refl]
  · simp only [Fin.isValue, H2, Int.cast_natAbs, Int.cast_abs, div_pow, _root_.sq_abs, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero,
    ne_zero_if_max' hx H2, div_self, le_refl]

lemma rpow_bound {k : ℝ} (hk : 0 ≤ k) (z : ℍ) (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    ((r z) ^ k) * (max (x 0).natAbs (x 1).natAbs) ^ k ≤
      (Complex.abs ((x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ))) ^ k := by
  by_cases hk0 : k ≠ 0
  · let n := max (x 0).natAbs (x 1).natAbs
    have hn0 : n ≠ 0 := by
      rw [← Iff.ne ((eq_zero_iff_eq_zero_of_mem_box (α := ℤ × ℤ) (x := ((x 0, x 1)))) (by simp)),
        ← Iff.ne (Function.Injective.eq_iff (Equiv.injective (piFinTwoEquiv fun _ ↦ ℤ)))] at *
      simpa only [Fin.isValue, ne_eq, Prod.mk_eq_zero, not_and, piFinTwoEquiv_apply, Pi.zero_apply,
        Prod.mk.injEq] using hx
    have h11 : ((x 0) * ↑z + (x 1)) =
        (((x 0 : ℝ) / (n : ℝ)) * (z : ℂ) + (x 1 : ℝ) / (n : ℝ)) * ((n : ℝ)) := by
        have : (n : ℂ) ≠ 0 := by norm_cast
        field_simp [this]
    simp only [Nat.cast_max, h11, map_mul, abs_ofReal, ge_iff_le]
    rw [Real.mul_rpow (by apply apply_nonneg) (by apply abs_nonneg)]
    cases' (div_max_sq_ge_one x hx) with H1 H2
    · apply mul_le_mul _ (by norm_cast) _ (by apply Real.rpow_nonneg (Complex.abs.nonneg _) k)
      · simpa only [Fin.isValue, ofReal_intCast, Nat.cast_max, ofReal_div, n] using
        (Real.rpow_le_rpow (r_pos _).le (auxbound1 z (x 1 / n) H1) hk)
      · positivity
    · apply mul_le_mul _ (by norm_cast) _ (by apply Real.rpow_nonneg (Complex.abs.nonneg _) k)
      · simpa only [Fin.isValue, ofReal_intCast, Nat.cast_max, ofReal_div, n] using
        (Real.rpow_le_rpow (r_pos _).le (auxbound2 z (x 0 / n) H2) hk)
      · positivity
  · simp only [ne_eq, not_not] at hk0
    simp only [hk0, Real.rpow_zero, Nat.cast_max, mul_one, le_refl]

theorem summand_is_bounded_on_box_rpow {k : ℝ} (hk : 0 ≤ k) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ)
    (hx : (x 0, x 1) ∈ box n) : (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)))) ^ (-k) ≤
      (r z) ^ (-k) * n ^ (-k) := by
  by_cases hn : n = 0
  · simp only [hn, box_zero, Finset.mem_singleton, Prod.mk_eq_zero] at hx
    rw [hx.1, hx.2] at *
    by_cases hk0 : k = 0
    · simp only [hk0, neg_zero, Real.rpow_zero, mul_one, le_refl]
    · simp only [Int.cast_zero, zero_mul, add_zero, map_zero]
      have h1 : (0 : ℝ) ^ (-k) = 0 := by
        rw [Real.rpow_eq_zero_iff_of_nonneg (by rfl)]
        simp only [ne_eq, neg_eq_zero, hk0, not_false_eq_true, and_self]
      simp only [h1, hn, CharP.cast_eq_zero, mul_zero, le_refl]
  · have hx2 : x ≠ 0 := by
      rw [← Iff.ne (Function.Injective.eq_iff (Equiv.injective (piFinTwoEquiv fun _ ↦ ℤ)))]
      simpa only [piFinTwoEquiv_apply, Fin.isValue, Pi.zero_apply, ne_eq, Prod.mk.injEq, not_and,
        Prod.mk_eq_zero] using
        (Iff.ne ((eq_zero_iff_eq_zero_of_mem_box (x := (x 0, x 1))) hx)).mpr hn
    simp only [Int.mem_box] at hx
    rw [Real.rpow_neg (by apply apply_nonneg), Real.rpow_neg ((r_pos z).le),
      Real.rpow_neg (Nat.cast_nonneg n), ← mul_inv, inv_le_inv]
    simp only [← hx, Nat.cast_max]
    convert (rpow_bound hk z x hx2)
    · simp only [Nat.cast_max]
    · apply Real.rpow_pos_of_pos
      apply Complex.abs.pos (linear_ne_zero ![x 0, x 1] z ?_)
      have := (Function.comp_ne_zero_iff x Int.cast_injective Int.cast_zero (γ := ℝ)).mpr hx2
      rw [← Iff.ne (Function.Injective.eq_iff (Equiv.injective (piFinTwoEquiv fun _ ↦ ℝ)))] at this
      simpa only [Fin.isValue, ne_eq, Matrix.cons_eq_zero_iff, Int.cast_eq_zero, Matrix.zero_empty,
        and_true, not_and, piFinTwoEquiv_apply, Function.comp_apply, Pi.zero_apply,
        Prod.mk.injEq] using this
    · apply mul_pos (Real.rpow_pos_of_pos (r_pos z) _)
      apply Real.rpow_pos_of_pos
      norm_cast
      exact Nat.pos_of_ne_zero hn

/-This is a special case of the above, but one that we use more. -/
theorem eisSummand_is_bounded_on_box {k: ℤ} (n : ℕ) (z : ℍ) (x : Fin 2 → ℤ) (hk : 0 ≤ k)
    (hx : (x 0, x 1) ∈ box n) : Complex.abs (eisSummand k x z) ≤ (((r z) ^ k * n ^ k))⁻¹ := by
  have := summand_is_bounded_on_box_rpow (Int.cast_nonneg.2 hk) z n x hx
  norm_cast at *
  rw [zpow_neg, mul_inv, eisSummand] at *
  simpa only [Fin.isValue, one_div, map_inv₀, map_zpow₀, ge_iff_le, zpow_neg] using this

lemma r_lower_bound_on_verticalStrip {A B : ℝ} (h : 0 < B) (z : verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z.1 := by
  have hz := z.2
  simp only [mem_verticalStrip_iff, abs_ofReal, ge_iff_le] at hz
  rw [r]
  apply min_le_min
  · convert hz.2
  · rw [Real.sqrt_le_sqrt_iff (by apply (r1_pos z).le)]
    simp only [r1', div_pow, one_div]
    rw [inv_le_inv (by positivity) (by positivity), add_le_add_iff_right]
    apply div_le_div (sq_nonneg _) _ (by positivity)
    · simpa only using pow_le_pow_left h.le hz.2 2
    · simpa only [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2

end bounding_functions

section summability

lemma summable_r_pow {k : ℤ} (z : ℍ) (h : 3 ≤ k) :
    Summable fun n : ℕ => 8 / (r z) ^ k * ((n : ℝ) ^ (k - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by norm_cast; linarith
  have nze : (8 / (r z) ^ k : ℝ) ≠ 0 := by
    apply div_ne_zero
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    apply zpow_ne_zero k (ne_of_gt (r_pos z))
  rw [← (summable_mul_left_iff nze).symm]
  convert (Real.summable_nat_rpow_inv.2 hk)
  norm_cast

lemma summable_over_box {k : ℤ} (z : ℍ) (h : 3 ≤ k):
    Summable (fun n : ℕ => ∑ v in (box n : Finset (ℤ × ℤ)), (1 / (r z) ^ k) * ((n : ℝ) ^ k)⁻¹) := by
  simp only [one_div, sum_const, nsmul_eq_mul]
  apply Summable.congr (summable_r_pow z h)
  intro b
  by_cases b0 : b = 0
  · simp only [b0, CharP.cast_eq_zero, box_zero, Finset.card_singleton, Nat.cast_one, one_mul]
    rw [zero_zpow k (by linarith), zero_zpow (k - 1) (by linarith)]
    simp only [inv_zero, mul_zero]
  · rw [Int.card_box b0, zpow_sub_one₀ (a:= (b: ℝ)) (Nat.cast_ne_zero.mpr b0) k]
    simp only [mul_inv_rev, inv_inv, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf

lemma summable_upper_bound {k : ℤ} (h : 3 ≤ k) (z : ℍ) : Summable fun (x : Fin 2 → ℤ) =>
    (((r z) ^ k) * (max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹ := by
  set f := fun x : Fin 2 → ℤ ↦ (((r z) ^ k) * (max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹
  rw [← (piFinTwoEquiv _).symm.summable_iff,
    summable_partition _ (s := fun n ↦ (box n : Finset (ℤ × ℤ))) Int.existsUnique_mem_box]
  · simp_rw [coe_sort_coe, Finset.tsum_subtype]
    simp only [one_div, piFinTwoEquiv_symm_apply, Function.comp_apply, Fin.cons_zero, Fin.cons_one]
    refine ⟨fun n ↦ ?_, Summable.congr (summable_over_box z h) fun n ↦ Finset.sum_congr rfl
      fun x hx ↦ ?_⟩
    · simpa using (box n).summable (f ∘ (piFinTwoEquiv _).symm)
    · simp only [Int.mem_box, one_div] at *
      simp only [← hx, Nat.cast_max, Fin.isValue, mul_inv_rev, Fin.cons_zero, Fin.cons_one, f]
      rw [mul_comm]
  · intro y
    simp only [Pi.zero_apply, Fin.isValue, mul_inv_rev, piFinTwoEquiv_symm_apply,
      Function.comp_apply, Fin.cons_zero, Fin.cons_one, f]
    apply mul_nonneg
    · simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, inv_nonneg, ge_iff_le,
      le_max_iff, Nat.cast_nonneg, or_self, zpow_nonneg]
    · simp only [one_div, inv_nonneg]
      apply zpow_nonneg (r_pos z).le

end summability

theorem eisensteinSeries_tendstoLocallyUniformly {k : ℤ} (hk : 3 ≤ k) (N : ℕ)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformly (fun (s : Finset (gammaSet N a)) =>
      (fun (z : ℍ) => ∑ x in s, eisSummand k x z))
        (fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) Filter.atTop := by
  rw [← tendstoLocallyUniformlyOn_univ,tendstoLocallyUniformlyOn_iff_forall_isCompact
    (by simp only [Set.top_eq_univ, isOpen_univ]), eisensteinSeries_SIF]
  simp only [Set.top_eq_univ, Set.subset_univ, eisensteinSeries, forall_true_left]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  have hu : Summable fun x : (gammaSet N a) =>
    (((r ⟨⟨A, B⟩, hB⟩) ^ k) * (max (x.1 0).natAbs (x.1 1).natAbs : ℝ) ^ k)⁻¹ := by
    apply (Summable.subtype (summable_upper_bound hk ⟨⟨A, B⟩, hB⟩) (gammaSet N a)).congr
    intro v
    simp only [zpow_natCast, one_div, Function.comp_apply]
  apply tendstoUniformlyOn_tsum hu
  intro v x hx
  apply le_trans (eisSummand_is_bounded_on_box (k := k) (max (v.1 0).natAbs (v.1 1).natAbs) x v
    (by linarith) (by simp only [Int.mem_box]))
  simp  [Fin.isValue, Nat.cast_max, mul_inv_rev, one_div]
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  gcongr
  · apply pow_pos (r_pos _)
  · apply (r_pos _).le
  · apply (r_lower_bound_on_verticalStrip hB ⟨x, HABK hx⟩)

local notation "↑ₕ" f => f ∘ (PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))

/- A version for the extension to maps `ℂ → ℂ` that is nice to have for holomorphicity later. -/
lemma eisensteinSeries_tendstoLocallyUniformlyOn {k : ℤ} {N : ℕ} (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z )) (↑ₕ(eisensteinSeries_SIF a k).toFun)
          Filter.atTop (UpperHalfPlane.coe '' ⊤) := by
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (PartialHomeomorph.continuousOn_symm _)
  · simp only [SlashInvariantForm.toFun_eq_coe, Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinSeries_tendstoLocallyUniformly hk
  · simp only [OpenEmbedding.toPartialHomeomorph_target, Set.top_eq_univ, mapsTo_range_iff,
    Set.mem_univ, forall_const]
