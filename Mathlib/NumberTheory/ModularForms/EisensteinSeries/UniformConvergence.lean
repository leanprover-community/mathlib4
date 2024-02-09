/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Finset_Decomposition

/-!
# Uniform convergence of Eisenstein series

We show that `eis` converges locally uniformly on `ℍ` to the Eisenstein series `E` of weight `k`
and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.
-/

noncomputable section

open Complex Filter UpperHalfPlane Set

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

namespace EisensteinSeries

section bounding_functions

/-- Auxilary function used for bounding Eisentein series-/
def lowerBound1 (z : ℍ) : ℝ :=
  ((z.1.2 ^ (2 : ℕ)) / (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)))

lemma lowerBound1' (z : ℍ) : lowerBound1 z = 1/((z.1.1 / z.1.2) ^ (2 : ℕ) + 1) := by
  have := z.2
  field_simp [lowerBound1]

theorem lowerBound1_pos (z : ℍ) : 0 < lowerBound1 z := by
  have H2 : 0 < (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)) := by
    apply_rules [pow_pos, add_pos_of_nonneg_of_pos, pow_two_nonneg, z.2]
  exact div_pos (pow_pos z.im_pos 2) H2

/-- This function is used to give an upper bound on Eisenstein series-/
def r (z : ℍ) : ℝ := min (z.1.2) (Real.sqrt (lowerBound1 z))

theorem r_pos (z : ℍ) : 0 < r z := by
  simp only [r, lt_min_iff, z.property, Real.sqrt_pos, lowerBound1_pos, and_self]

theorem r_ne_zero (z : ℍ) : r z ≠ 0 := ne_of_gt (r_pos z)

lemma r_mul_pos_pos (k : ℕ) (z : ℍ) (n : ℝ) (hn : 0 < n) :
    0 < (Complex.abs ((r z : ℂ) ^ (k : ℤ) * (n : ℂ)^ (k : ℤ))) := by
  norm_cast
  apply _root_.abs_pos.mpr (mul_ne_zero (pow_ne_zero k (ne_of_gt (r_pos z))) ?_)
  simp only [Nat.cast_pow, ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, not_and, not_not] at *
  intro _
  linarith

theorem auxlb (z : ℍ) (δ ε : ℝ) (hε : 0 ≤ ε^2 - 1) :
    (z.1.2 ^ 2 ) / (z.1.1 ^ 2 + z.1.2 ^ 2) ≤ (δ * z.1.1 + ε) ^ 2 + (δ * z.1.2) ^ 2 := by
  have H1 : (δ * z.1.1 + ε) ^ 2 + (δ * z.1.2) ^ 2 =
        δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + ε * 2 * δ * z.1.1 + ε^2 := by ring
  have H4 : (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + ε * 2 * δ * z.1.1 + ε^2) * (z.1.1 ^ 2 + z.1.2 ^ 2)
    - (z.1.2 ^ 2) = (δ * (z.1.1 ^ 2 + z.1.2 ^ 2)+ ε * z.1.1)^2 + (ε^2 - 1)* (z.1.2)^2 := by ring
  rw [H1, div_le_iff, ← sub_nonneg, H4]
  · apply add_nonneg (pow_two_nonneg _) ?_
    apply mul_nonneg
    norm_cast
    apply pow_two_nonneg
  · apply_rules [add_pos_of_nonneg_of_pos, pow_two_nonneg, (pow_pos z.im_pos 2)]

theorem auxbound1 (z : ℍ) (δ : ℝ) : r z ≤ Complex.abs ((z : ℂ) + δ) := by
  rw [r, Complex.abs]
  have H1 : (z : ℂ).im ≤
    Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) := by
    rw [Real.le_sqrt' ]
    nlinarith
    exact z.2
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, AbsoluteValue.coe_mk, MulHom.coe_mk,
    min_le_iff] at *
  left
  simp only [normSq_apply, add_re, coe_re, ofReal_re, add_im, coe_im, ofReal_im, add_zero]
  exact H1

theorem auxbound2 (z : ℍ) (δ ε : ℝ) (hε : 0 ≤ ε^2 - 1) : r z ≤ Complex.abs (δ * (z : ℂ) + ε) := by
  rw [r, Complex.abs, min_le_iff]
  have H1 :
    Real.sqrt (lowerBound1 z) ≤ Real.sqrt ((δ * (z : ℂ).re + ε) * (δ * (z : ℂ).re + ε ) +
      δ * (z : ℂ).im * (δ * (z : ℂ).im)) := by
    rw [lowerBound1, Real.sqrt_le_sqrt_iff, ← pow_two, ← pow_two]
    apply auxlb z δ ε hε
    nlinarith
  right
  simp only [ne_eq, coe_re, coe_im, normSq_apply, AbsoluteValue.coe_mk, MulHom.coe_mk, add_re,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, int_cast_re, add_im, mul_im, add_zero,
    int_cast_im] at *
  exact H1

theorem bound1 (z : ℍ) (x : Fin 2 → ℤ) (k : ℕ) :
    (r z ) ^ k ≤ Complex.abs (((z : ℂ) + (x 1 : ℂ) / (x 0 : ℂ)) ^ k) := by
  have := auxbound1 z (x 1 / x 0 : ℝ)
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast] at *
  exact this

theorem bound2 (z : ℍ) (x : Fin 2 → ℤ) (k : ℕ) :
    (r z ) ^ k ≤ Complex.abs (((x 0 : ℂ) / (x 1 : ℂ) * (z : ℂ) + 1) ^ k) := by
  have := auxbound2 z (x 0 / x 1 : ℝ) 1 (by norm_cast)
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast, Int.cast_one] at *
  exact this

lemma fds (z : ℂ) (hz : 0 < Complex.abs (z)) : z ≠ 0 := by exact nnnorm_pos.mp hz

lemma eis_bound_1 (k : ℕ) (z : ℍ) (x : Fin 2 → ℤ) (C1 : 0 < Complex.abs (x 0 : ℂ)) :
    (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
      (Complex.abs ((r z) ^ (k : ℤ) * (Complex.abs (x 0 : ℂ)) ^ (k : ℤ)))⁻¹ := by
  have h0 : (x 0 : ℂ) ≠ 0 :=  nnnorm_pos.mp C1
  rw [inv_le_inv]
  have h1 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
    ((x 0 : ℂ) ^ (k : ℤ)) * ((z : ℂ) + (x 1 : ℂ) / x 0) ^ (k : ℤ) := by
    field_simp
    ring
  rw [h1]
  have gd := mul_le_mul_of_nonneg_left (bound1 z x k) (pow_nonneg C1.le k)
  simp only [AbsoluteValue.pos_iff, ne_eq, Int.cast_eq_zero, zpow_coe_nat, map_pow, map_mul,
    abs_ofReal, Complex.abs_abs, ge_iff_le] at *
  rw [ mul_comm]
  convert gd
  apply abs_eq_self.mpr ((r_pos z).le )
  have := Complex.abs.pos (pow_ne_zero k (linear_ne_zero ![x 0, x 1] z ?_))
  apply this
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Int.cast_eq_zero, Matrix.zero_empty, and_true, not_and]
  intro hx
  norm_cast at *
  apply r_mul_pos_pos k z (Complex.abs (x 0 : ℂ)) C1

lemma eis_bound_2 (k : ℕ) (z : ℍ) (x : Fin 2 → ℤ)  (C2 : 0 < Complex.abs (x 1 : ℂ)) :
    (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
      (Complex.abs ((r z) ^ (k : ℤ) * (Complex.abs (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ := by
  have h0 : (x 1 : ℂ) ≠ 0 :=  nnnorm_pos.mp C2
  rw [inv_le_inv]
  have h1 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
    (x 1 : ℂ)^ (k) * ((x 0 : ℂ) / (x 1 : ℂ) * (z : ℂ) + 1) ^ (k) := by
    field_simp
    ring_nf
  rw [h1]
  have gd := mul_le_mul_of_nonneg_left (bound2 z x k) (pow_nonneg C2.le k)
  simp only [AbsoluteValue.pos_iff, ne_eq, Int.cast_eq_zero, zpow_coe_nat, map_pow, map_mul,
    abs_ofReal, Complex.abs_abs, ge_iff_le] at *
  rw [ mul_comm]
  convert gd
  apply abs_eq_self.mpr ((r_pos z).le )
  have := Complex.abs.pos (pow_ne_zero k (linear_ne_zero ![x 0, x 1] z ?_))
  apply this
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Int.cast_eq_zero, Matrix.zero_empty, and_true, not_and]
  intro hx
  norm_cast at *
  apply r_mul_pos_pos k z (Complex.abs (x 1 : ℂ)) C2

theorem Eis_is_bounded_on_square (k : ℕ) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ)
    (hx : ⟨x 0, x 1⟩ ∈ square n) : (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ k))⁻¹ ≤
      (Complex.abs ((r z) ^ k * n ^ k))⁻¹ := by
  by_cases hn : n = 0
  · rw [hn] at hx
    simp only [CharP.cast_eq_zero, square_zero, Finset.mem_singleton, Prod.mk.injEq] at hx
    by_cases hk : k = 0
    rw [hk] at *
    simp only [coe_eq_fst, pow_zero, map_one, inv_one, mul_one, le_refl]
    rw [hx.1, hx.2]
    have h1 : (0 : ℝ) ^ (k : ℕ) = 0 := by
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact hk
    simp only [Int.cast_zero, coe_eq_fst, zero_mul, add_zero, map_pow, map_zero, h1, inv_zero, hn,
      CharP.cast_eq_zero, map_mul, abs_ofReal, mul_zero, le_refl]
  · have hnn : 0 < (n : ℝ) := by norm_cast; exact Nat.pos_of_ne_zero hn
    by_cases C1 : Complex.abs (x 0 : ℂ) = n
    · have := eis_bound_1 k z x (by rw [C1]; exact hnn)
      rw [C1] at *
      exact this
    · have C2 := Complex_abs_square_left_ne n ⟨x 0, x 1⟩ hx C1
      have := eis_bound_2 k z x (by rw [C2]; exact hnn)
      rw [C2] at this
      exact this

theorem r_lower_bound_on_slice (A B : ℝ) (h : 0 < B) (z : upperHalfPlaneSlice A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z.1 := by
  have hz := z.2
  simp only [slice_mem, abs_ofReal, ge_iff_le] at hz
  rw [r, r]
  apply min_le_min
  · dsimp only
    convert hz.2
    have := abs_eq_self.mpr (UpperHalfPlane.im_pos z.1).le
    convert this.symm
  rw [Real.sqrt_le_sqrt_iff]
  simp [lowerBound1']
  rw [inv_le_inv, add_le_add_iff_right]
  apply div_le_div (sq_nonneg _)
  · simpa [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2
  · positivity
  · simpa [even_two.pow_abs] using pow_le_pow_left h.le hz.2 2
  · positivity
  · positivity
  · apply (lowerBound1_pos z).le

end bounding_functions

section summability

variable {α : Type*} {β : Type*} {i : α → Set β}

/--Equivalence between the sigma of a fammily of finsets of `β × β` and `β × β`-/
def sigmaEquiv (ι : α → Finset (β × β)) (HI : ∀ y : β × β , ∃! i : α, y ∈ ι i) :
    (Σ s : α, ((ι s) : Set (β × β))) ≃ (β × β) where
  toFun x := x.2
  invFun x := by
    refine ⟨(HI x).choose, x, (HI x).choose_spec.1⟩
  left_inv x := by
      ext
      exact ((HI x.2).choose_spec.2 x.1 x.2.2).symm
      repeat {rfl}
  right_inv x := by rfl

theorem summable_lemma (f : (Fin 2 → ℤ) → ℝ) (h : ∀ y : (Fin 2 → ℤ), 0 ≤ f y)
    (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ ι i) :
      Summable f ↔ Summable fun n : ℕ => ∑ x in ι n, f ![x.1, x.2] := by
  let h2 := Equiv.trans (sigmaEquiv ι HI) (piFinTwoEquiv fun _ => ℤ).symm
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
      simp only [Finset.coe_sort_coe, Equiv.coe_trans, Function.comp_apply,sigmaEquiv]
      convert (Finset.summable (ι x) (f ∘ (piFinTwoEquiv fun _ => ℤ).symm))
    · convert H
      rw [← Finset.tsum_subtype]
      rfl

lemma summable_r_pow (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
    Summable fun n : ℕ => 8 / (r z) ^ k * ((n : ℝ) ^ (k - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by
    have : 1 < (k - 1 : ℤ) := by linarith
    norm_cast at *
  have riesum := Real.summable_nat_rpow_inv.2 hk
  have nze : (8 / (r z) ^ k : ℝ) ≠ 0 := by
    apply div_ne_zero
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    apply zpow_ne_zero k (ne_of_gt (r_pos z))
  rw [← (summable_mul_left_iff nze).symm]
  convert riesum
  norm_cast

lemma summable_over_square (k : ℤ) (z : ℍ) (h : 3 ≤ k):
    Summable (fun n : ℕ => ∑ v in square n, (1 / (r z) ^ k) * ((n : ℝ) ^ k)⁻¹) := by
  simp only [one_div, Finset.sum_const, nsmul_eq_mul]
  apply Summable.congr (summable_r_pow k z h)
  intro b
  by_cases b0 : b = 0
  · rw [b0]
    have hk0 : k ≠ 0 := by linarith
    have hk1 : k - 1 ≠ 0 := by linarith
    norm_cast
    rw [zero_zpow k hk0, zero_zpow (k - 1) hk1]
    simp only [inv_zero, mul_zero, square_zero, Finset.card_singleton, Nat.cast_one]
  · rw [square_size' b0, zpow_sub_one₀ (a:= ( b: ℝ)) (Nat.cast_ne_zero.mpr b0) k]
    simp only [mul_inv_rev, inv_inv, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf

lemma summable_upper_bound (k : ℤ) (h : 3 ≤ k) (z : ℍ) : Summable fun (x : Fin 2 → ℤ) =>
    (1 / (r z) ^ k) * ((max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹ := by
  rw [summable_lemma _ _ (fun (n : ℕ) => square n) squares_cover_all]
  have : ∀ n : ℕ, ∑ v in square n, (1 / (r z) ^ k) * ((max v.1.natAbs v.2.natAbs: ℝ) ^ k)⁻¹ =
     ∑ v in square n, (1 / (r z) ^ k) * ((n : ℝ)^k)⁻¹ := by
     intro n
     apply Finset.sum_congr rfl
     intro x hx
     simp only [square_mem] at hx
     congr
     norm_cast
  apply Summable.congr (summable_over_square k z h)
  intro b
  apply (this b).symm
  intro y
  apply mul_nonneg
  simp only [one_div, inv_nonneg]
  apply zpow_nonneg (r_pos z).le
  simp only [inv_nonneg, ge_iff_le, le_max_iff, Nat.cast_nonneg, or_self, zpow_nonneg]

end summability

lemma eisensteinSeries_TendstoLocallyUniformlyOn (k : ℤ) (hk : 3 ≤ k) (N : ℕ)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
      (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) )
        ( fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) Filter.atTop ⊤ := by
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact, eisensteinSeries_SIF]
  simp only [top_eq_univ, subset_univ, eisensteinSeries, forall_true_left]
  intros K hK
  obtain ⟨A,B,hB, HABK⟩:= compact_in_some_slice K hK
  let u := fun x : (gammaSet N a ) =>
    (1/((r ⟨⟨A, B⟩, hB⟩)^k))* ( (max (x.1 0).natAbs (x.1 1).natAbs : ℝ)^k)⁻¹
  have hu : Summable u := by
    have := Summable.subtype (summable_upper_bound k hk ⟨⟨A, B⟩, hB⟩) (gammaSet N a )
    apply this.congr
    intro v
    simp only [zpow_coe_nat, one_div, Function.comp_apply]
  apply tendstoUniformlyOn_tsum hu
  intro v x hx
  have sq := square_mem (max (v.1 0).natAbs (v.1 1).natAbs ) ⟨(v.1 0), v.1 1⟩
  have := Eis_is_bounded_on_square k x (max (v.1 0).natAbs (v.1 1).natAbs ) v
  simp only [Nat.cast_max, Int.coe_natAbs, iff_true, zpow_coe_nat, one_div, coe_eq_fst, map_pow,
    map_mul, abs_ofReal, abs_natCast, mul_inv_rev, eisSummand, norm_inv, norm_pow, norm_eq_abs,
    ge_iff_le] at *
  apply le_trans (this sq)
  rw [mul_comm]
  apply mul_le_mul
  rw [inv_le_inv]
  apply pow_le_pow_left (r_pos _).le
  rw [abs_of_pos (r_pos _)]
  · exact r_lower_bound_on_slice A B hB ⟨x, HABK hx⟩
  · apply pow_pos (abs_pos.mpr (r_ne_zero x))
  · apply pow_pos (r_pos _)
  · rfl
  repeat {simp only [inv_nonneg, ge_iff_le, le_max_iff, Nat.cast_nonneg, or_self, pow_nonneg,
    inv_nonneg, pow_nonneg (r_pos _).le]}
  · simp only [top_eq_univ, isOpen_univ]
