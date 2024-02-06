import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Finset_Decomposition

noncomputable section

open Complex Filter UpperHalfPlane Set

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

namespace EisensteinSeries

/-- Auxilary function used for bounding Eisentein series-/
def lowerBound1 (z : ℍ) : ℝ :=
  ((z.1.2 ^ (2 : ℕ)) / (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)))

theorem lowerBound1_pos (z : ℍ) : 0 < lowerBound1 z := by
  have H2 : 0 < (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ))  := by
    apply_rules [pow_pos, add_pos_of_nonneg_of_pos, pow_two_nonneg, z.2]
  exact div_pos (pow_pos z.im_pos 2) H2

/-- This function is used to give an upper bound on Eisenstein series-/
def r (z : ℍ) : ℝ := min (z.1.2) (Real.sqrt (lowerBound1 z))

theorem r_pos (z : ℍ) : 0 < r z := by
  simp only [r, lt_min_iff, z.property, Real.sqrt_pos, lowerBound1_pos, and_self]

theorem r_ne_zero (z : ℍ) :  r z ≠ 0 := ne_of_gt (r_pos z)

lemma r_mul_n_pos (k : ℕ) (z : ℍ) (n : ℕ) (hn : 1 ≤ n) :
    0 < (Complex.abs ((r z : ℂ) ^ (k : ℤ) * (n : ℂ)^ (k : ℤ))) := by
  norm_cast
  apply _root_.abs_pos.mpr (mul_ne_zero (pow_ne_zero k (ne_of_gt (r_pos z))) ?_)
  simp only [Nat.cast_pow, ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, not_and, not_not] at *
  intro _
  linarith

lemma pow_two_of_nonzero_ge_one (a : ℤ) (ha : a  ≠ 0) : 0 ≤ a^2 - 1  := by
  simp only [sub_nonneg, one_le_sq_iff_one_le_abs, ge_iff_le]
  exact Int.one_le_abs ha

theorem aux4 (a b : ℝ) (h : 0 < b) : (b ^ 2) / (a ^ 2 + b ^ 2) = 1 / ((a / b) ^ 2 + 1) := by
  field_simp

theorem auxlb (z : ℍ) (δ : ℝ) (n : ℤ) (hn : n ≠ 0) :
    (z.1.2 ^ 2 ) / (z.1.1 ^ 2 + z.1.2 ^ 2) ≤  (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 := by
  have H1 : (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 =
        δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1 + n^2 := by ring
  have H4 : (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1   + n^2) * (z.1.1 ^ 2 + z.1.2 ^ 2)
    - (z.1.2 ^ 2) = (δ * (z.1.1 ^ 2 + z.1.2 ^ 2)+ n * z.1.1)^2 + (n^2 - 1)* (z.1.2)^2 := by ring
  rw [H1, div_le_iff, ← sub_nonneg, H4]
  · apply add_nonneg (pow_two_nonneg _) ?_
    apply mul_nonneg
    norm_cast
    apply pow_two_of_nonzero_ge_one n hn
    apply pow_two_nonneg
  · apply_rules [add_pos_of_nonneg_of_pos, pow_two_nonneg, (pow_pos z.im_pos 2)]

theorem auxbound1 (z : ℍ) (δ : ℝ) : r z ≤ Complex.abs ((z : ℂ) + δ)  := by
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

theorem auxbound2 (z : ℍ) (δ : ℝ) (n : ℤ) (h : n ≠ 0) : r z ≤ Complex.abs (δ * (z : ℂ) + n) := by
  rw [r, Complex.abs, min_le_iff]
  have H1 :
    Real.sqrt (lowerBound1 z) ≤ Real.sqrt ((δ * (z : ℂ).re + n) * (δ * (z : ℂ).re + n) +
      δ * (z : ℂ).im * (δ * (z : ℂ).im)) := by
    rw [lowerBound1, Real.sqrt_le_sqrt_iff, ← pow_two, ← pow_two]
    apply auxlb z δ n h
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
  have := auxbound2 z (x 0 / x 1 : ℝ) 1 one_ne_zero
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast, Int.cast_one] at *
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
  have := aux4 (z : ℂ).re (z : ℂ).im (UpperHalfPlane.im_pos z.1)
  simp only [coe_eq_fst, div_pow, one_div] at this
  simp_rw [lowerBound1]
  rw [this, aux4 A B h, one_div, inv_le_inv, add_le_add_iff_right, div_pow]
  apply div_le_div (sq_nonneg _)
  · simpa [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2
  · positivity
  · simpa [even_two.pow_abs] using pow_le_pow_left h.le hz.2 2
  · positivity
  · positivity
  · apply (lowerBound1_pos z).le


variable {α : Type*} {β : Type*} {i : α → Set β}

/--Equivalence between the sigma of a fammily of finsets of `ℤ × ℤ` and `ℤ × ℤ`-/
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

lemma summable_r_pow  (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
  Summable fun n : ℕ => 8 / (r z) ^ k * ((n : ℝ) ^ (k - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by
    have : 1 < (k - 1 : ℤ) := by linarith
    norm_cast at *
  have riesum := Real.summable_nat_rpow_inv.2 hk
  have nze : (8 / (r z) ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    apply zpow_ne_zero k (ne_of_gt (r_pos z))
  rw [← (summable_mul_left_iff nze).symm]
  convert riesum
  norm_cast

lemma summable_over_square (k : ℤ) (z : ℍ) (h : 3 ≤ k):
    Summable (fun n : ℕ => ∑ v in square n, (1 / (r z) ^ k) * ((n : ℝ) ^ k)⁻¹)  := by
    simp only [one_div, Finset.sum_const, nsmul_eq_mul]
    apply Summable.congr (summable_r_pow k z h)
    intro b
    by_cases b0 : b = 0
    · rw [b0]
      have hk0 :  k ≠ 0 := by linarith
      have hk1 :  k - 1 ≠ 0 := by linarith
      norm_cast
      rw [zero_zpow k hk0, zero_zpow (k - 1) hk1]
      simp only [inv_zero, mul_zero, square_zero, Finset.card_singleton, Nat.cast_one]
    · rw [square_size' b0, zpow_sub_one₀ (a:= ( b: ℝ)) (Nat.cast_ne_zero.mpr b0)  k]
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


lemma Eise_bound_1 (k : ℕ) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ) (hn : 1 ≤ n)
  (C1 : Complex.abs (x 0 : ℂ) = n) : (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
  (Complex.abs ((r z) ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
  rw [inv_le_inv]
  have h0 : (x 0 : ℂ) ≠ 0 := by
    intro hx
    rw [hx] at C1
    simp only [map_zero, Int.cast_eq_zero] at *
    norm_cast at *
    simp_rw [← C1] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  have h1 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
    ((x 0 : ℂ) ^ (k : ℤ)) * ((z : ℂ) + (x 1 : ℂ) / x 0) ^ (k : ℤ) :=
    by
    field_simp
    ring
  rw [h1]
  simp_rw [map_mul Complex.abs]
  norm_cast at *
  have h3 : Complex.abs (n^k : ℕ) = Complex.abs ((x 0)^k : ℤ) := by
    have : Complex.abs ((x 0)^k : ℤ) = Complex.abs (x 0)^k := by
      simp only [Int.cast_pow, map_pow, Real.rpow_nat_cast]
    rw [this, C1]
    norm_cast
    simp only [Nat.cast_pow, map_pow, abs_natCast]
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (Complex.abs.nonneg _)
  convert bound1 z x k
  apply abs_eq_self.mpr ( pow_nonneg (r_pos z).le k)
  norm_cast
  have := Complex.abs.pos (pow_ne_zero k (linear_ne_zero ![x 0, x 1] z ?_))
  apply this
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Int.cast_eq_zero, Matrix.zero_empty, and_true, not_and]
  intro hx
  rw [hx] at C1
  simp [Int.cast_zero] at C1
  norm_cast at C1
  rw [← C1] at hn
  simp only [Nat.one_ne_zero, le_zero_iff] at hn
  apply r_mul_n_pos k z n hn

lemma Eis_bound_2 (k : ℕ) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ) (hn : 1 ≤ n)
  (C2 : Complex.abs (x 1 : ℂ) = n) : (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
  (Complex.abs ((r z) ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
  have h0 : (x 1 : ℂ) ≠ 0 := by
    intro hx
    rw [hx] at C2
    simp at C2
    norm_cast at *
    rw [← C2] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  rw [inv_le_inv]
  have h1 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
    (x 1 : ℂ)^ (k) * ((x 0 : ℂ) / (x 1 : ℂ) * (z : ℂ) + 1) ^ (k) := by
    field_simp
    ring_nf
  rw [h1]
  simp_rw [map_mul Complex.abs]
  have h3 : Complex.abs (n^k ) = Complex.abs ((x 1)^k ) := by
    simp only [map_pow, abs_natCast, ge_iff_le, Nat.cast_nonneg, map_nonneg, C2]
  simp at *
  norm_cast at *
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left
  convert (bound2 z x k)
  apply abs_eq_self.mpr (  (r_pos z).le )
  norm_cast
  simp  [ge_iff_le, map_nonneg, zpow_nonneg]
  apply pow_nonneg (Complex.abs.nonneg _)
  apply Complex.abs.pos (pow_ne_zero k (linear_ne_zero ![x 0, x 1] z ?_))
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Int.cast_eq_zero, Matrix.zero_empty, and_true, not_and]
  intro hx
  norm_cast at *
  apply r_mul_n_pos k z n hn

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
  · have hnn : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
    by_cases C1 : Complex.abs (x 0 : ℂ) = n
    apply Eise_bound_1 k z n x hnn C1
    have C2 := Complex_abs_square_left_ne n ⟨x 0, x 1⟩ hx C1
    apply Eis_bound_2 k z n x hnn C2

lemma  eisensteinSeries_TendstoLocallyUniformlyOn  (k : ℤ) (hk : 3 ≤ k) (N : ℕ)
  (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
  (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) )
  ( fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) Filter.atTop ⊤ := by
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact, eisensteinSeries_SIF]
  simp only [top_eq_univ, subset_univ, eisensteinSeries, forall_true_left]
  intros K hK
  obtain ⟨A,B,hB, HABK⟩:= compact_in_some_slice K hK
  let u :=  fun x : (gammaSet N a ) =>
    (1/((r ⟨⟨A, B⟩, hB⟩)^k))* ( (max (x.1 0).natAbs (x.1 1).natAbs : ℝ)^k)⁻¹
  have hu : Summable u := by
    have := Summable.subtype (summable_upper_bound k hk  ⟨⟨A, B⟩, hB⟩) (gammaSet N a )
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
