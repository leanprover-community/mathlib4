/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Data.Real.Archimedean

/-!
# Standard part function

Suppose `K` is some ring which can embed the real numbers. Let `x y : K` be non-zero with
`ArchimedeanClass.mk y ≤ ArchimedeanClass.mk x`. Then, there exists exactly one real number `r` such
that `ArchimedeanClass.mk y < ArchimedeanClass.mk (x - r * y)`. We call this the `standardPart` of
the ratio `x / y`.

This generalizes the function of the same name in the study of `Hyperreal` numbers, which is just
`standardPart x 1`.

## Todo

Should we redefine `Hyperreal.st x = ArchimedeanClass.standardPart x 1`?
-/

namespace ArchimedeanClass
variable {K : Type*} [LinearOrder K] [CommRing K] [IsStrictOrderedRing K] {x y : K}

private theorem exists_mk_sub_real_mul_gt' (f : ℝ →+* K) (hf : StrictMono f)
    (hx : 0 < x) (hy : 0 < y) (h : mk y ≤ mk x) :
    ∃ r : ℝ, mk y < mk (x - f r * y) := by
  obtain h | h := h.lt_or_eq
  · use 0; simpa
  · let s := {r : ℝ | f r * y ≤ x}
    have hs₁ : s.Nonempty := by
      obtain ⟨r, hr, hr'⟩ := (mk_le_mk_iff_denselyOrdered f hf).1 h.ge
      rw [abs_of_pos hx, abs_of_pos hy] at hr'
      exact ⟨r, hr'⟩
    have hs₂ : BddAbove s := by
      obtain ⟨n, hn⟩ := mk_le_mk.1 h.le
      rw [abs_of_pos hx, abs_of_pos hy] at hn
      refine ⟨n, fun r hr ↦ ?_⟩
      rw [← hf.le_iff_le, map_natCast f, ← mul_le_mul_iff_of_pos_right hy, ← nsmul_eq_mul]
      exact hr.trans hn
    have hs₃ : IsLowerSet s := by
      refine fun r₁ r₂ hr hrs ↦ hrs.trans' ?_
      rw [mul_le_mul_iff_left₀ hy]
      exact hf.monotone hr
    use sSup s
    rw [mk_lt_mk]
    rintro (_ | n)
    · simpa using hy.ne'
    have hfn : 0 < f (n + 1)⁻¹ := by
      rw [← f.map_zero, hf.lt_iff_lt, inv_pos]
      exact n.cast_add_one_pos
    have hfn' : f (n + 1)⁻¹ * (n + 1 :) = 1 := by
      rw [← map_natCast f, Nat.cast_add_one, ← f.map_mul, inv_mul_cancel₀, f.map_one]
      exact n.cast_add_one_ne_zero
    by_contra! hn
    rw [abs_of_pos hy] at hn
    obtain hs | hs := le_total (x - f (sSup s) * y) 0
    · rw [abs_of_nonpos hs, nsmul_eq_mul, mul_neg, mul_sub, ← mul_assoc, le_neg, sub_le_iff_le_add,
        ← neg_one_mul, ← add_mul, ← mul_le_mul_iff_right₀ hfn, ← mul_assoc, hfn', one_mul,
        ← mul_assoc, mul_add, ← mul_assoc, hfn', one_mul, mul_neg_one,
        ← f.map_neg, ← f.map_add] at hn
      have hn' : -(n + 1 : ℝ)⁻¹ + sSup s < sSup s := by simpa using n.cast_add_one_pos
      obtain ⟨a, ha, ha'⟩ := exists_lt_of_lt_csSup hs₁ hn'
      apply ha'.not_ge
      rw [← hf.le_iff_le, ← mul_le_mul_iff_left₀ hy]
      exact ha.trans_eq <| hn.antisymm (hs₃ ha'.le ha)
    · rw [abs_of_nonneg hs, nsmul_eq_mul, mul_sub, ← mul_assoc, le_sub_iff_add_le,
        ← one_add_mul, ← mul_le_mul_iff_right₀ hfn, ← mul_assoc, mul_add, ← mul_assoc, hfn',
        one_mul, mul_one, ← mul_assoc, hfn', one_mul, ← f.map_add] at hn
      have hn' : sSup s < (n + 1 : ℝ)⁻¹ + sSup s := by simpa using n.cast_add_one_pos
      apply hn.not_gt
      simpa [s] using notMem_of_csSup_lt hn' hs₂

theorem exists_mk_sub_real_mul_gt (f : ℝ →+* K) (hf : StrictMono f)
    (hy : y ≠ 0) (h : mk y ≤ mk x) : ∃ r : ℝ, mk y < mk (x - f r * y) := by
  obtain rfl | hx := eq_or_ne x 0
  · use 0; simp_all [lt_top_iff_ne_top]
  have H (x y r) : mk (-x - f r * y) = mk (x + f r * y) := by rw [← neg_add', mk_neg]
  obtain hx | hx := hx.lt_or_gt <;> obtain hy | hy := hy.lt_or_gt
  · convert exists_mk_sub_real_mul_gt' f hf (neg_pos.2 hx) (neg_pos.2 hy) (by simpa) using 3
    · simp
    · rw [H, mul_neg, sub_eq_add_neg]
  · rw [(Equiv.neg _).exists_congr_left]
    convert exists_mk_sub_real_mul_gt' f hf (neg_pos.2 hx) hy (by simpa) using 3
    simp [H]
  · rw [(Equiv.neg _).exists_congr_left]
    convert exists_mk_sub_real_mul_gt' f hf hx (neg_pos.2 hy) (by simpa) using 3 <;> simp
  · exact exists_mk_sub_real_mul_gt' f hf hx hy h

theorem exists_mk_add_real_mul_gt (f : ℝ →+* K) (hf : StrictMono f) (hy : y ≠ 0) (h : mk y ≤ mk x) :
    ∃ r : ℝ, mk y < mk (x + f r * y) := by
  rw [(Equiv.neg _).exists_congr_left]
  simpa [← sub_eq_add_neg] using exists_mk_sub_real_mul_gt f hf hy h

open Classical in
/-- The standard part of a ratio `x / y` is the unique real `r` such that
`ArchimedeanClass.mk y < ArchimedeanClass.mk (x - f r * y)`. -/
noncomputable def standardPart (f : ℝ →+* K) (x y : K) : ℝ :=
  if H : ∃ r : ℝ, mk y < mk (x - f r * y) then Classical.choose H else 0

theorem mk_lt_mk_sub_standardPart_mul (f : ℝ →+* K) (hf : StrictMono f)
    (hy : y ≠ 0) (h : mk y ≤ mk x) : mk y < mk (x - f (standardPart f x y) * y) := by
  have H := exists_mk_sub_real_mul_gt f hf hy h
  rw [standardPart, dif_pos H]
  exact Classical.choose_spec H

theorem standardPart_of_mk_lt_mk (f : ℝ →+* K) (hf : StrictMono f) {r : ℝ}
    (h : mk x < mk y) : standardPart f x y = 0 := by
  apply dif_neg
  intro ⟨r, hr⟩
  apply hr.not_ge
  rw [mk_sub_eq_mk_left]


  #exit

theorem standardPart_of_mk_sub_gt_mk (f : ℝ →+* K) (hf : StrictMono f) {r : ℝ}
    (h : mk y < mk (x - f r * y)) : standardPart f x y = r := by
  have hy : y ≠ 0 := by aesop

  sorry

  #exit

@[simp]
theorem standardPart_zero_right (f : ℝ →+* K) (x : K) : standardPart f x 0 = 0 := by
  simp [standardPart]

theorem standardPart_zero_left (f : ℝ →+* K) (hf : StrictMono f) (x : K) :
    standardPart f 0 x = 0 := by
  obtain rfl | hx := eq_or_ne x 0
  · exact standardPart_zero_right f 0
  · rw [standardPart]
    split_ifs
    apply dif_neg
    simp only [zero_sub, mk_neg,  not_exists, not_lt]

#exit

#exit

theorem existsUnique_mk_sub_real_mul_gt (f : ℝ →+* K) (hf : StrictMono f)
    (hx : x ≠ 0) (h : mk y ≤ mk x) :
    ∃! r : ℝ, mk y < mk (x - f r * y) := by
  apply existsUnique_of_exists_of_unique (exists_mk_sub_real_mul_gt f hf hx h)
  intro r₁ r₂ hr₁ hr₂
  by_contra hr
  rw [← sub_eq_zero, ← hf.injective.eq_iff, f.map_zero] at hr
  sorry

theorem existsUnique_mk_add_real_mul_gt (f : ℝ →+* K) (hf : StrictMono f)
    (hx : x ≠ 0) (h : mk y ≤ mk x) :
    ∃! r : ℝ, mk y < mk (x + f r * y) := by
  rw [(Equiv.neg _).existsUnique_congr_left]
  simpa [← sub_eq_add_neg] using existsUnique_mk_sub_real_mul_gt f hf hx h

end ArchimedeanClass
