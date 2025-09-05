import Mathlib.Analysis.RCLike.Basic


variable {K : Type*} [RCLike K]


/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are star ordered rings.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)

Note this is only an instance with `open scoped ComplexOrder`. -/
lemma toStarOrderedRing : StarOrderedRing K :=
  StarOrderedRing.of_nonneg_iff'
    (h_add := fun {x y} hxy z => by
      rw [RCLike.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [nonneg_iff]
      refine ⟨fun h ↦ ⟨√(re x), by simp [ext_iff (K := K), h.1, h.2]⟩, ?_⟩
      rintro ⟨s, rfl⟩
      simp [mul_comm, mul_self_nonneg, add_nonneg])

scoped[ComplexOrder] attribute [instance] RCLike.toStarOrderedRing

lemma toZeroLEOneClass : ZeroLEOneClass K where
  zero_le_one := by simp [@RCLike.le_iff_re_im K]

scoped[ComplexOrder] attribute [instance] RCLike.toZeroLEOneClass

lemma toIsOrderedAddMonoid : IsOrderedAddMonoid K where
  add_le_add_left _ _ := add_le_add_left

scoped[ComplexOrder] attribute [instance] RCLike.toIsOrderedAddMonoid

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly ordered rings.

Note this is only an instance with `open scoped ComplexOrder`. -/
lemma toIsStrictOrderedRing : IsStrictOrderedRing K :=
  .of_mul_pos fun z w hz hw ↦ by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedRing

lemma toPosMulReflectLT : PosMulReflectLT K where
  elim := by
    rintro ⟨x, hx⟩ y z hyz
    dsimp at *
    rw [RCLike.le_iff_re_im, map_zero, map_zero, eq_comm] at hx
    obtain ⟨r, rfl⟩ := ((is_real_TFAE x).out 3 1).1 hx.2
    simp only [RCLike.lt_iff_re_im (K := K), mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      mul_im, add_zero, mul_eq_mul_left_iff] at hyz ⊢
    refine ⟨lt_of_mul_lt_mul_of_nonneg_left hyz.1 <| by simpa using hx, hyz.2.resolve_right ?_⟩
    rintro rfl
    simp at hyz

scoped[ComplexOrder] attribute [instance] RCLike.toPosMulReflectLT

theorem toOrderedSMul : OrderedSMul ℝ K :=
  OrderedSMul.mk' fun a b r hab hr => by
    replace hab := hab.le
    rw [RCLike.le_iff_re_im] at hab
    rw [RCLike.le_iff_re_im, smul_re, smul_re, smul_im, smul_im]
    exact hab.imp (fun h => mul_le_mul_of_nonneg_left h hr.le) (congr_arg _)

scoped[ComplexOrder] attribute [instance] RCLike.toOrderedSMul

/-- A star algebra over `K` has a scalar multiplication that respects the order. -/
lemma _root_.StarModule.instOrderedSMul {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Module K A] [StarModule K A] [IsScalarTower K A A] [SMulCommClass K A A] :
    OrderedSMul K A := .mk' fun _a _b _zc hab hc ↦ (smul_lt_smul_of_pos_left hab hc).le

instance {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℝ A] [StarModule ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] :
    OrderedSMul ℝ A :=
  StarModule.instOrderedSMul

scoped[ComplexOrder] attribute [instance] StarModule.instOrderedSMul

theorem ofReal_mul_pos_iff (x : ℝ) (z : K) :
    0 < x * z ↔ (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z) := by
  simp only [pos_iff (K := K), neg_iff (K := K), re_ofReal_mul, im_ofReal_mul]
  obtain hx | hx | hx := lt_trichotomy x 0
  · simp only [mul_pos_iff, not_lt_of_gt hx, false_and, hx, true_and, false_or, mul_eq_zero, hx.ne,
      or_false]
  · simp only [hx, zero_mul, lt_self_iff_false, false_and, false_or]
  · simp only [mul_pos_iff, hx, true_and, not_lt_of_gt hx, false_and, or_false, mul_eq_zero,
      hx.ne', false_or]

theorem ofReal_mul_neg_iff (x : ℝ) (z : K) :
    x * z < 0 ↔ (x < 0 ∧ 0 < z) ∨ (0 < x ∧ z < 0) := by
  simpa only [mul_neg, neg_pos, neg_neg_iff_pos] using ofReal_mul_pos_iff x (-z)

lemma instPosMulReflectLE : PosMulReflectLE K where
  elim a b c h := by
    obtain ⟨a', ha1, ha2⟩ := pos_iff_exists_ofReal.mp a.2
    rw [← sub_nonneg]
    #adaptation_note /-- 2025-03-29 need beta reduce for lean4#7717 -/
    beta_reduce at h
    rw [← ha2, ← sub_nonneg, ← mul_sub, le_iff_lt_or_eq] at h
    rcases h with h | h
    · rw [ofReal_mul_pos_iff] at h
      exact le_of_lt <| h.rec (False.elim <| not_lt_of_gt ·.1 ha1) (·.2)
    · exact ((mul_eq_zero_iff_left <| ofReal_ne_zero.mpr ha1.ne').mp h.symm).ge

scoped[ComplexOrder] attribute [instance] RCLike.instPosMulReflectLE

section Order

open scoped ComplexOrder
variable {z w : K}

theorem lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w := by
  simp_rw [lt_iff_le_and_ne, @RCLike.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩

theorem nonneg_iff : 0 ≤ z ↔ 0 ≤ re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)

theorem pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)

theorem nonpos_iff : z ≤ 0 ↔ re z ≤ 0 ∧ im z = 0 := by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)

theorem neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0 := by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)

lemma nonneg_iff_exists_ofReal : 0 ≤ z ↔ ∃ x ≥ (0 : ℝ), x = z := by
  simp_rw [nonneg_iff (K := K), ext_iff (K := K)]; aesop

lemma pos_iff_exists_ofReal : 0 < z ↔ ∃ x > (0 : ℝ), x = z := by
  simp_rw [pos_iff (K := K), ext_iff (K := K)]; aesop

lemma nonpos_iff_exists_ofReal : z ≤ 0 ↔ ∃ x ≤ (0 : ℝ), x = z := by
  simp_rw [nonpos_iff (K := K), ext_iff (K := K)]; aesop

lemma neg_iff_exists_ofReal : z < 0 ↔ ∃ x < (0 : ℝ), x = z := by
  simp_rw [neg_iff (K := K), ext_iff (K := K)]; aesop

@[simp, norm_cast]
lemma ofReal_le_ofReal {x y : ℝ} : (x : K) ≤ (y : K) ↔ x ≤ y := by
  rw [le_iff_re_im]
  simp

@[simp, norm_cast]
lemma ofReal_lt_ofReal {x y : ℝ} : (x : K) < (y : K) ↔ x < y := by
  rw [lt_iff_re_im]
  simp

@[simp, norm_cast]
lemma ofReal_nonneg {x : ℝ} : 0 ≤ (x : K) ↔ 0 ≤ x := by
  rw [← ofReal_zero, ofReal_le_ofReal]

@[simp, norm_cast]
lemma ofReal_nonpos {x : ℝ} : (x : K) ≤ 0 ↔ x ≤ 0 := by
  rw [← ofReal_zero, ofReal_le_ofReal]

@[simp, norm_cast]
lemma ofReal_pos {x : ℝ} : 0 < (x : K) ↔ 0 < x := by
  rw [← ofReal_zero, ofReal_lt_ofReal]

@[simp, norm_cast]
lemma ofReal_lt_zero {x : ℝ} : (x : K) < 0 ↔ x < 0 := by
  rw [← ofReal_zero, ofReal_lt_ofReal]

lemma norm_le_re_iff_eq_norm {z : K} :
    ‖z‖ ≤ re z ↔ z = ‖z‖ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : ‖z‖ = re z := (le_antisymm (re_le_norm z) h).symm
    rw [h', re_eq_self_of_le h]
  · rw [h]
    simp

lemma re_le_neg_norm_iff_eq_neg_norm {z : K} :
    re z ≤ -‖z‖ ↔ z = -‖z‖ := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

lemma norm_of_nonneg' {x : K} (hx : 0 ≤ x) : ‖x‖ = x := by
  rw [eq_comm, ← norm_le_re_iff_eq_norm, ← sqrt_normSq_eq_norm, normSq_apply]
  simp [nonneg_iff.mp hx]

lemma re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjoint x) : 0 ≤ re x ↔ 0 ≤ x := by
  simp [nonneg_iff (K := K), conj_eq_iff_im.mp hx]

@[gcongr]
lemma re_le_re {x y : K} (h : x ≤ y) : re x ≤ re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

lemma re_monotone : Monotone (re : K → ℝ) :=
  fun _ _ => re_le_re

protected lemma inv_pos_of_pos (hz : 0 < z) : 0 < z⁻¹ := by
  rw [pos_iff_exists_ofReal] at hz
  obtain ⟨x, hx, hx'⟩ := hz
  rw [← hx', ← ofReal_inv, ofReal_pos]
  exact inv_pos_of_pos hx

protected lemma inv_pos : 0 < z⁻¹ ↔ 0 < z := by
  refine ⟨fun h => ?_, fun h => RCLike.inv_pos_of_pos h⟩
  rw [← inv_inv z]
  exact RCLike.inv_pos_of_pos h


lemma norm_le_im_iff_eq_I_mul_norm {z : K} :
    ‖z‖ ≤ im z ↔ z = I * ‖z‖ := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := K)
  · simp [h, im_eq_zero]
  · have : (I : K) ≠ 0 := fun _ ↦ by simp_all
    rw [← mul_right_inj' (neg_ne_zero.mpr this)]
    convert norm_le_re_iff_eq_norm (z := -I * z) using 2
    all_goals simp [neg_mul, ← mul_assoc, I_mul_I_of_nonzero this, norm_I_of_ne_zero this]

lemma im_le_neg_norm_iff_eq_neg_I_mul_norm {z : K} :
    im z ≤ -‖z‖ ↔ z = -(I * ‖z‖) := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

end Order
