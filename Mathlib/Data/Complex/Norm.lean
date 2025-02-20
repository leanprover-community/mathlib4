/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

/-!
  # Norm on the complex numbers
-/

noncomputable section

open ComplexConjugate Topology Filter Set

namespace Complex
variable {z : ℂ}

instance instNorm : Norm ℂ where
  norm z := Real.sqrt (normSq z)

theorem norm_def (z : ℂ) : ‖z‖ = Real.sqrt (normSq z) := rfl

theorem norm_mul_self_eq_normSq (z : ℂ) : ‖z‖ * ‖z‖ = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

@[deprecated (since := "2025-02-16")] alias mul_self_abs := norm_mul_self_eq_normSq

private theorem norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ :=
  Real.sqrt_nonneg _

@[bound]
theorem abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (norm_nonneg _), abs_mul_abs_self,
    norm_mul_self_eq_normSq]
  apply re_sq_le_normSq

theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm _)).2

@[deprecated (since := "2025-02-16")] alias abs_re_le_abs := abs_re_le_norm
@[deprecated (since := "2025-02-16")] alias re_le_abs := re_le_norm

private theorem norm_add_le' (z w : ℂ) :  ‖z + w‖ ≤ ‖z‖ + ‖w‖ :=
  (mul_self_le_mul_self_iff (norm_nonneg (z + w)) (add_nonneg (norm_nonneg z)
    (norm_nonneg w))).2 <| by
    rw [norm_mul_self_eq_normSq, add_mul_self_eq, norm_mul_self_eq_normSq, norm_mul_self_eq_normSq,
      add_right_comm, normSq_add, add_le_add_iff_left, mul_assoc, mul_le_mul_left (zero_lt_two' ℝ),
      norm_def, norm_def, ← Real.sqrt_mul <| normSq_nonneg z, ← normSq_conj w, ← map_mul]
    exact re_le_norm (z * conj w)

private theorem norm_eq_zero_iff {z : ℂ} : ‖z‖ = 0 ↔ z = 0 :=
  (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero

private theorem norm_map_zero' : ‖(0 : ℂ)‖ = 0 :=
  norm_eq_zero_iff.mpr rfl

private theorem norm_neg' (z : ℂ) : ‖-z‖ = ‖z‖ := by
  rw [Complex.norm_def, norm_def, normSq_neg]

instance instNormedAddCommGroup : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
  { map_zero' := norm_map_zero'
    add_le' := norm_add_le'
    neg' := norm_neg'
    eq_zero_of_map_eq_zero' := fun _ ↦ norm_eq_zero_iff.mp }

/-- The complex absolute value function, defined as the Complex norm. -/
@[deprecated "use the norm instead" (since := "2025-02-16")]
protected noncomputable abbrev abs (z : ℂ) : ℝ := ‖z‖

@[deprecated (since := "2025-02-16")] alias abs_apply := norm_def

@[simp 1100]
protected theorem norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
  rw [norm_def, norm_def, norm_def, normSq_mul, Real.sqrt_mul (normSq_nonneg _)]

@[simp 1100]
protected theorem norm_div (z w : ℂ) : ‖z / w‖ = ‖z‖ / ‖w‖ := by
  rw [norm_def, norm_def, norm_def, normSq_div, Real.sqrt_div (normSq_nonneg _)]

instance isAbsoluteValueNorm : IsAbsoluteValue (‖·‖ : ℂ → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero_iff
  abv_add' := norm_add_le
  abv_mul' := Complex.norm_mul

protected theorem norm_pow (z : ℂ) (n : ℕ) : ‖z ^ n‖ = ‖z‖ ^ n :=
  map_pow isAbsoluteValueNorm.abvHom _ _

protected theorem norm_zpow (z : ℂ) (n : ℤ) :  ‖z ^ n‖ = ‖z‖ ^ n :=
  map_zpow₀ isAbsoluteValueNorm.abvHom _ _

protected theorem norm_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖s.prod f‖ = s.prod fun i ↦ ‖f i‖ :=
  map_prod isAbsoluteValueNorm.abvHom _ _

theorem norm_conj (z : ℂ) : ‖conj z‖ = ‖z‖ := by simp [norm_def]

@[deprecated (since := "2025-02-16")] protected alias abs_pow := Complex.norm_pow
@[deprecated (since := "2025-02-16")] alias abs_zpow := Complex.norm_zpow
@[deprecated (since := "2025-02-16")] alias abs_prod := Complex.norm_prod
@[deprecated (since := "2025-02-16")] alias abs_conj := norm_conj
@[deprecated (since := "2025-02-16")] protected alias abs_abs := abs_norm

@[simp] lemma norm_I : ‖I‖ = 1 := by simp [norm]

@[deprecated (since := "2025-02-16")] alias abs_I := norm_I

@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

@[simp 1100, norm_cast]
lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]

protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
  (norm_real _).trans (abs_of_nonneg h)

@[deprecated (since := "2025-02-16")] alias abs_ofReal := norm_real
@[deprecated (since := "2025-02-16")] protected alias abs_of_nonneg := Complex.norm_of_nonneg

@[simp, norm_cast]
lemma nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ := by ext; exact norm_real _

@[simp 1100, norm_cast]
lemma norm_natCast (n : ℕ) : ‖(n : ℂ)‖ = n := Complex.norm_of_nonneg n.cast_nonneg

@[simp 1100]
lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖ = OfNat.ofNat n := norm_natCast n

protected lemma norm_two : ‖(2 : ℂ)‖ = 2 := norm_ofNat 2

@[simp 1100, norm_cast]
lemma nnnorm_natCast (n : ℕ) : ‖(n : ℂ)‖₊ = n := Subtype.ext <| by simp

@[simp 1100]
lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖₊ = OfNat.ofNat n := nnnorm_natCast n

@[deprecated (since := "2025-02-16")] alias abs_natCast := norm_natCast
@[deprecated (since := "2025-02-16")] alias abs_ofNat := norm_ofNat
@[deprecated (since := "2025-02-16")] protected alias abs_two := Complex.norm_two

@[simp 1100, norm_cast]
lemma norm_intCast (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := by
  rw [← ofReal_intCast, norm_real, Real.norm_eq_abs]

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by
  rw [norm_intCast, ← Int.cast_abs, abs_of_nonneg hn]

@[simp 1100, norm_cast]
lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := norm_real _

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
lemma nnnorm_ratCast (q : ℚ) : ‖(q : ℂ)‖₊ = ‖(q : ℝ)‖₊ := nnnorm_real q

@[simp 1100, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖₊ = q := by simp [nnnorm]

@[deprecated (since := "2024-08-25")] alias norm_nat := norm_natCast
@[deprecated (since := "2024-08-25")] alias norm_int := norm_intCast
@[deprecated (since := "2024-08-25")] alias norm_rat := norm_ratCast
@[deprecated (since := "2024-08-25")] alias nnnorm_nat := nnnorm_natCast
@[deprecated (since := "2025-02-16")] alias abs_intCast := norm_intCast

lemma normSq_eq_norm_sq (z : ℂ) : normSq z = ‖z‖ ^ 2 := by
  simp [norm_def, sq, Real.mul_self_sqrt (normSq_nonneg _)]

protected theorem sq_norm (z : ℂ) : ‖z‖ ^ 2 = normSq z := (normSq_eq_norm_sq z).symm

@[simp]
theorem sq_norm_sub_sq_re (z : ℂ) : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := by
   rw [Complex.sq_norm, normSq_apply, ← sq, ← sq, add_sub_cancel_left]

@[simp]
theorem sq_norm_sub_sq_im (z : ℂ) : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_norm_sub_sq_re, sub_sub_cancel]

lemma norm_add_mul_I (x y : ℝ) : ‖x + y * I‖ = (x ^ 2 + y ^ 2).sqrt := by
  rw [← normSq_add_mul_I]; rfl

lemma norm_eq_sqrt_sq_add_sq (z : ℂ) : ‖z‖ = (z.re ^ 2 + z.im ^ 2).sqrt := by
  rw [norm_def, normSq_apply, sq, sq]

@[deprecated (since := "2025-02-16")] alias normSq_eq_abs := normSq_eq_norm_sq
@[deprecated (since := "2025-02-16")] protected alias sq_abs := Complex.sq_norm
@[deprecated (since := "2025-02-16")] alias sq_abs_sub_sq_re := sq_norm_sub_sq_re
@[deprecated (since := "2025-02-16")] alias sq_abs_sub_sq_im := sq_norm_sub_sq_im
@[deprecated (since := "2025-02-16")] alias abs_add_mul_I := norm_add_mul_I
@[deprecated (since := "2025-02-16")] alias abs_eq_sqrt_sq_add_sq := norm_eq_sqrt_sq_add_sq

@[simp 1100]
protected theorem range_norm : range (‖·‖ : ℂ → ℝ) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun x hx ↦ ⟨x, Complex.norm_of_nonneg hx⟩

@[deprecated (since := "2025-02-16")] alias range_abs := Complex.range_norm

@[simp]
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨Real.sqrt x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩

theorem norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
    simpa [re_add_im] using norm_add_le (z.re : ℂ) (z.im * I)

@[bound]
theorem abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq, ← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem im_le_norm (z : ℂ) : z.im ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2

@[simp]
theorem abs_re_lt_norm {z : ℂ} : |z.re| < ‖z‖ ↔ z.im ≠ 0 := by
  rw [norm_def, Real.lt_sqrt (abs_nonneg _), normSq_apply, sq_abs, ← sq, lt_add_iff_pos_right,
    mul_self_pos]

@[simp]
theorem abs_im_lt_norm {z : ℂ} : |z.im| < ‖z‖ ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_norm (z * I)

@[simp]
lemma abs_re_eq_norm {z : ℂ} : |z.re| = ‖z‖ ↔ z.im = 0 :=
  not_iff_not.1 <| (abs_re_le_norm z).lt_iff_ne.symm.trans abs_re_lt_norm

@[simp]
lemma abs_im_eq_norm {z : ℂ} : |z.im| = ‖z‖ ↔ z.re = 0 :=
  not_iff_not.1 <| (abs_im_le_norm z).lt_iff_ne.symm.trans abs_im_lt_norm

@[deprecated (since := "2025-02-16")] alias abs_le_abs_re_add_abs_im := norm_le_abs_re_add_abs_im
@[deprecated (since := "2025-02-16")] alias abs_im_le_abs := abs_im_le_norm
@[deprecated (since := "2025-02-16")] alias im_le_abs := im_le_norm
@[deprecated (since := "2025-02-16")] alias abs_re_lt_abs := abs_re_lt_norm
@[deprecated (since := "2025-02-16")] alias abs_im_lt_abs := abs_im_lt_norm
@[deprecated (since := "2025-02-16")] alias abs_re_eq_abs := abs_re_eq_norm
@[deprecated (since := "2025-02-16")] alias abs_im_eq_abs := abs_im_eq_norm

theorem norm_le_sqrt_two_mul_max (z : ℂ) : ‖z‖ ≤ Real.sqrt 2 * max |z.re| |z.im| := by
  obtain ⟨x, y⟩ := z
  simp only [norm_def, normSq_mk, norm_def, ← sq]
  by_cases hle : |x| ≤ |y|
  · calc
      Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (y ^ 2 + y ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle) _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_right hle, ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
  · have hle' := le_of_not_le hle
    rw [add_comm]
    calc
      Real.sqrt (y ^ 2 + x ^ 2) ≤ Real.sqrt (x ^ 2 + x ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle') _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_left hle', ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]

theorem abs_re_div_norm_le_one (z : ℂ) : |z.re / ‖z‖| ≤ 1 :=
 if hz : z = 0 then by simp [hz, zero_le_one]
 else by simp_rw [abs_div, abs_norm,
   div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_re_le_norm]

theorem abs_im_div_norm_le_one (z : ℂ) : |z.im / ‖z‖| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by simp_rw [_root_.abs_div, abs_norm,
    div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_im_le_norm]

@[deprecated (since := "2025-02-16")] alias abs_le_sqrt_two_mul_max := norm_le_sqrt_two_mul_max
@[deprecated (since := "2025-02-16")] alias abs_re_div_abs_le_one := abs_re_div_norm_le_one
@[deprecated (since := "2025-02-16")] alias abs_im_div_abs_le_one := abs_im_div_norm_le_one

theorem dist_eq (z w : ℂ) : dist z w = ‖z - w‖ := rfl

theorem dist_eq_re_im (z w : ℂ) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq, sq]
  rfl

@[simp]
theorem dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _

theorem dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
  NNReal.eq <| dist_of_re_eq h

theorem edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist, edist_nndist, nndist_of_re_eq h]

theorem dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
  NNReal.eq <| dist_of_im_eq h

theorem edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist, edist_nndist, nndist_of_im_eq h]

theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, Real.dist_eq, sub_neg_eq_add, ← two_mul,
    _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]

theorem nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * Real.nnabs z.im :=
  NNReal.eq <| by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]

theorem nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm, nndist_conj_self]

/-! ### Cauchy sequences -/

theorem isCauSeq_re (f : CauSeq ℂ (‖·‖)) : IsCauSeq abs fun n ↦ (f n).re := fun _ ε0 ↦
  (f.cauchy ε0).imp fun i H j ij ↦
    lt_of_le_of_lt (by simpa using abs_re_le_norm (f j - f i)) (H _ ij)

theorem isCauSeq_im (f : CauSeq ℂ (‖·‖)) : IsCauSeq abs fun n ↦ (f n).im := fun ε ε0 ↦
  (f.cauchy ε0).imp fun i H j ij ↦ by
    simpa only [← ofReal_sub, norm_real, sub_re] using (abs_im_le_norm _).trans_lt <| H _ ij

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩

theorem isCauSeq_norm {f : ℕ → ℂ} (hf : IsCauSeq (‖·‖) f) :
    IsCauSeq abs ((‖·‖) ∘ f) := fun ε ε0 ↦
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj ↦  lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ (‖·‖)) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

theorem equiv_limAux (f : CauSeq ℂ (‖·‖)) :
    f ≈ CauSeq.const (‖·‖) (limAux f) := fun ε ε0 ↦
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun _ H j ij ↦ by
    obtain ⟨H₁, H₂⟩ := H _ ij
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    dsimp [limAux] at *
    have := add_lt_add H₁ H₂
    rwa [add_halves] at this

instance instIsComplete : CauSeq.IsComplete ℂ (‖·‖) :=
  ⟨fun f ↦ ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ (‖·‖)) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    letI : IsAbsoluteValue (‖·‖ : ℂ → ℝ) := inferInstance
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const (‖·‖) (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ ↦
          Complex.ext (by simp [limAux, cauSeqRe, ofReal]) (by simp [limAux, cauSeqIm, ofReal])

theorem lim_re (f : CauSeq ℂ (‖·‖)) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

theorem lim_im (f : CauSeq ℂ (‖·‖)) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

theorem isCauSeq_conj (f : CauSeq ℂ (‖·‖)) :
    IsCauSeq (‖·‖) fun n ↦ conj (f n) := fun ε ε0 ↦
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    simp_rw [← RingHom.map_sub, norm_conj]; exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ (‖·‖)) : CauSeq ℂ (‖·‖) :=
  ⟨_, isCauSeq_conj f⟩

theorem lim_conj (f : CauSeq ℂ (‖·‖)) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

/-- The norm of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqNorm (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_norm f.2⟩

theorem lim_norm (f : CauSeq ℂ (‖·‖)) : lim (cauSeqNorm f) = ‖lim f‖ :=
  lim_eq_of_equiv_const fun ε ε0 ↦
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

@[deprecated (since := "2025-02-16")] alias isCauSeq_abs := isCauSeq_norm
@[deprecated (since := "2025-02-16")] alias cauSeqAbs := cauSeqNorm
@[deprecated (since := "2025-02-16")] alias  lim_abs := lim_norm

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 :=
  fun h ↦ (zero_re ▸ h ▸ hs).false

lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 :=
  ne_zero_of_re_pos <| zero_lt_one.trans hs

lemma re_neg_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : (-s).re ≠ 0 :=
  ne_iff_lt_or_gt.mpr <| Or.inl <| neg_re s ▸ (neg_lt_zero.mpr hs)

lemma re_neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : (-s).re ≠ 0 :=
  re_neg_ne_zero_of_re_pos <| zero_lt_one.trans hs

end Complex
