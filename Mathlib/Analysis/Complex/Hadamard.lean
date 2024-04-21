/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Hadamard three-lines Theorem

In this file we present a proof of a special case of Hadamard's three-lines Theorem.

## Main result

- `norm_le_interp_on_closed_strip` :
Hadamard three-line theorem on `re ⁻¹' [0,1]`: If `f` is a bounded function, continuous on
`re ⁻¹' [0,1]` and differentiable on `re ⁻¹' (0,1)`, then for
`M(x) := sup ((norm ∘ f) '' (re ⁻¹' {x}))`, that is `M(x)` is the supremum of the absolute value of
`f` along the vertical lines `re z = x`, we have that `∀ z ∈ re ⁻¹' [0,1]` the inequality
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|` holds. This can be seen to be equivalent to the statement
that `log M(re z)` is a convex function on `[0,1]`.

## Main definitions

- `Complex.HadamardThreeLines.verticalStrip` :
    The vertical verticalStrip defined by : `re ⁻¹' Ioo a b`

- `Complex.HadamardThreeLines.verticalClosedStrip` :
    The vertical verticalStrip defined by : `re ⁻¹' Icc a b`

- `Complex.HadamardThreeLines.sSupNormIm` :
    The supremum function on vertical lines defined by : `sSup {|f(z)| : z.re = x}`

- `Complex.HadamardThreeLines.invInterpStrip` :
    Inverse of the interpolation between the `sSupNormIm` on the edges of the verticalStrip.

- `Complex.HadamardThreeLines.F` :
    Function defined by `f` times `invInterpStrip`. Convenient form for proofs.

## Note

The proof follows from Phragmén-Lindelöf when both frontiers are not everywhere zero.
We then use a limit argument to cover the case when either of the sides are `0`.
-/


open Set Filter Function Complex

namespace Complex
namespace HadamardThreeLines

/-- The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b`. -/
def verticalStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Ioo a b

/-- The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b`. -/
def verticalClosedStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Icc a b

/-- The supremum of the norm of `f` on imaginary lines. (Fixed real part)
This is also known as the function `M` -/
noncomputable def sSupNormIm {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (x : ℝ) : ℝ :=
  sSup ((norm ∘ f) '' (re ⁻¹' {x}))

section invInterpStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (z : ℂ)

/--
The inverse of the interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the inverse of the right side of the target inequality:
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|`.

Shifting this by a positive epsilon allows us to prove the case when either of the boundaries
is zero.-/
noncomputable def invInterpStrip (ε : ℝ) : ℂ :=
  (ε + sSupNormIm f 0)^(z - 1) * (ε + sSupNormIm f 1)^(-z)

/-- A function useful for the proofs steps. We will aim to show that it is bounded by 1. -/
noncomputable def F (ε : ℝ) := fun z ↦ invInterpStrip f z ε • f z

/-- `sSup` of `norm` is nonneg applied to the image of `f` on the vertical line `re z = x` -/
lemma sSupNormIm_nonneg (x : ℝ) : 0 ≤ sSupNormIm f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

/-- `sSup` of `norm` translated by `ε > 0` is positive applied to the image of `f` on the
vertical line `re z = x` -/
lemma sSupNormIm_eps_pos {ε : ℝ} (hε : ε > 0) (x : ℝ) : 0 < ε + sSupNormIm f x := by
  apply add_pos_of_pos_of_nonneg hε
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

/-- Useful rewrite for the absolute value of `invInterpStrip`-/
lemma abs_invInterpStrip {ε : ℝ} (hε : ε > 0) :
    abs (invInterpStrip f z ε) =
    (ε + sSupNormIm f 0)^(z.re - 1) * (ε + sSupNormIm f 1)^(-z.re) := by
  simp only [invInterpStrip, map_mul]
  repeat rw [← ofReal_add]
  repeat rw [abs_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp only [sub_re, one_re, neg_re]

/-- The function `invInterpStrip` is `diffContOnCl`. -/
lemma diffContOnCl_invInterpStrip {ε : ℝ} (hε : ε > 0) :
    DiffContOnCl ℂ (fun z ↦ invInterpStrip f z ε) (verticalStrip 0 1) := by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const (differentiable_id') 1) _
    left
    rw [← ofReal_add, ofReal_ne_zero]
    simp only [ne_eq, ne_of_gt (sSupNormIm_eps_pos f hε 0), not_false_eq_true]
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id')
    apply Or.inl
    rw [← ofReal_add, ofReal_ne_zero];
    exact (ne_of_gt (sSupNormIm_eps_pos f hε 1))

/-- If `f` is bounded on the unit vertical strip, then `f` is bounded by `sSupNormIm` there. -/
lemma norm_le_sSupNormIm (f : ℂ → E) (z : ℂ) (hD : z ∈ verticalClosedStrip 0 1)
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) :
    ‖f z‖ ≤ sSupNormIm f (z.re) := by
  refine le_csSup ?_ ?_
  · apply BddAbove.mono (image_subset (norm ∘ f) _) hB
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

/-- The function `f` is bounded by `sSupNormIm`. (`f` is bounded on its domain.) -/
lemma norm_lt_sSupNormIm_eps (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hD : z ∈ verticalClosedStrip 0 1) (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) :
    ‖f z‖ < ε + sSupNormIm f (z.re) :=
  lt_add_of_pos_of_le hε (norm_le_sSupNormIm f z hD hB)

/-- When the function `f` is bounded above on a vertical strip, then so is `F`. -/
lemma F_BddAbove (f : ℂ → E) (ε : ℝ) (hε : ε > 0)
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) :
    BddAbove ((norm ∘ (F f ε)) '' (verticalClosedStrip 0 1)) := by
 -- Rewriting goal
  simp only [F, image_congr, comp_apply, map_mul, invInterpStrip]
  rw [bddAbove_def] at *
  cases' hB with B hB
  -- Using bound
  use ((max 1 ((ε + sSupNormIm f 0)^ (-(1 : ℝ)))) * max 1 ((ε + sSupNormIm f 1)^ (-(1 : ℝ)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intros z hset
  specialize hB (‖f z‖)
  specialize hB _
  · simp only [image_congr, mem_image, comp_apply]; use z
  -- Proof that the bound is correct
  · rw [norm_smul]
    repeat rw [← ofReal_add]
    apply mul_le_mul _ hB (norm_nonneg _) _
    · rw [norm_mul]
      apply mul_le_mul _ _ (norm_nonneg _) (zero_le_one.trans (le_max_left _ _))
      -- Bounding individual terms
      · by_cases hM0_one : 1 ≤ ε + sSupNormIm f 0
        -- `1 ≤ (sSupNormIm f 0)`
        · apply le_trans _ (le_max_left _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
            one_re, Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
        -- `0 < (sSupNormIm f 0) < 1`
        · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
            one_re]
          apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
          simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
      · by_cases hM1_one : 1 ≤ ε + sSupNormIm f 1
        -- `1 ≤ sSupNormIm f 1`
        · apply le_trans _ (le_max_left _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1), sub_re,
            one_re, neg_re, Real.rpow_le_one_of_one_le_of_nonpos
            hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
        -- `0 < sSupNormIm f 1 < 1`
        · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1), sub_re,
            one_re, neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
            (le_of_lt hM1_one) (neg_le_neg_iff.mpr hset.2)]
    simp only [gt_iff_lt, lt_max_iff, zero_lt_one, true_or, mul_nonneg_iff_of_pos_left, le_max_iff,
      zero_le_one]

/-- Proof that the edges are bounded by one -/
lemma F_edge_le_one (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) (hz : z ∈ re ⁻¹' {0, 1}) :
    ‖F f ε z‖ ≤ 1 := by
  simp only [F, norm_smul, norm_eq_abs, map_mul, abs_cpow_eq_rpow_re_of_pos,
    abs_invInterpStrip f z hε, sSupNormIm_eps_pos f hε 1,
    sub_re, one_re, neg_re]
  cases' hz with hz0 hz1
  -- `z.re = 0`
  · simp only [hz0, zero_sub, Real.rpow_neg_one, neg_zero, Real.rpow_zero, mul_one,
      inv_mul_le_iff (sSupNormIm_eps_pos f hε 0)]
    rw [← hz0]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
      inv_mul_le_iff (sSupNormIm_eps_pos f hε 1), mul_one]
    rw [← hz1]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

theorem norm_mul_invInterpStrip_le_one_on_closedStrip (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F f ε z‖ ≤ 1 := by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f hε) hd) _
    (fun x hx ↦ F_edge_le_one f ε hε x hB (Or.inl hx))
    (fun x hx ↦ F_edge_le_one f ε hε x hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero, div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f ε hε hB
  simp only [comp_apply, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply eventually_of_forall
  intro x hx
  norm_num
  exact (hBF x ((preimage_mono Ioo_subset_Icc_self) hx)).trans
    ((le_of_lt (lt_add_one BF)).trans (Real.add_one_le_exp BF))

end invInterpStrip

-----

variable [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)

/--
The the interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the right side of the target inequality:
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|`.

Note that if `(sSupNormIm f 0) = 0 ∨ (sSupNormIm f 1) = 0` then the power is not continuous
since `0 ^ 0 = 1`. Hence the use of `ite`. -/
noncomputable def interpStrip (z : ℂ) : ℂ :=
  if (sSupNormIm f 0) = 0 ∨ (sSupNormIm f 1) = 0
    then 0
    else (sSupNormIm f 0)^(1-z) * (sSupNormIm f 1)^(z)

/-- Rewrite for `InterpStrip` when `0 < sSupNormIm f 0` and `0 < sSupNormIm f 1`. -/
lemma interpStrip_eq_of_pos (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1) :
    interpStrip f z = (sSupNormIm f 0)^(1 - z) * (sSupNormIm f 1)^(z) := by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, if_false, or_false]

/-- Rewrite for `InterpStrip` when `0 = sSupNormIm f 0` or `0 = sSupNormIm f 1`. -/
lemma interpStrip_eq_of_zero (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0) :
    interpStrip f z = 0 :=
  if_pos h

/-- Rewrite for `InterpStrip` on the open vertical strip. -/
lemma interpStrip_eq_on_Strip (z : ℂ) (hz : z ∈ verticalStrip 0 1):
    interpStrip f z = (sSupNormIm f 0)^(1 - z) * (sSupNormIm f 1)^(z) := by
  by_cases h : ((sSupNormIm f 0) = 0 ∨ (sSupNormIm f 1) = 0)
  · rw [interpStrip_eq_of_zero _ h]
    cases' h with h0 h1
    · simp only [h0, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ne_eq, true_and, ofReal_eq_zero]
      left
      rw [sub_eq_zero, eq_comm]
      simp only [ne_eq, ext_iff, one_re, ne_of_lt hz.2, or_iff_left, false_and, not_false_eq_true]
    · simp only [h1, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq, true_and]
      right
      rw [eq_comm]
      simp only [ne_eq, ext_iff, zero_re, ne_of_lt hz.1, or_iff_left, false_and, not_false_eq_true]
  · push_neg at h
    replace h : (0 < sSupNormIm f 0) ∧ (0 < sSupNormIm f 1) := by
      exact ⟨(lt_of_le_of_ne (sSupNormIm_nonneg f 0) (ne_comm.mp h.1)),
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact interpStrip_eq_of_pos f h.1 h.2

lemma diffContOnCl_interpStrip (f : ℂ → E) :
    DiffContOnCl ℂ (interpStrip f) (verticalStrip 0 1) := by
  by_cases h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  -- Case everywhere 0
  · eta_expand; simp_rw [interpStrip_eq_of_zero f h]; exact diffContOnCl_const
  -- Case nowhere 0
  · push_neg at h
    cases' h with h0 h1
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    eta_expand
    simp_rw [interpStrip_eq_of_pos f (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.const_sub (differentiableAt_id') 1) _
      left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · apply differentiableAt_id'
      · left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]

lemma norm_le_interp_on_closedStrip_eps (ε : ℝ) (hε : ε > 0)
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1)))
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) (hz : z ∈ verticalClosedStrip 0 1) :
  ‖f z‖ ≤  ‖((ε + sSupNormIm f 0)^(1-z) * (ε + sSupNormIm f 1)^(z) : ℂ)‖ := by
  simp only [F, abs_invInterpStrip _ _ hε, norm_smul, norm_mul, norm_eq_abs]
  repeat rw [← ofReal_add]
  repeat rw [abs_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp only [sub_re, one_re]
  rw [← mul_inv_le_iff, ← one_mul (((ε + sSupNormIm f 1) ^ z.re)), ← mul_inv_le_iff',
    ← Real.rpow_neg_one, ← Real.rpow_neg_one]
  · simp only [← Real.rpow_mul (le_of_lt (sSupNormIm_eps_pos f hε _)),
    mul_neg, mul_one, neg_sub, mul_assoc]
    simpa [F, abs_invInterpStrip _ _ hε, norm_smul, mul_comm] using
      norm_mul_invInterpStrip_le_one_on_closedStrip f ε hε z hd hB hz
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) z.re]
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) (1-z.re)]

lemma eventuallyle (f : ℂ → E) (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1)))
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) (hz : z ∈ verticalStrip 0 1) :
    (fun _ : ℝ ↦ ‖f z‖) ≤ᶠ[nhdsWithin 0 (Ioi 0)]
    (fun ε ↦ ‖((ε + sSupNormIm f 0)^(1-z) * (ε + sSupNormIm f 1)^(z) : ℂ)‖ ) := by
  rw [EventuallyLE, eventually_nhdsWithin_iff, eventually_nhds_iff]
  use Ioo (-1) 1
  refine ⟨ ?_, ⟨isOpen_Ioo, by simp only [mem_Ioo, Left.neg_neg_iff, zero_lt_one, and_self]⟩⟩
  simp only [comp_apply, mem_Ioo, mem_Ioi, and_imp] at *
  · intro x _ _ hnezero
    exact norm_le_interp_on_closedStrip_eps f x (hnezero) hB hd
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))

lemma norm_le_interp_on_strip_zero (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) :
    ∀ z ∈ verticalStrip 0 1, ‖f z‖ ≤ ‖interpStrip f z‖ := by
  intro z hz
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f hB hd hz)
  · apply tendsto_inf_left
    simp only [tendsto_const_nhds_iff]
  -- Proof that we can let epsilon tend to zero.
  · rw [interpStrip_eq_on_Strip _ _ hz]
    convert ContinuousWithinAt.tendsto _ using 2
    · simp only [ofReal_zero, zero_add]
    · simp_rw [← ofReal_add, norm_eq_abs]
      have : ∀ x ∈ (Ioi 0), (x + sSupNormIm f 0) ^ (1 - z.re) * (x + (sSupNormIm f 1)) ^ z.re
          = abs (↑(x + sSupNormIm f 0) ^ (1 - z) * ↑(x + sSupNormIm f 1) ^ (z)) := by
              intro x hx
              simp only [map_mul]
              repeat rw [abs_cpow_eq_rpow_re_of_nonneg (le_of_lt (sSupNormIm_eps_pos f hx _)) _]
              · simp only [sub_re, one_re]
              · simpa using (ne_comm.mpr (ne_of_lt hz.1))
              · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))
      apply tendsto_nhdsWithin_congr this _
      simp only [zero_add]
      rw [map_mul, abs_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _,
        abs_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]
      · apply Tendsto.mul
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 0)]
            exact Tendsto.add_const (sSupNormIm f 0) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.2]
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 1)]
            exact Tendsto.add_const (sSupNormIm f 1) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.1]
      · simpa using (ne_comm.mpr (ne_of_lt hz.1))
      · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))

/--
**Hadamard three-line theorem** on `[0,1]`: If `f` is a bounded function, continuous on `[0,1]`
and differentiable on `(0,1)`, then for `M(x) := sup ((norm ∘ f) '' (re ⁻¹' {x}))` we have that
`∀ z ∈ [0,1]` the inequality `|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|` holds. -/
lemma norm_le_interp_on_closedStrip (f : ℂ → E) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip 0 1))) :
    ‖f z‖ ≤ ‖interpStrip f z‖ := by
  apply le_on_closure (norm_le_interp_on_strip_zero f hd hB)
    (Continuous.comp_continuousOn' continuous_norm hd.2)
    (Continuous.comp_continuousOn' continuous_norm (diffContOnCl_interpStrip f).2)
  rwa [verticalClosedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz

end HadamardThreeLines
end Complex
