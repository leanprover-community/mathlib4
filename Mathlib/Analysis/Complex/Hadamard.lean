/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Hadamard three-lines Theorem

In this file we present a proof of a special case Hadamard's three-lines Theorem.

## Main result

- `abs_le_interp_on_closed_strip` :
Hadamard three-line theorem on `re ⁻¹' [0,1]`: If `f` is a bounded function, continuous on
`re ⁻¹' [0,1]` and differentiable on `re ⁻¹' (0,1)`, then for
`M(x) := sup ((norm ∘ f) '' (re ⁻¹' {x}))`, that is `M(x)` is the supremum of the absolute value of
`f` along the vertical lines `re z = x`, we have that `∀ z ∈ re ⁻¹' [0,1]` the inequality
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|` holds. This can be seen to be equivalent to the statement
that `log M(re z)` is a convex function on `[0,1]`.

## Main definitions

- `Complex.HadamardThreeLines.strip` : The vertical strip defined by : `re ⁻¹' Ioo a b`

- `Complex.HadamardThreeLines.closedStrip` : The vertical strip defined by : `re ⁻¹' Icc a b`

- `Complex.HadamardThreeLines.sSupAbsIm` :
    The supremum function on vertical lines defined by : `sSup {|f(z)| : z.re = x}`

- `Complex.HadamardThreeLines.invInterpStrip` :
    Inverse of the interpolation between the `sSupAbsIm` on the edges of the strip.

- `Complex.HadamardThreeLines.F` :
    Function defined by `f` times `invInterpStrip`. Convenient form for proofs.

- `Complex.HadamardThreeLines.cocompactStrip` :
    The filter along the vertical strip `re ⁻¹' Ioo a b` and `|z.im| atTop`.

- `Complex.HadamardThreeLines.transl`
    A function translated by a constant `ε`.

## References

The proof follows from Phragmén-Lindelöf when both frontiers are not everywhere zero.
We then use a limit argument to cover the case when either of the sides are `0`.
-/


open Set Filter Function Complex

namespace Complex
namespace HadamardThreeLines
variable (z : ℂ)

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b`. -/
def strip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Ioo a b

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b`. -/
def closedStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Icc a b

/-- The supremum of the absolute value of `f` on imaginary lines. (Fixed real part)
This is also known as the function `M` -/
noncomputable def sSupAbsIm [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (x : ℝ) : ℝ :=
  sSup ((norm ∘ f) '' (re ⁻¹' {x}))

section invInterpStrip

variable [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)
variable (h0 : 0 < sSupAbsIm f 0) (h1 : 0 < sSupAbsIm f 1)

/--
The inverse of the interpolation of `sSupAbsIm` on the two boundaries.
In other words, this is the inverse of the right side of the target inequality:
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|`. -/
noncomputable def invInterpStrip (z : ℂ) : ℂ :=
  (sSupAbsIm f 0)^(z-1) * (sSupAbsIm f 1)^(-z)

/-- A function useful for the proofs steps. We will aim to show that it is bounded by 1. -/
noncomputable def F := fun z ↦ invInterpStrip f z • f z

/-- `sSup` of `abs` is nonneg applied to the image of `f` on the vertical line `re z = x` -/
lemma sSupAbsIm_nonneg (x : ℝ) : 0 ≤ sSupAbsIm f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

/-- The function `invInterpStrip` is `diffContOnCl`. -/
lemma diffContOnCl_invInterpStrip : DiffContOnCl ℂ (invInterpStrip f) (strip 0 1) := by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const (differentiable_id') 1) _
    left; simpa using ne_of_gt h0
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id')
    simp only [ne_eq, ofReal_eq_zero, neg_eq_zero, Or.inl (ne_of_gt h1)]

/-- The function `f` is bounded by `sSupAbsIm`. (`f` is bounded on its domain.) -/
lemma abs_le_sSupAbsIm (z : ℂ) (hD : z ∈ (closedStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1))) : norm (f z) ≤ sSupAbsIm f (z.re) := by
  refine le_csSup ?_ ?_
  · apply BddAbove.mono (image_subset (norm ∘ f) _) hB
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

/-- The function `F` is bounded above because `f` is. -/
lemma F_BddAbove (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1))) :
    BddAbove ((norm ∘ (F f)) '' (closedStrip 0 1)) := by
 -- Rewriting goal
  simp only [F, image_congr, comp_apply, map_mul, invInterpStrip]
  rw [bddAbove_def] at *
  cases' hB with B hB
  -- Using bound
  use ((max 1 ((sSupAbsIm f 0)^ (-(1 : ℝ)))) * max 1 ((sSupAbsIm f 1)^ (-(1 : ℝ)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intros z hset
  specialize hB (norm (f z))
  specialize hB _
  · simp only [image_congr, mem_image, comp_apply]; use z
  -- Proof that the bound is correct
  · rw [norm_smul]
    apply mul_le_mul _ hB (norm_nonneg _) _
    · rw [norm_mul]
      apply mul_le_mul _ _ (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))
      -- Bounding individual terms
      · by_cases hM0_one : 1 ≤ sSupAbsIm f 0
        -- `1 ≤ (sSupAbsIm f 0)`
        · apply le_trans _ (le_max_left _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos h0, sub_re, one_re,
          Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
        -- `0 < (sSupAbsIm f 0) < 1`
        · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos h0, sub_re, one_re]
          apply Real.rpow_le_rpow_of_exponent_ge (h0) (le_of_lt hM0_one) _
          simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
      · by_cases hM1_one : 1 ≤ sSupAbsIm f 1
        -- `1 ≤ sSupAbsIm f 1`
        · apply le_trans _ (le_max_left _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos h1, sub_re, one_re, neg_re,
          Real.rpow_le_one_of_one_le_of_nonpos hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
        -- `0 < sSupAbsIm f 1 < 1`
        · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
          simp only [norm_eq_abs, abs_cpow_eq_rpow_re_of_pos h1, sub_re, one_re, neg_re,
          Real.rpow_le_rpow_of_exponent_ge (h1) (le_of_lt hM1_one)
            (neg_le_neg_iff.mpr hset.2)]
    simp only [gt_iff_lt, lt_max_iff, zero_lt_one, true_or, mul_nonneg_iff_of_pos_left, le_max_iff,
      zero_le_one]

-- Proof that the edges are bounded by one
lemma F_edge_le_one (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1)))
    (hz : z ∈ re ⁻¹' {0, 1}) : ‖F f z‖ ≤ 1 := by
  simp only [F, invInterpStrip, norm_smul, norm_eq_abs, map_mul, abs_cpow_eq_rpow_re_of_pos,
    h0, h1, sub_re, one_re, neg_re]
  cases' hz with hz0 hz1
  -- `z.re = 0`
  · simp [hz0, mul_one, zero_sub, Real.rpow_zero, neg_zero,
    Real.rpow_neg_one, inv_mul_le_iff h0]
    rw [← hz0]
    apply abs_le_sSupAbsIm f z _ hB
    simp only [closedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
    inv_mul_le_iff h1, mul_one]
    rw [← hz1]
    apply abs_le_sSupAbsIm f z _ hB
    simp only [closedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

theorem abs_mul_invInterpStrip_le_one_on_closedStrip
    (hd : DiffContOnCl ℂ f (strip 0 1)) (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1)))
    (z : ℂ) (hz : z ∈ closedStrip 0 1) : ‖F f z‖ ≤ 1 := by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f h0 h1) hd) _
    (fun x hx ↦ F_edge_le_one x f h0 h1 hB (Or.inl hx))
    (fun x hx ↦ F_edge_le_one x f h0 h1 hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero, div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f h0 h1 hB
  simp [mem_upperBounds] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply eventually_of_forall
  intro x hx
  norm_num
  apply le_trans (hBF x ((preimage_mono Ioo_subset_Icc_self) hx))
    (le_trans (le_of_lt (lt_add_one BF)) (Real.add_one_le_exp BF))

end invInterpStrip

-----

variable [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)
variable (z : ℂ)

noncomputable def interpStrip : ℂ :=
  if (sSupAbsIm f (0 : ℝ)) = (0 : ℝ) ∨ (sSupAbsIm f (1 : ℝ)) = (0 : ℝ)
    then 0
    else (sSupAbsIm f 0)^(1-z) * (sSupAbsIm f 1)^(z)

/-- Rewrite for `InterpStrip` when `0 < sSupAbsIm f 0` and `0 < sSupAbsIm f 1`. -/
lemma interpStrip_eq_of_pos (h0 : 0 < sSupAbsIm f 0) (h1 : 0 < sSupAbsIm f 1) :
    interpStrip f z = (sSupAbsIm f 0)^(1-z) * (sSupAbsIm f 1)^(z) := by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, if_false, or_false]

/-- Rewrite for `InterpStrip` when `0 = sSupAbsIm f 0` or `0 = sSupAbsIm f 1`. -/
lemma interpStrip_eq_of_zero (h : (sSupAbsIm f 0) = 0 ∨ (sSupAbsIm f 1) = 0) :
    interpStrip f z = 0 :=
  if_pos h

lemma abs_le_interp_on_closedStrip_pos (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1)))
    (hd : DiffContOnCl ℂ f (strip 0 1)) (hz : z ∈ closedStrip 0 1) (h0 : 0 < sSupAbsIm f 0)
    (h1 : 0 < sSupAbsIm f 1) : norm (f z) ≤ norm (interpStrip f z ) := by
  rw [interpStrip_eq_of_pos _ _ h0 h1]
  obtain h := abs_mul_invInterpStrip_le_one_on_closedStrip f h0 h1 hd hB z hz
  simp only [F, invInterpStrip, norm_smul, norm_mul, norm_eq_abs] at *
  rw [← mul_inv_le_iff, ← one_mul (abs (↑(sSupAbsIm f 1) ^ z)), ← mul_inv_le_iff',
  ← Real.rpow_neg_one, ← Real.rpow_neg_one,← abs_cpow_real, ← abs_cpow_real]
  · simp only [ofReal_neg, ofReal_one, cpow_neg_one, cpow_neg_one,
      ← cpow_neg, ← cpow_neg, neg_sub, mul_assoc]
    rwa [mul_comm]
  · simp only [abs_cpow_eq_rpow_re_of_pos h1, Real.rpow_pos_of_pos h1 z.re]
  · simp only [abs_cpow_eq_rpow_re_of_pos h0, Real.rpow_pos_of_pos h0 (1-z).re]

section transl

/-
  This section introduces the translation function:
  `tansl (f : ℂ → ℂ) (ε : ℂ) := fun z ↦ f z + ε`,
  which allows us to take simple limits. The goal is to obtain the general case
  from `abs_le_interp_on_closedStrip_pos` by using `tendsto_le_of_eventuallyLE`.

  This lst lemma requires that the function are continuous. Since the function `interpStrip`
  constains supremums, it is not trivial to show continuity. We then establish first some lemmas
  `sSupAbsIm_of_transl_le_transl_of_sSupAbsIm`, `sSupAbsIm_le_transl_of_sSupAbsIm_of_transl`
  and `transl_sub_sSupAbsIm_le_transl_of_sSupAbsIm` that will be used to prove continuity.

  Next, as we take the limit, we need that the sequence retains the property that
  `0 < sSupAbsIm f 0` and `0 < sSupAbsIm f 1` as they approach `0`. This is the purpose of
  the lemma `sSupAbsIm_transl_nhds_zero_pos`, which garantees it in an open set around 0.

  Finally, this only holds on the open strip, so we use a continuity argument once again
  to get the whole strip.
 -/

variable (ε : E)
def transl := fun z ↦ f z + ε

lemma transl_def : (transl f ε) = fun z ↦ f z + ε := by
  rfl

lemma transl_DiffCont (hd : DiffContOnCl ℂ f (strip 0 1)) :
    DiffContOnCl ℂ (transl f ε) (strip 0 1) :=
  DiffContOnCl.add_const hd ε

variable (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1)))

/-image_eq_range-/

instance ClosedStrip.instNonempty : Nonempty (closedStrip 0 1) := by
  use 0
  simp [HadamardThreeLines.closedStrip]

lemma transl_BddAbove : BddAbove ((norm ∘ (transl f ε)) '' (closedStrip 0 1)) := by
  rw [image_eq_range] at *
  apply BddAbove.range_mono _ (fun _ ↦ norm_add_le _ _) (BddAbove.range_add hB _)
  rw [range_const]
  exact bddAbove_singleton

lemma sSupAbsIm_of_transl_le_transl_of_sSupAbsIm (w : ℝ) (hset: w ∈ Icc 0 1) :
    sSupAbsIm (transl f ε) w ≤ sSupAbsIm f w + norm ε := by
  apply csSup_le _ _
  · simp only [image_nonempty, Nonempty.preimage (singleton_nonempty _) re_surjective];
  intros b hset;
  obtain ⟨x, hxset, hb⟩ := hset
  rw [← hb]
  apply le_trans (norm_add_le (f x) ε)
  simp only [add_le_add_iff_right]
  apply le_csSup
    (BddAbove.mono (image_subset _ (preimage_mono (singleton_subset_iff.mpr hset))) hB) _
  simpa using mem_image_of_mem (norm ∘ f) hxset

lemma sSupAbsIm_le_transl_of_sSupAbsIm_of_transl (w : ℝ) (hset: w ∈ Icc 0 1) :
    sSupAbsIm f w  ≤ sSupAbsIm (transl f ε) w + norm ε := by
  simpa [transl_def, add_neg_cancel_right, norm_neg]
    using sSupAbsIm_of_transl_le_transl_of_sSupAbsIm (transl f ε) (-ε)
      (transl_BddAbove f ε hB) w hset

lemma transl_sub_sSupAbsIm_le_transl_of_sSupAbsIm (w : ℝ) (hset: w ∈ Icc 0 1) :
    norm ε - sSupAbsIm f w  ≤ sSupAbsIm (transl f ε) w := by
  have : norm (f w + ε) ∈ (fun a ↦ norm (f a + ε)) '' (re ⁻¹' {w}) := by
    use w; simp only [mem_preimage, ofReal_re, mem_singleton_iff, and_self]
  apply le_trans _ (le_csSup (BddAbove.mono (image_subset _ (preimage_mono
    (singleton_subset_iff.mpr hset))) (transl_BddAbove f  ε hB)) this)
  rw [add_comm]
  apply le_trans _ (tsub_le_iff_right.mpr (norm_le_add_norm_add ε (f w)))
  rw [sub_le_sub_iff_left]
  apply le_csSup
    (BddAbove.mono (image_subset _ (preimage_mono (singleton_subset_iff.mpr hset))) hB) _
  use w
  simp only [mem_preimage, ofReal_re, mem_singleton_iff, comp_apply, and_self]

lemma Continuous_sSupAbsIm_transl_zero (w : ℝ) (hset: w ∈ Icc 0 1) :
    Tendsto (fun ε => sSupAbsIm (transl f ε) w) (nhds 0) (nhds (sSupAbsIm f w)) := by
  simp_rw [sSupAbsIm, transl_def, comp_apply, Metric.tendsto_nhds_nhds, dist_eq_norm_sub]
  simp only [gt_iff_lt, sub_zero, Real.norm_eq_abs]
  intros ε hε
  use ε
  refine ⟨hε, ?_⟩
  intro x hx
  by_cases h : (sSup ((fun a => norm (f a + x)) '' (re ⁻¹' {w}))
              - sSup ((fun a => norm (f a)) '' (re ⁻¹' {w}))) > 0
  · rw [abs_of_pos h, sub_lt_iff_lt_add']
    apply lt_of_le_of_lt (sSupAbsIm_of_transl_le_transl_of_sSupAbsIm f x hB w hset)
      ((add_lt_add_iff_left _).mpr hx)
  · simp only [gt_iff_lt, not_lt] at h;
    rw [abs_of_nonpos h, neg_sub, sub_lt_iff_lt_add'];
    apply lt_of_le_of_lt (sSupAbsIm_le_transl_of_sSupAbsIm_of_transl f x hB w hset)
      ((add_lt_add_iff_left _).mpr hx)

lemma sSupAbsIm_transl_nhds_zero_pos :
    ∃ T > 0, ∀ ε ∈ {0}ᶜ ∩ Metric.ball 0 (T),
    ((sSupAbsIm (transl f ε) 0) > 0) ∧ ((sSupAbsIm (transl f ε) 1) > 0) := by
  -- The proofs of the two possible cases
  have hc_pos (r : ℝ) (ε : E) (hε_r: norm ε < sSupAbsIm f r) (hset : r ∈ Icc 0 1) :
      0 < sSupAbsIm (transl f ε) r := by
    exact lt_of_lt_of_le (sub_pos.mpr hε_r) (tsub_le_iff_right.mpr
      (sSupAbsIm_le_transl_of_sSupAbsIm_of_transl f ε hB r (hset)))
  have hc_zero (r : ℝ) (ε : E) (hε_r: 0 = sSupAbsIm f r) (hset : r ∈ Icc 0 1) (hε_ne_zero: ¬ε = 0) :
      0 < sSupAbsIm (transl f ε) r := by
    apply lt_of_lt_of_le _ (transl_sub_sSupAbsIm_le_transl_of_sSupAbsIm f ε hB r (hset))
    simp_rw [sSupAbsIm, comp_apply] at hε_r;
    simpa [← hε_r, sSupAbsIm]
  -- Using the proofs in the cases
  cases' lt_or_eq_of_le (sSupAbsIm_nonneg f 0) with h0pos h0zero
  · cases' lt_or_eq_of_le (sSupAbsIm_nonneg f 1) with h1pos h1zero
    · use min (sSupAbsIm f 0) (sSupAbsIm f 1)
      simp [h0pos, h1pos]
      exact fun ε _ hε_0 hε_1 ↦ ⟨hc_pos 0 ε hε_0 (Set.left_mem_Icc.mpr zero_le_one),
        hc_pos 1 ε hε_1 (Set.right_mem_Icc.mpr zero_le_one) ⟩
    use sSupAbsIm f 0
    simp [h0pos]
    exact fun ε hε_ne_zero hε_0 ↦ ⟨hc_pos 0 ε hε_0 (Set.left_mem_Icc.mpr zero_le_one),
        hc_zero 1 ε h1zero (Set.right_mem_Icc.mpr zero_le_one) hε_ne_zero⟩
  cases' lt_or_eq_of_le (sSupAbsIm_nonneg f 1) with h1pos h1zero
  · use sSupAbsIm f 1
    simp [h1pos]
    exact fun ε hε_ne_zero hε_1 ↦
      ⟨hc_zero 0 ε h0zero (Set.left_mem_Icc.mpr zero_le_one) hε_ne_zero,
      hc_pos 1 ε hε_1 (Set.right_mem_Icc.mpr zero_le_one)⟩
  use 1
  simp
  exact fun ε hε_ne_zero _ ↦ ⟨hc_zero 0 ε h0zero (Set.left_mem_Icc.mpr zero_le_one) hε_ne_zero,
      hc_zero 1 ε h1zero (Set.right_mem_Icc.mpr zero_le_one) hε_ne_zero⟩

lemma interpStrip_nhds_zero_pos :
    ∃ T > 0, ∀ ε ∈ {0}ᶜ ∩ Metric.ball 0 (T), norm ((sSupAbsIm (transl f ε) 0 : ℂ)^(1-z) *
      (sSupAbsIm (transl f ε) 1)^(z)) = norm (interpStrip (transl f ε) z ) := by
  obtain ⟨T, hTpos, hT⟩ := sSupAbsIm_transl_nhds_zero_pos f hB
  use T
  refine ⟨hTpos, ?_⟩
  intro ε hε
  simp only [(eq_comm.mp (interpStrip_eq_of_pos _ _ (hT ε hε).1 (hT ε hε).2))]

lemma eventuallyle (hd : DiffContOnCl ℂ f (strip 0 1)) (hz : z ∈ strip 0 1) :
    (fun ε ↦ norm ((transl f ε) z))
      ≤ᶠ[nhdsWithin 0 {0}ᶜ] (fun ε ↦ norm (interpStrip (transl f ε) z)) := by
  obtain ⟨T, hTpos, hT⟩ := sSupAbsIm_transl_nhds_zero_pos f hB
  rw [EventuallyLE, eventually_nhdsWithin_iff, eventually_nhds_iff]
  use Metric.ball 0 T
  refine ⟨ ?_, ⟨Metric.isOpen_ball, Metric.mem_ball_self hTpos⟩⟩
  · intro x hx hnezero
    exact abs_le_interp_on_closedStrip_pos _ _ (transl_BddAbove f x hB) (transl_DiffCont f x hd)
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))
       (hT x ⟨hnezero, hx⟩).1 (hT x ⟨hnezero, hx⟩).2

lemma tendsto_interpStrip_pos (hz: z ∈ strip 0 1) : ContinuousAt (fun ε =>
    norm (↑(sSupAbsIm (transl f ε) 0 : ℂ) ^ (1 - z) * ↑(sSupAbsIm (transl f ε) 1 : ℂ) ^ z)) 0 := by
  simp only [norm_mul, norm_eq_abs]
  simp_rw [abs_cpow_eq_rpow_re_of_nonneg (sSupAbsIm_nonneg _ _) (ne_comm.mp (ne_of_lt hz.1))]
  simp_rw [abs_cpow_eq_rpow_re_of_nonneg (sSupAbsIm_nonneg _ _)
    (show (1-z).re ≠ 0 by exact ne_comm.mp (ne_of_lt (sub_pos.mpr hz.2)))]
  apply ContinuousAt.mul
  · apply ContinuousAt.rpow_const _ _
    · apply continuousAt_of_tendsto_nhds
      exact Continuous_sSupAbsIm_transl_zero _ hB 0 (left_mem_Icc.mpr zero_le_one)
    simp only [or_true, sub_re, one_re, sub_nonneg, le_of_lt, hz.2]
  · apply ContinuousAt.rpow_const _ _
    · apply continuousAt_of_tendsto_nhds
      exact Continuous_sSupAbsIm_transl_zero _ hB 1 (right_mem_Icc.mpr zero_le_one)
    simp only [or_true, le_of_lt, hz.1]

lemma Tendsto_interpStrip (hz: z ∈ strip 0 1) (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) :
    Tendsto (fun ε => norm (interpStrip (transl f ε) z)) (nhdsWithin 0 {0}ᶜ)
    (nhds (norm (interpStrip f z))) := by
  obtain ⟨T, hTpos, hT⟩ := interpStrip_nhds_zero_pos f z hB
  rw [nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ hTpos)]
  have : (interpStrip f z) =
      (↑(sSupAbsIm (transl f 0) 0) ^ (1 - z) * ↑(sSupAbsIm (transl f 0) 1) ^ z) := by
    rw [strip, mem_preimage, mem_Ioo] at hz
    simp [- ne_eq, interpStrip_eq_of_zero f _ h]
    rw [transl_def]; simp
    cases' h with h1 h2
    · left
      refine ⟨h1, ?_⟩
      rw [sub_eq_zero, eq_comm]
      simp only [ne_eq, ext_iff, one_re, ne_of_lt hz.2, or_iff_left, false_and, not_false_eq_true]
    right
    refine ⟨h2, ?_ ⟩
    rw [eq_comm]
    simp only [ne_eq, ext_iff, zero_re, ne_of_lt hz.1, or_iff_left, false_and, not_false_eq_true]
  rw [this]
  apply tendsto_nhdsWithin_congr hT (tendsto_nhdsWithin_of_tendsto_nhds
    (ContinuousAt.tendsto (tendsto_interpStrip_pos _ _ hB hz)))

end transl

variable (hB : BddAbove ((norm ∘ f) '' (closedStrip 0 1))) (hd : DiffContOnCl ℂ f (strip 0 1))

/-  This condition is required for the limit arguement and is met for example
    when we have `[Nontrivial E]`. -/
variable [Filter.NeBot (nhdsWithin (0 : E) {0}ᶜ)]

lemma abs_le_interp_on_strip_zero (hz : z ∈ strip 0 1)
    (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) : norm (f z) ≤ norm (interpStrip f z) := by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · apply tendsto_inf_left
    apply Continuous.tendsto'
      (Continuous.comp continuous_norm (Continuous.add continuous_const continuous_id))
    simp only [id_eq, comp_apply, add_zero]
  · apply Tendsto_interpStrip f z hB hz h

lemma abs_eq_zero_on_strip (hz : z ∈ strip 0 1)
    (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) : f z = 0 := by
  rw [← norm_eq_zero]
  apply le_antisymm _ (norm_nonneg _)
  simpa [interpStrip_eq_of_zero f z h, map_zero] using
    abs_le_interp_on_strip_zero f z hB hd hz h

lemma abs_eq_zero_on_closedStrip (hz : z ∈ closedStrip 0 1)
    (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) : norm (f z) = 0 := by
  have : f '' strip 0 1 = {0} := by
    ext; constructor
    · intro ⟨a, ⟨ha1, ha2⟩⟩
      rw [← ha2]
      exact abs_eq_zero_on_strip f a hB hd ha1 h
    · intro hx; rw [hx]; use (1/2 : ℚ);
      have : ((1/2: ℚ): ℂ) ∈ strip 0 1 := by rw [strip, mem_preimage, rat_cast_re]; norm_num;
      exact ⟨this, abs_eq_zero_on_strip f ((1/2: ℚ): ℂ) hB hd this h⟩
  have : closure (f '' strip 0 1) = {0} := by simp only [this, closure_singleton]
  simp only [norm_eq_zero]
  apply eq_of_mem_singleton
  rw [closedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz
  rw [←this]
  apply ContinuousWithinAt.mem_closure_image
    (ContinuousWithinAt.mono (ContinuousOn.continuousWithinAt hd.2 hz) subset_closure) hz

/--
**Hadamard three-line theorem** on `[0,1]`: If `f` is a bounded function, continuous on `[0,1]`
and differentiable on `(0,1)`, then for `M(x) := sup ((norm ∘ f) '' (re ⁻¹' {x}))` we have that
`∀ z ∈ [0,1]` the inequality `|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|` holds.
-/
theorem abs_le_interp_on_closedStrip (hz : z ∈ closedStrip 0 1) :
    norm (f z) ≤ norm (interpStrip f z) := by
  by_cases h : (sSupAbsIm f 0) = 0 ∨ (sSupAbsIm f 1) = 0
  · rw [interpStrip_eq_of_zero f z h]
    simp only [norm_zero];
    exact le_of_eq (abs_eq_zero_on_closedStrip f z hB hd hz h)
  · push_neg at h
    replace h : (0 < sSupAbsIm f 0) ∧ (0 < sSupAbsIm f 1) := by
      exact ⟨(lt_of_le_of_ne (sSupAbsIm_nonneg f 0) (ne_comm.mp h.1)),
      (lt_of_le_of_ne (sSupAbsIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact abs_le_interp_on_closedStrip_pos _ _ hB hd hz h.1 h.2


end HadamardThreeLines
end Complex
