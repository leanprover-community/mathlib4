/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Hadamard three-lines Theorem

In this file we present a proof of a special case Hadamard's three-lines Theorem.
We think this result generalises well by a change of variables.

## Main result

- `abs_le_interp_on_closed_strip` :
Hadamard three-line theorem on `re ⁻¹' [0,1]`: If `f` is a bounded function, continuous on
`re ⁻¹' [0,1]` and differentiable on `re ⁻¹' (0,1)`, then for
`M(x) := sup ((abs ∘ f) '' (re ⁻¹' {x}))`, that is `M(x)` is the supremum of the absolute value of
`f` along the vertical lines `re z = x`, we have that `∀ z ∈ re ⁻¹' [0,1]` the inequality
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|` holds. This can be seen to be equivalent to the statement
that `log M(re z)` is a convex function on `[0,1]`.

## Main definitions

- `Complex.HadamardThreeLines.strip` : The vertical strip defined by : `re ⁻¹' Ioo a b`

- `Complex.HadamardThreeLines.closedStrip` : The vertical strip defined by : `re ⁻¹' Icc a b`

- `Complex.HadamardThreeLines.bddStrip` :
    The rectangle defined by : `re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T`

- `Complex.HadamardThreeLines.closedBddStrip` :
    The rectangle defined by : `re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T`

- `Complex.HadamardThreeLines.sSupAbsIm` :
    The supremum function on vertical lines defined by : `sSup {|f(z)| : z.re = x}`

- `Complex.HadamardThreeLines.invInterpStrip` :
    Inverse of the interpolation between the `sSupAbsIm` on the edges of the strip.

- `Complex.HadamardThreeLines.F` :
    Function defined by `f` times `invInterpStrip`. Convenient form for proofs.

- `Complex.HadamardThreeLines.F'` :
    'Easy' function converging to `F`.

- `Complex.HadamardThreeLines.cocompactStrip` :
    The filter along the vertical strip `re ⁻¹' Ioo a b` and `|z.im| atTop`.

## References

This proof follows loosely the proof found on the wiki page :
[wiki](https://en.wikipedia.org/wiki/Hadamard_three-lines_theorem)

-/


open Set Filter Function Complex

namespace Complex
namespace HadamardThreeLines
variable (z : ℂ) (C: CompleteSpace ℂ)

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b`. -/
def strip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Ioo a b

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b`. -/
def closedStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Icc a b

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b` and
`z.im ∈ Ioo (-T) T`. -/
def bddStrip (a : ℝ) (b : ℝ) (T : ℝ) : Set ℂ :=  re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b` and
`z.im ∈ Icc (-T) T`. -/
def closedBddStrip (a : ℝ) (b : ℝ) (T : ℝ) : Set ℂ :=  re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T

/-- The filter along the vertical strip `re ⁻¹' Icc a b` and `|z.im| atTop` -/
def cocompactStrip (a b : ℝ) : Filter ℂ :=
  comap im (cocompact ℝ) ⊓ (comap re (principal (Icc a b)))

/-- The supremum of the absolute value of `f` on imaginary lines. (Fixed real part)
This is also known as the function `M` -/
noncomputable def sSupAbsIm (f : ℂ → ℂ) (x : ℝ) : ℝ  :=  sSup ((abs ∘ f) '' (re ⁻¹' {x}))

/--
The inverse of the interpolation of `sSupAbsIm` on the two boundaries.
In other words, this is the inverse of the right side of the target inequality:
`|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|`.
 -/
noncomputable def invInterpStrip (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if (sSupAbsIm f (0 : ℝ)) = (0 : ℝ) ∨ (sSupAbsIm f (1 : ℝ)) = (0 : ℝ)
    then 0
    else (sSupAbsIm f 0)^(z-1) * (sSupAbsIm f 1)^(-z)

/-- A function useful for the proofs steps. We will aim to show that it is bounded by 1. -/
noncomputable def F (f : ℂ → ℂ) := fun z ↦ f z • invInterpStrip f z

/-- Similar to `F` only 'easier'. Useful for proof steps. -/
noncomputable def F' (n : ℕ) (f : ℂ → ℂ) := fun z ↦ F f z • exp ((z^2-1) * (n : ℝ)⁻¹)


/-- `sSup` of `abs` is nonneg applied to the image of `f` on the vertical line `re z = x` -/
lemma sSupAbsIm_nonneg (f : ℂ → ℂ) (x : ℝ) : 0 ≤ sSupAbsIm f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, map_nonneg]

/-- Rewrite for `invInterpStrip` when `0 < sSupAbsIm f 0` and `0 < sSupAbsIm f 1`. -/
lemma invInterpStrip_eq_of_pos (f : ℂ → ℂ ) (h0 : 0 < sSupAbsIm f 0) (h1 : 0 < sSupAbsIm f 1) :
    invInterpStrip f z = (sSupAbsIm f 0)^(z-1) * (sSupAbsIm f 1)^(-z) := by
  simp only [ne_of_gt h0, ne_of_gt h1, invInterpStrip, if_false, or_false]

/-- Rewrite for `invInterpStrip` when `0 = sSupAbsIm f 0` or `0 = sSupAbsIm f 1`. -/
lemma invInterpStrip_eq_of_zero (f : ℂ → ℂ ) (h : (sSupAbsIm f 0) = 0 ∨ (sSupAbsIm f 1) = 0) :
    invInterpStrip f z = 0 :=
  if_pos h

/-- The function `invInterpStrip` is `diffContOnCl`. -/
lemma diffContOnCl_invInterpStrip (f : ℂ → ℂ) : DiffContOnCl ℂ (invInterpStrip f) (strip 0 1) := by
  by_cases (sSupAbsIm f 0) = 0 ∨ (sSupAbsIm f 1) = 0
  -- Case everywhere 0
  -- Starting with Lemma to handle rewriting of invInterpStrip as a function.
  · have hzero : invInterpStrip f = 0 := by
      rw [funext_iff]
      intro z
      simp only [invInterpStrip_eq_of_zero z f h, Pi.zero_apply, eq_self_iff_true]
    rw [hzero, Pi.zero_def]
    exact diffContOnCl_const
  -- Case nowhere 0
  · push_neg at h
    cases' h with h0 h1
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    -- Same strategy.
    have hpos: invInterpStrip f = fun (z : ℂ) ↦ (sSupAbsIm f 0)^(z-1) * (sSupAbsIm f 1)^(-z) := by
      funext z
      rw [invInterpStrip_eq_of_pos z f (lt_of_le_of_ne (sSupAbsIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupAbsIm_nonneg f 1) h1)]
    rw [hpos]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.sub_const (differentiableAt_id') 1) _
      left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · rw [differentiableAt_neg_iff]
        apply differentiableAt_id'
      · left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]

/-- The function `F'` is `diffContOnCl`. -/
lemma diffContOnCl_F' (f : ℂ → ℂ) (n : ℕ) (hd : DiffContOnCl ℂ f (strip 0 1)) :
    DiffContOnCl ℂ (F' n f) (strip 0 1) := by
  refine DiffContOnCl.smul (DiffContOnCl.smul hd (diffContOnCl_invInterpStrip f) )
    <| Differentiable.diffContOnCl <| Differentiable.cexp <| Differentiable.mul ?_
      (differentiable_const _)
  rw [differentiable_sub_const_iff]
  simp only [cpow_two, differentiable_id', Differentiable.pow]

/-- The function `f` is bounded by `sSupAbsIm`. (`f` is bounded on its domain.) -/
lemma abs_le_sSupAbsIm (f : ℂ → ℂ) (z : ℂ) (hD : z ∈ (closedStrip 0 1))
    (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1))) : abs (f z) ≤ sSupAbsIm f (z.re) := by
  refine le_csSup ?_ ?_
  · apply BddAbove.mono (image_subset (abs ∘ f) _) hB
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (abs ∘ f)
    simp only [mem_image_of_mem (abs ∘ f), mem_preimage, mem_singleton]

lemma cocompact_strip.basis : HasBasis (cocompactStrip 0 1) (fun _ : ℝ × ℝ ↦ True )
    (fun T ↦ (im ⁻¹' (Iic (T.1) ∪ Ici (T.2)) ∩ re ⁻¹' Icc 0 1)) := by
  simp only [cocompactStrip, comap_principal, Real.cocompact_eq]
  rw [← true_and True]
  exact HasBasis.inf_principal (HasBasis.comap _ (HasBasis.sup atBot_basis atTop_basis)) _

lemma cocompact_strip.mem_sets {s : Set ℂ} : s ∈ cocompactStrip 0 1 ↔ ∃ T, ∀ (z : ℂ),
    z.re ∈ Icc 0 (1 : ℝ) → T ≤ |z.im| → z ∈ s := by
  rw [HasBasis.mem_iff cocompact_strip.basis]
  constructor
  · rintro ⟨⟨a,b⟩, h⟩
    simp only [preimage_union, ge_iff_le, zero_le_one, not_true, gt_iff_lt, true_and] at h
    use max (-a) b
    intros z hset him
    apply h
    refine mem_inter ?_ hset
    simp only [mem_preimage, mem_Iic, mem_Ici, mem_union]
    simp only [abs_ofReal, max_le_iff] at him
    cases' him with hima himb
    by_cases 0 ≤ z.im
    · right; rwa [← _root_.abs_of_nonneg h]
    · left; rwa [← neg_le_neg_iff, ← abs_of_neg (not_le.mp h)]
  · rintro ⟨T, h⟩
    use (-T, T)
    simp only [preimage_union, true_and]
    rintro z ⟨him, hset⟩
    apply h _ hset
    rwa [le_abs, ← le_neg, or_comm, ← mem_Iic, ← mem_Ici,
      ← mem_union, ← mem_preimage, preimage_union]

lemma _root_.Real.tendsto_sq_cocompact_atTop : Tendsto (fun x ↦ x^2) (cocompact ℝ) atTop := by
  convert_to Tendsto (fun x ↦ ‖x‖ * ‖x‖) (cocompact ℝ) atTop
  · ext x; rw [pow_two]; exact (abs_mul_abs_self _).symm
  · exact tendsto_norm_cocompact_atTop.atTop_mul_atTop tendsto_norm_cocompact_atTop

lemma cocompact_strip.tendsto_sq_im_atTop :
    Tendsto (fun z : ℂ ↦ z.im^2) (cocompactStrip 0 1) atTop := by
  apply tendsto_inf_left _
  change Tendsto ((fun x ↦ x^2) ∘ im) (comap im (cocompact ℝ)) atTop
  rw [tendsto_comap'_iff]
  · convert_to Tendsto (fun x ↦ ‖x‖ * ‖x‖) (cocompact ℝ) atTop
    · ext x; simp only [Real.rpow_two, pow_two, Real.norm_eq_abs, abs_mul_abs_self]
    · exact tendsto_norm_cocompact_atTop.atTop_mul_atTop tendsto_norm_cocompact_atTop
  ·  simp only [univ_mem, range_im]

lemma cocompact_strip.eventually_sq_re_le_one :
    ∀ᶠ (z : ℂ) in (cocompactStrip 0 1), z.re^2 ≤ 1 := by
  rw [cocompactStrip, comap_principal, eventually_inf_principal]
  apply eventually_of_forall
  rintro z hz
  simp only [Real.rpow_two]
  rw [sq_le_one_iff hz.1]
  exact hz.2

-- Smoothly decreasing function when the real part is bounded eventually ≤ 1
lemma expterm_eventually_le_one (C : ℝ) (n : ℕ) (hn : 1 ≤ n) : ∀ᶠ (z : ℂ)
    in (comap Complex.im (cocompact ℝ) ⊓ (comap Complex.re (principal  (Icc 0 1)))),
    C * abs (exp ((z^(2 : ℕ)-1) * (n : ℝ)⁻¹)) ≤ 1 := by
  apply eventually_le_of_tendsto_lt  (zero_lt_one' ℝ) _
  simp only [abs_exp]
  have hz_re_im : (fun z : ℂ ↦ C * Real.exp (((z^(2 : ℕ)-1) * (n : ℝ)⁻¹).re))
      = (fun z : ℂ ↦ C * Real.exp ((z.re^(2 : ℕ) - z.im^(2 : ℕ) - 1) * (n : ℝ)⁻¹)) := by
    ext1 z
    nth_rewrite 1 [← re_add_im z]
    simp only [mul_re, sub_re, ofReal_im, mul_zero, tsub_zero, ofReal_re]
    rw [cpow_nat_cast, sq, mul_re]
    simp only [re_add_im, one_re, Nat.cast_ofNat, Real.rpow_two, mul_eq_mul_left_iff,
    Real.exp_eq_exp, mul_eq_mul_right_iff, sub_left_inj, inv_eq_zero, Nat.cast_eq_zero, sq]
  rw [hz_re_im]
  nth_rewrite 2 [← mul_zero C]
  apply Tendsto.const_mul C _
  rw [Real.tendsto_exp_comp_nhds_zero]
  apply Tendsto.atBot_mul_const (show 0 < (n : ℝ)⁻¹ by
    simp only [inv_pos, Nat.cast_pos, lt_of_lt_of_le zero_lt_one hn])
  -- x.re ^ 2 - x.im ^ 2 - 1 Tendsto at_bot
  apply tendsto_atBot_add_const_right _ (-1) _
  simp only [sub_eq_add_neg]
  apply tendsto_atBot_add_left_of_ge' _ (1 : ℝ) cocompact_strip.eventually_sq_re_le_one _
  rw [tendsto_neg_atBot_iff]
  exact cocompact_strip.tendsto_sq_im_atTop

/-- The function `F` is bounded above because `f` is. -/
lemma F_BddAbove (f : ℂ → ℂ) (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1))) :
    BddAbove ((abs ∘ F f) '' (closedStrip 0 1)) := by
  -- Rewriting goal
  simp only [F, image_congr, comp_apply, map_mul]
  rw [bddAbove_def] at *
  cases' hB with B hB
  -- Using bound
  use B * ((max 1 ((sSupAbsIm f 0)^ (-(1 : ℝ)))) * max 1 ((sSupAbsIm f 1)^ (-(1 : ℝ))))
  simp only [smul_eq_mul, map_mul, mem_image, forall_exists_index,
   and_imp, forall_apply_eq_imp_iff₂]
  intros z hset
  specialize hB (abs (f z))
  specialize hB _
  · simp only [image_congr, mem_image, comp_apply]; use z
  -- Proof that the bound is correct
  · apply mul_le_mul hB _ (map_nonneg abs _) (le_trans (map_nonneg abs _) hB)
    by_cases (sSupAbsIm f 0) = 0 ∨ (sSupAbsIm f 1) = 0
    -- Zero case
    · rw [invInterpStrip_eq_of_zero z f h]
      simp only [zero_le_one, true_or, le_max_iff, zero_le_mul_right,
      map_zero, lt_max_iff, zero_lt_one]
    -- Positive case
    · push_neg at h
      replace h : (0 < sSupAbsIm f 0) ∧ (0 < sSupAbsIm f 1)
      cases' h with h1 h2
      · rw [ne_comm] at h1; rw [ne_comm] at h2
        exact ⟨ (lt_of_le_of_ne (sSupAbsIm_nonneg f 0) (h1)),
        (lt_of_le_of_ne (sSupAbsIm_nonneg f 1) (h2)) ⟩
      simp only [invInterpStrip_eq_of_pos z f h.1 h.2, map_mul]
      apply mul_le_mul _ _ (map_nonneg _ _) (le_trans zero_le_one (le_max_left _ _))
      -- Bounding individual terms
      · by_cases hM0_one : 1 ≤ sSupAbsIm f 0
        -- `1 ≤ (sSupAbsIm f 0)`
        · apply le_trans _ (le_max_left _ _)
          simp only [abs_cpow_eq_rpow_re_of_pos h.1, sub_re, one_re,
          Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
        -- `0 < (sSupAbsIm f 0) < 1`
        · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
          simp only [abs_cpow_eq_rpow_re_of_pos h.1, sub_re, one_re]
          apply Real.rpow_le_rpow_of_exponent_ge (h.1) (le_of_lt hM0_one) _
          simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
      · by_cases hM1_one : 1 ≤ sSupAbsIm f 1
        -- `1 ≤ sSupAbsIm f 1`
        · apply le_trans _ (le_max_left _ _)
          simp only [abs_cpow_eq_rpow_re_of_pos h.2, sub_re, one_re, neg_re,
          Real.rpow_le_one_of_one_le_of_nonpos hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
        -- `0 < sSupAbsIm f 1 < 1`
        · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
          simp only [abs_cpow_eq_rpow_re_of_pos h.2, sub_re, one_re, neg_re,
          Real.rpow_le_rpow_of_exponent_ge (h.2) (le_of_lt hM1_one)
            (neg_le_neg_iff.mpr hset.2)]

lemma F'_eventually_le_one (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1))) :
    ∀ᶠ (z : ℂ) in (cocompactStrip 0 1), (abs ∘ (F' n f)) z ≤ 1 := by
  simp only [F', comp_apply, map_mul, Algebra.id.smul_eq_mul, ofReal_nat_cast, map_mul]
  cases' (F_BddAbove f hB) with C hF'
  rw [mem_upperBounds] at hF'
  apply Eventually.mp (expterm_eventually_le_one C n hn) (Eventually.filter_mono inf_le_right _)
  rw [comap_principal]
  apply eventually_of_mem (mem_principal_self _) _
  intros z hset hexp
  specialize hF' (abs (F f z))
  -- Showing `abs (F f z) ∈ abs ∘ F f '' closedStrip 0 1`
  specialize hF' _
  · simp only [image_congr, mem_image, comp_apply]; use z; refine ⟨hset , refl _⟩
  -- Combining `hexp` with `hF'` by `trans`
  · exact le_trans (mul_le_mul hF' (le_refl _) (map_nonneg _ _)
      (le_trans (map_nonneg _ _) hF')) hexp

-- Proof that the edges are bounded by one
lemma F_edge_le_one (f : ℂ → ℂ) (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1)))
    (hz : z ∈ re ⁻¹' {0, 1}) : abs (F f z) ≤ 1 := by
  simp only [F, Algebra.id.smul_eq_mul, map_mul]
  cases' lt_or_eq_of_le (sSupAbsIm_nonneg f 0) with hpos hzero
  · cases' lt_or_eq_of_le (sSupAbsIm_nonneg f 1) with h1pos h1zero
    -- Positive case
    · simp only [invInterpStrip_eq_of_pos z f hpos h1pos, map_mul, abs_cpow_eq_rpow_re_of_pos,
        hpos, h1pos, sub_re, one_re, neg_re]
      cases' hz with hz0 hz1
      -- `z.re = 0`
      · simp only [hz0, mul_one, zero_sub, Real.rpow_zero, neg_zero,
        Real.rpow_neg_one, mul_inv_le_iff hpos]
        rw [← hz0]
        apply abs_le_sSupAbsIm f z _ hB
        simp only [closedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
      -- `z.re = 1`
      · rw [mem_singleton_iff] at hz1
        simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
        mul_inv_le_iff h1pos, mul_one]
        rw [← hz1]
        apply abs_le_sSupAbsIm f z _ hB
        simp only [closedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

    -- Handling cases where `sSupAbsIm f 0 = 0` or `sSupAbsIm f 1 = 0.`
    · rw [invInterpStrip_eq_of_zero z f]
      simp only [zero_le_one, mul_zero, map_zero]
      right; simp only [h1zero, eq_self_iff_true]
  · rw [invInterpStrip_eq_of_zero z f]
    simp only [zero_le_one, mul_zero, map_zero]
    left; rw [eq_comm]; exact hzero

-- Edges of `F'` are constructed to be ≤ 1
lemma edges_le_one (f : ℂ → ℂ) (n : ℕ) (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1)))
    (hz : z ∈ re ⁻¹' {0, 1}) : (abs ∘ F' n f) z ≤ 1 := by
  -- Small useful lemma
  have hdivnat : 0 ≤ ((n : ℂ)⁻¹).re := by
    simp only [← ofReal_nat_cast n, ← ofReal_inv n, ofReal_re, inv_nonneg, Nat.cast_nonneg]
  -- Expterm ≤ 1
  have hexp : abs (exp ((z ^ 2 - 1) * (↑n)⁻¹)) ≤ 1 := by
    rw [abs_exp, ← re_add_im z]
    simp only [tsub_zero, sub_re, one_re, add_im, add_zero, mul_one, mul_re,
      zero_div, zero_mul, ofReal_re, add_re, one_im, nat_cast_im, ofReal_im, I_im,
      zero_add, inv_im, sq, sub_im, I_re, Real.exp_le_one_iff, mul_im, mul_zero, neg_zero]
    cases' hz with hz0 hz1
    · simp only [hz0, ofReal_zero, cpow_two, nat_cast_re, sq, zero_add, mul_re, ofReal_re,
        I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, mul_im, add_zero, zero_sub]
      apply mul_nonpos_of_nonpos_of_nonneg _ hdivnat
      simp only [sub_nonpos, ofReal_zero, zero_add, cpow_two]
      apply le_trans _ zero_le_one
      rw [Right.neg_nonpos_iff, ← sq]
      apply sq_nonneg
    · rw [hz1.out]
      simp only [ofReal_one, cpow_two, nat_cast_re, sq, mul_re, add_re, one_re, ofReal_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, one_im, mul_im, zero_add,
        sub_sub_cancel_left, neg_mul, Left.neg_nonpos_iff, gt_iff_lt, mul_self_pos, ne_eq]
      simp only [hz1.out, Right.neg_nonpos_iff, one_pow, neg_mul, sub_sub_cancel_left,← sq]
      rw [mul_nonneg_iff]
      left
      exact ⟨sq_nonneg _, hdivnat ⟩

  -- Combining Expterm ≤ 1 with F ≤ 1 on edges
  simp only [Complex.HadamardThreeLines.F', cpow_two, ofReal_inv, ofReal_nat_cast, smul_eq_mul,
    comp_apply, map_mul, ge_iff_le]
  apply Left.mul_le_one_of_le_of_le (F_edge_le_one z f hB hz) _ (map_nonneg _ _)
  simp only [← cpow_two, hexp]

-- Show the Theorem on the members of the sequence `(F')` that tends to `F`.
lemma abs_le_interp_on_closed_strip_sequence (f : ℂ → ℂ) (z : ℂ)
    (hd : DiffContOnCl ℂ f (strip 0 1)) (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1)))
    (hz : z ∈ closedStrip 0 1) (n : ℕ) (hn : 1 ≤ n) : (abs ∘ F' n f) z ≤ 1 := by
  rcases (Eventually.exists_mem (F'_eventually_le_one f n hn hB)) with ⟨w, ⟨h_w, h_h⟩⟩
  rw [cocompact_strip.mem_sets] at h_w
  cases' h_w with B h_w
  -- Using positive bound to prevent pathologies
  let T := max B 1
  have h_w_pos (z : ℂ) (hset : z.re ∈ Icc 0 (1 : ℝ)) (him : T ≤ |z.im|) : z ∈ w :=
    h_w z hset (le_trans (le_max_left B 1) him)
  by_cases (|z.im| ≤ T)
  -- First case `|z.im| ≤ T`
  · have bdd_strip_is_bounded : Bornology.IsBounded (bddStrip 0 1 (T)) :=
      ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _))
    --Function is DiffContOnCl on subset + multiplied by 'simple' function
    have hd_subset : DiffContOnCl ℂ (F' n f) (bddStrip 0 1 (T)) := by
      apply DiffContOnCl.mono _ _
      · use strip 0 1
      · exact diffContOnCl_F' _ _ hd
      · exact inter_subset_left _ _
    apply norm_le_of_forall_mem_frontier_norm_le bdd_strip_is_bounded hd_subset _ _
    -- Frontier bounded by one
    · intros z hfz
      rw [bddStrip, ← Set.reProdIm, frontier_reProdIm] at hfz
      cases' hfz with hfz1 hfz2
      · cases' hfz1 with hfz_re hfz_im
        rw [frontier_Ioo] at hfz_im
        rw [closure_Ioo (zero_ne_one' ℝ)] at hfz_re
        apply h_h; apply h_w_pos z hfz_re
        -- `|T| = |z.im|`
        apply le_of_eq
        rwa [eq_comm, abs_eq (le_trans (zero_le_one' ℝ) (le_max_right B 1)),
         ← mem_singleton_iff, or_comm, ← mem_insert_iff, ← mem_preimage]
        -- `-T < T`
        exact neg_lt_self_iff.mpr (lt_of_lt_of_le (zero_lt_one' ℝ) (le_max_right B 1))
      · replace hfz_re := mem_of_mem_inter_left hfz2
        rw [frontier_Ioo (zero_lt_one' ℝ)] at hfz_re
        exact edges_le_one z f n hB hfz_re
    -- Local goal: `z ∈ closure (bddStrip 0 1 T)` with `h : |z.im| ≤ T` and `hz : z ∈ strip 0 1`.
    · rw [bddStrip, ← Set.reProdIm, closure_reProdIm, closure_Ioo (zero_ne_one' ℝ), closure_Ioo,
      Set.reProdIm, mem_inter_iff]
      refine ⟨hz, ?_⟩
      rwa [mem_preimage, mem_Icc, ← abs_le]
      apply ne_of_lt
      exact neg_lt_self_iff.mpr (lt_of_lt_of_le (zero_lt_one' ℝ) (le_max_right B 1))
  -- Now : `T < |z.im|`.
  · simp only [not_le] at h; apply h_h; exact h_w_pos z hz (le_of_lt h)

-- Proof that `F'` Tendsto `F`
lemma tendsto_F'_atTop_F (f : ℂ → ℂ) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ F' n f z ) atTop (nhds (F f z)) :=
  have mul_const : Tendsto (fun n : ℕ ↦ (z^2-1) * (n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero]
      using tendsto_const_nhds.mul (tendsto_algebraMap_inverse_atTop_nhds_0_nat ℂ)
  have comp_exp : Tendsto (fun n : ℕ ↦ exp ( (z^2-1) * (n : ℝ)⁻¹)) atTop (nhds 1) := by
    simpa only [exp_zero]
      using  (Continuous.tendsto continuous_exp 0).comp mul_const
  by simpa only [mul_one]
    using tendsto_const_nhds.mul comp_exp

-- Proof that `abs F'` Tendsto `abs F`
lemma tendsto_F'_atTop_F_abs (f : ℂ → ℂ) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ (abs ∘ (F' n f)) z) atTop (nhds ((abs ∘ (F f)) z)) :=
  (Continuous.tendsto continuous_abs (F f z)).comp (tendsto_F'_atTop_F f z)

-- We are now ready to combine of `Hadamard_sequence` with `tendsto_F'_atTop_F_abs`:

/--
**Hadamard three-line theorem** on `[0,1]`: If `f` is a bounded function, continuous on `[0,1]`
and differentiable on `(0,1)`, then for `M(x) := sup ((abs ∘ f) '' (re ⁻¹' {x}))` we have that
`∀ z ∈ [0,1]` the inequality `|f(z)| ≤ |M(0)^(1-z)| * |M(1)^z|` holds.
-/
theorem abs_mul_invInterpStrip_le_one_on_closedStrip (f : ℂ → ℂ) (hd : DiffContOnCl ℂ f (strip 0 1))
    (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1))) (z : ℂ) (hz : z ∈ closedStrip 0 1) :
    (abs (f z • invInterpStrip f z)) ≤ 1 := by
  apply le_of_tendsto (tendsto_F'_atTop_F_abs f z) _
  rw [eventually_iff_exists_mem]
  use {n : ℕ | 1 ≤ n}
  exact ⟨mem_atTop _ , abs_le_interp_on_closed_strip_sequence f z hd hB hz⟩

-----


lemma _root_.abs_sub_abs_le_abs_add (a b : R) [Ring R]
    [OrderedCommRing S] (abv : AbsoluteValue R S) [NoZeroDivisors S] :
    abv a - abv b ≤ abv (a+b) := by
  rw [tsub_le_iff_right, add_comm, add_comm a]
  simpa only [neg_add_cancel_left, AbsoluteValue.map_neg]
    using AbsoluteValue.add_le abv (-b) (b + a)

variable (f : ℂ → ℂ) (z : ℂ)

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

/-- Main theorem when `0 < sSupAbsIm f 0` and  `0 < sSupAbsIm f 1`. -/
lemma abs_le_interp_on_closedStrip_pos (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1)))
    (hd : DiffContOnCl ℂ f (strip 0 1))  (hz : z ∈ closedStrip 0 1) (h0 : 0 < sSupAbsIm f 0)
    (h1 : 0 < sSupAbsIm f 1) : abs (f z) ≤ abs (interpStrip f z) := by
  rw [interpStrip_eq_of_pos f z h0 h1]
  have h : (abs (f z • invInterpStrip f z)) ≤ 1 := by
    exact abs_mul_invInterpStrip_le_one_on_closedStrip f hd hB z hz
  rw [invInterpStrip_eq_of_pos z f h0 h1] at h
  simp at h;
  simp only [map_mul, ge_iff_le]
  rw [← mul_inv_le_iff, ← one_mul (abs (↑(sSupAbsIm f 1) ^ z)), ← mul_inv_le_iff',
  ← Real.rpow_neg_one, ← Real.rpow_neg_one,← Complex.abs_cpow_real, ← Complex.abs_cpow_real]
  · simp only [ofReal_neg, ofReal_one, Complex.cpow_neg_one, Complex.cpow_neg_one,
      ← Complex.cpow_neg, ← Complex.cpow_neg, neg_sub, mul_assoc, h]
  · simp only [Complex.abs_cpow_eq_rpow_re_of_pos h1,  Real.rpow_pos_of_pos h1 z.re]
  · simp only [Complex.abs_cpow_eq_rpow_re_of_pos h0, Real.rpow_pos_of_pos h0 (1-z).re]

section transl

/-
  This section introduces the translation function `tansl (ε : ℂ) := fun z ↦ f z + ε`,
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

variable (ε : ℂ)
def transl := fun z ↦ f z + ε

lemma transl_def : (transl f ε) = fun z ↦ f z + ε := by
  rfl

lemma transl_DiffCont (hd : DiffContOnCl ℂ f (strip 0 1)) : DiffContOnCl ℂ (transl f ε) (strip 0 1) := by
  rw [transl_def]
  exact DiffContOnCl.add_const hd ε

variable (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1)))

lemma transl_BddAbove :
    BddAbove ((abs ∘ (transl f ε)) '' (closedStrip 0 1)) := by
  rw [transl_def, bddAbove_def] at *
  obtain ⟨B, hB⟩ := hB
  use B + abs ε
  simp only [comp_apply, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  exact fun y hy ↦ (le_trans (AbsoluteValue.add_le abs _ _)
    ((add_le_add_iff_right _).mpr (hB y hy)))

lemma sSupAbsIm_of_transl_le_transl_of_sSupAbsIm (w : ℝ) (hset: w ∈ Icc 0 1) :
    sSupAbsIm (transl f ε) w ≤ sSupAbsIm f w + abs ε := by
  apply csSup_le _ _
  · simp only [nonempty_image_iff, Nonempty.preimage (singleton_nonempty _) re_surjective];
  intros b hset;
  obtain ⟨x, hxset, hb⟩ := hset
  rw [← hb]
  apply le_trans (AbsoluteValue.add_le abs (f x) ε)
  simp only [add_le_add_iff_right]
  apply le_csSup
    (BddAbove.mono (image_subset _ (preimage_mono (singleton_subset_iff.mpr hset))) hB) _
  simpa using mem_image_of_mem (abs ∘ f) hxset

lemma sSupAbsIm_le_transl_of_sSupAbsIm_of_transl (w : ℝ) (hset: w ∈ Icc 0 1) :
    sSupAbsIm f w  ≤ sSupAbsIm (transl f ε) w + abs ε := by
  simpa only [add_neg_cancel_right, AbsoluteValue.map_neg, transl]
    using sSupAbsIm_of_transl_le_transl_of_sSupAbsIm (fun x ↦ f x + ε) (-ε) 
      (transl_BddAbove f ε hB) w hset

lemma transl_sub_sSupAbsIm_le_transl_of_sSupAbsIm (w : ℝ) (hset: w ∈ Icc 0 1) :
    abs ε - sSupAbsIm f w  ≤ sSupAbsIm (transl f ε) w := by
  have : abs (f w + ε) ∈ (fun a ↦ abs (f a + ε)) '' (re ⁻¹' {w}) := by
    use w; simp only [mem_preimage, ofReal_re, mem_singleton_iff, and_self]
  apply le_trans _ (le_csSup (BddAbove.mono (image_subset _ (preimage_mono
    (singleton_subset_iff.mpr hset))) (transl_BddAbove f  ε hB)) this)
  rw [add_comm]
  apply le_trans _ (abs_sub_abs_le_abs_add ε (f w) abs)
  rw [sub_le_sub_iff_left]
  apply le_csSup
    (BddAbove.mono (image_subset _ (preimage_mono (singleton_subset_iff.mpr hset))) hB) _
  use w; simp only [mem_preimage, ofReal_re, mem_singleton_iff, and_self]
  simp only [comp_apply, and_self]

lemma Continuous_sSupAbsIm_transl_zero (w : ℝ) (hset: w ∈ Icc 0 1) :
    Tendsto (fun ε => sSupAbsIm (transl f ε) w) (nhds 0) (nhds (sSupAbsIm f w)) := by
  simp_rw [sSupAbsIm, transl, comp_apply, Metric.tendsto_nhds_nhds, dist_eq,
    Real.dist_eq]
  simp only [gt_iff_lt, sub_zero]
  intros ε hε
  use ε
  refine ⟨hε, ?_⟩
  intro x hx
  by_cases (sSup ((fun a => abs (f a + x)) '' (re ⁻¹' {w}))
              - sSup ((fun a => abs (f a)) '' (re ⁻¹' {w}))) > 0
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
  have hc_pos (r : ℝ) (ε : ℂ) (hε_r: abs ε < sSupAbsIm f r) (hset : r ∈ Icc 0 1) :
      0 < sSupAbsIm (transl f ε) r := by
    exact lt_of_lt_of_le (sub_pos.mpr hε_r) (tsub_le_iff_right.mpr 
      (sSupAbsIm_le_transl_of_sSupAbsIm_of_transl f ε hB r (hset)))
  have hc_zero (r : ℝ) (ε : ℂ) (hε_r: 0 = sSupAbsIm f r) (hset : r ∈ Icc 0 1) (hε_ne_zero: ¬ε = 0) :
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
    exact fun ε hε_ne_zero hε_1 ↦ ⟨hc_zero 0 ε h0zero (Set.left_mem_Icc.mpr zero_le_one) hε_ne_zero,
      hc_pos 1 ε hε_1 (Set.right_mem_Icc.mpr zero_le_one)⟩
  use 1
  simp
  exact fun ε hε_ne_zero _ ↦ ⟨hc_zero 0 ε h0zero (Set.left_mem_Icc.mpr zero_le_one) hε_ne_zero,
      hc_zero 1 ε h1zero (Set.right_mem_Icc.mpr zero_le_one) hε_ne_zero⟩

lemma interpStrip_nhds_zero_pos :
    ∃ T > 0, ∀ ε ∈ {0}ᶜ ∩ Metric.ball 0 (T), abs ((sSupAbsIm (transl f ε) 0)^(1-z) *
      (sSupAbsIm (transl f ε) 1)^(z)) = abs (interpStrip (transl f ε) z ) := by
  obtain ⟨T, hTpos, hT⟩ := sSupAbsIm_transl_nhds_zero_pos f hB
  use T
  refine ⟨hTpos, ?_⟩
  intro ε hε
  simp only [(eq_comm.mp (interpStrip_eq_of_pos _ _ (hT ε hε).1 (hT ε hε).2))]

lemma eventuallyle (hd : DiffContOnCl ℂ f (strip 0 1)) (hz : z ∈ strip 0 1) :
    (fun ε ↦ abs ((transl f ε) z)) ≤ᶠ[nhdsWithin 0 {0}ᶜ] (fun ε ↦ abs (interpStrip (transl f ε) z)) := by
  obtain ⟨T, hTpos, hT⟩ := sSupAbsIm_transl_nhds_zero_pos f hB
  rw [EventuallyLE, eventually_nhdsWithin_iff, eventually_nhds_iff]
  use Metric.ball 0 T
  refine ⟨ ?_, ⟨Metric.isOpen_ball, Metric.mem_ball_self hTpos⟩⟩
  · intro x hx hnezero
    exact abs_le_interp_on_closedStrip_pos _ _ (transl_BddAbove f x hB) (transl_DiffCont f x hd) 
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))
       (hT x ⟨hnezero, hx⟩).1 (hT x ⟨hnezero, hx⟩).2

lemma tendsto_interpStrip_pos (hz: z ∈ strip 0 1) : ContinuousAt (fun ε => 
    abs (↑(sSupAbsIm (transl f ε) 0) ^ (1 - z) * ↑(sSupAbsIm (transl f ε) 1) ^ z)) 0 := by
  simp only [map_mul]
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
    Tendsto (fun ε => abs (interpStrip (transl f ε) z)) (nhdsWithin 0 {0}ᶜ)
    (nhds (abs (interpStrip f z))) := by
  obtain ⟨T, hTpos, hT⟩ := interpStrip_nhds_zero_pos f z hB
  rw [nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ hTpos)]
  have : (interpStrip f z) = (↑(sSupAbsIm (transl f 0) 0) ^ (1 - z) * ↑(sSupAbsIm (transl f 0) 1) ^ z) := by
    rw [strip, mem_preimage, mem_Ioo] at hz
    simp [- ne_eq, interpStrip_eq_of_zero f _ h]
    rw [transl_def]; simp
    cases' h with h1 h2
    left
    refine ⟨h1, ?_ ⟩
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

variable (hB : BddAbove ((abs ∘ f) '' (closedStrip 0 1))) (hd : DiffContOnCl ℂ f (strip 0 1))

lemma abs_le_interp_on_strip_zero (hz : z ∈ strip 0 1)
    (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) : abs (f z) ≤ abs (interpStrip f z) := by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · apply Filter.tendsto_inf_left
    apply Continuous.tendsto'
      (Continuous.comp continuous_abs (Continuous.add continuous_const continuous_id))
    simp only [id_eq, comp_apply, add_zero]
  · apply Tendsto_interpStrip f z hB hz h 

lemma abs_eq_zero_on_strip (hz : z ∈ strip 0 1)
    (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) : f z = 0 := by
  rw [← map_eq_zero abs]
  apply le_antisymm _ (map_nonneg _ _)
  simpa [interpStrip_eq_of_zero f z h, map_zero] using
    abs_le_interp_on_strip_zero f z hB hd hz h

lemma abs_eq_zero_on_closedStrip (hz : z ∈ closedStrip 0 1)
    (h : sSupAbsIm f 0 = 0 ∨ sSupAbsIm f 1 = 0) : abs (f z) = 0 := by
  have : f '' strip 0 1 = {0} := by
    ext; constructor
    · intro ⟨a, ⟨ha1, ha2⟩⟩
      rw [← ha2]
      exact abs_eq_zero_on_strip f a hB hd ha1 h
    · intro hx; rw [hx]; use (1/2 : ℚ);
      have : ((1/2: ℚ): ℂ) ∈ strip 0 1 := by rw [strip, mem_preimage, rat_cast_re]; norm_num;
      exact ⟨this, abs_eq_zero_on_strip f ((1/2: ℚ): ℂ) hB hd this h⟩
  have : closure (f '' strip 0 1) = {0} := by simp only [this, closure_singleton]
  simp only [map_eq_zero]
  apply eq_of_mem_singleton
  rw [closedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz
  rw [←this]
  apply ContinuousWithinAt.mem_closure_image
    (ContinuousWithinAt.mono (ContinuousOn.continuousWithinAt hd.2 hz) subset_closure) hz

theorem abs_le_interp_on_closedStrip (hz : z ∈ closedStrip 0 1) : 
  abs (f z) ≤ abs (interpStrip f z) := by
  by_cases (sSupAbsIm f 0) = 0 ∨ (sSupAbsIm f 1) = 0
  · rw [interpStrip_eq_of_zero f z h]
    simp only [map_zero];
    exact le_of_eq (abs_eq_zero_on_closedStrip f z hB hd hz h)
  · push_neg at h
    replace h : (0 < sSupAbsIm f 0) ∧ (0 < sSupAbsIm f 1)
    cases' h with h1 h2
    · rw [ne_comm] at h1; rw [ne_comm] at h2
      exact ⟨ (lt_of_le_of_ne (sSupAbsIm_nonneg f 0) (h1)),
      (lt_of_le_of_ne (sSupAbsIm_nonneg f 1) (h2)) ⟩
    exact abs_le_interp_on_closedStrip_pos _ _ hB hd hz h.1 h.2

end HadamardThreeLines
end Complex
