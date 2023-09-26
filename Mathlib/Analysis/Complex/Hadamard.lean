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
This result generalises well by a change of variables.

## Main result

- `abs_le_interp_on_closed_strip` : 
  Let f be a bounded function on the strip {x+iy: 0 ≤ x ≤ 1} (hB), differientable in the interior 
  and continuous on the closure (hd). Then the function `sup {|f(z)| : z.re = x}` is convex
  on [0,1].

## Notation

- `Complex.HadamardThreeLines.strip` : The vertical strip defined by : re ⁻¹' Ioo a b

- `Complex.HadamardThreeLines.closed_strip` : The vertical strip defined by : re ⁻¹' Icc a b

- `Complex.HadamardThreeLines.bdd_strip` : 
    The rectangle defined by : re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T

- `Complex.HadamardThreeLines.closed_bdd_strip` : 
    The rectangle defined by : re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T

- `Complex.HadamardThreeLines.sSup_abs_im` : 
    The supremum function on vertical lines defined by : sSup {|f(z)| : z.re = x}

- `Complex.HadamardThreeLines.inv_interp_strip` : 
    Inverse of the interpolation between the sSup_abs_im on the edges of the strip.

- `Complex.HadamardThreeLines.F` : 
    Function defined by f times inv_interp_strip. Convenient form for proofs.

- `Complex.HadamardThreeLines.F'` : 
    'Easy' function converging to F.

- `Complex.HadamardThreeLines.cocompact_strip` :
    The filter along the vertical strip re ⁻¹' Ioo a b and |z.im| atTop.

## References

This proof follows loosely the proof found on the wiki page :
[wiki](https://en.wikipedia.org/wiki/Hadamard_three-lines_theorem)

-/


open Set Metric Filter Function Complex
open Interval 

attribute [-simp] div_eq_zero_iff

namespace Complex
namespace HadamardThreeLines
variable (a b : ℝ) (z : ℂ) 

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b`. -/
def strip (a: ℝ) (b: ℝ) := re ⁻¹' Ioo a b

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b`. -/
def closed_strip (a: ℝ) (b: ℝ) := re ⁻¹' Icc a b

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b` and 
`z.im ∈ Ioo (-T) T`. -/
def bdd_strip (a: ℝ) (b: ℝ) (T: ℝ) :=  re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T

/-- The strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b` and 
`z.im ∈ Icc (-T) T`. -/
def closed_bdd_strip (a: ℝ) (b: ℝ) (T: ℝ) :=  re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T

/-- The filter along the vertical strip `re ⁻¹' Ioo a b` and `|z.im| atTop` -/
def cocompact_strip (a b : ℝ) : Filter ℂ := 
  comap im (cocompact ℝ) ⊓ (comap re (principal  (Icc a b)))

/-- The supremum of the absolute value of `f` on imaginary lines. (Fixed real part) -/
noncomputable def sSup_abs_im (f : ℂ → ℂ) (x : ℝ) :=  sSup ((abs ∘ f) '' (re ⁻¹' {x})) 


/-- The inverse of the interpolation of sSup_abs_im on the two boundaries. -/
noncomputable def inv_interp_strip (f : ℂ → ℂ) (z : ℂ): ℂ := 
  if (sSup_abs_im f (0:ℝ)) = (0:ℝ) ∨ (sSup_abs_im f (1:ℝ)) = (0:ℝ)
    then 0
    else (sSup_abs_im f 0)^(z-1) * (sSup_abs_im f 1)^(-z)

/-- A function useful for the proofs steps. We will aim to show that it is bounded by 1. -/
private noncomputable def F (f : ℂ → ℂ) := fun z ↦ f z • inv_interp_strip f z

/-- Similar to F only 'easier'. Useful for proof steps. -/
private noncomputable def F' (n: ℕ) (f: ℂ → ℂ) := fun z ↦ F f z • exp ((z^2-1) * (n : ℝ)⁻¹) 


-- Small lemma : Sup of abs is nonneg
lemma sSup_abs_im_nonneg (f : ℂ → ℂ) (x : ℝ) : 0 ≤ sSup_abs_im f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, map_nonneg]


-- Definition rewrites for inv_interp_strip
lemma inv_interp_strip_of_pos_def (f: ℂ → ℂ ) (h0: 0 < sSup_abs_im f 0) (h1: 0 < sSup_abs_im f 1) :
    inv_interp_strip f z = (sSup_abs_im f 0)^(z-1) * (sSup_abs_im f 1)^(-z) := by
  simp only [ne_of_gt h0, ne_of_gt h1, inv_interp_strip, if_false, or_false]


lemma inv_interp_strip_of_zero_def (f: ℂ → ℂ ) (h: (sSup_abs_im f 0) = 0 ∨ (sSup_abs_im f 1) = 0) : 
    inv_interp_strip f z = 0 :=
  if_pos h

-- Differentiable continuous function inv_interp_strip
lemma inv_interp_strip_diff_cont (f: ℂ → ℂ) : DiffContOnCl ℂ (inv_interp_strip f) (strip 0 1) := by
  by_cases (sSup_abs_im f 0) = 0 ∨ (sSup_abs_im f 1) = 0 
  -- Case everywhere 0
  -- Starting with Lemma to handle rewriting of inv_interp_strip as a function.
  have hzero : inv_interp_strip f = 0 := by 
    rw [funext_iff]
    intro z
    simp only [inv_interp_strip_of_zero_def z f h, Pi.zero_apply, eq_self_iff_true]
  rw [hzero, Pi.zero_def]
  exact diffContOnCl_const

  -- Case nowhere 0
  push_neg at h
  cases' h with h0 h1
  rw [ne_comm] at h0 h1
  apply Differentiable.diffContOnCl
  intro z
  -- Same strategy.
  have hpos: inv_interp_strip f = fun (z:ℂ) ↦ (sSup_abs_im f 0)^(z-1) * (sSup_abs_im f 1)^(-z) := by
    funext z
    rw [inv_interp_strip_of_pos_def z f (lt_of_le_of_ne (sSup_abs_im_nonneg f 0) h0)
    (lt_of_le_of_ne (sSup_abs_im_nonneg f 1) h1)]
  rw [hpos]
  apply DifferentiableAt.mul _ _
  · apply DifferentiableAt.const_cpow (DifferentiableAt.sub_const (differentiableAt_id') 1) _ 
    left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]
  · apply DifferentiableAt.const_cpow _ _
    rw [differentiableAt_neg_iff]
    apply differentiableAt_id'
    left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]



lemma F'_diff_cont (f: ℂ → ℂ) (n : ℕ) (hd : DiffContOnCl ℂ f (strip 0 1)) : 
    DiffContOnCl ℂ (F' n f) (strip 0 1) := by
  apply DiffContOnCl.smul (DiffContOnCl.smul hd (inv_interp_strip_diff_cont f) ) _ 
  apply Differentiable.diffContOnCl
  apply Differentiable.cexp
  apply Differentiable.mul
  · rw [differentiable_sub_const_iff]
    simp only [differentiable_sub_const_iff, cpow_two, differentiable_id', Differentiable.pow]
  · exact differentiable_const _
      


-- The function f is bounded by sSup_abs_im 
lemma f_le_Sup (f : ℂ → ℂ) (z : ℂ) (hD: z ∈ (closed_strip 0 1)) 
    (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1))) : abs (f z) ≤ sSup_abs_im f (z.re) := by
  apply le_csSup _ _
  · apply BddAbove.mono (image_subset (abs ∘ f) _) hB
    apply preimage_mono
    simp only [singleton_subset_iff]
    exact hD
  · apply mem_image_of_mem (abs ∘ f)
    simp only [mem_preimage, mem_singleton]

lemma cocompact_strip.basis : HasBasis (cocompact_strip 0 1) (fun _ : ℝ × ℝ ↦ True ) 
    (fun T ↦ (im ⁻¹' (Iic (T.1) ∪ Ici (T.2)) ∩ re ⁻¹' Icc 0 1)) := by
  simp only [cocompact_strip, comap_principal, Real.cocompact_eq]
  rw [← true_and True]
  exact HasBasis.inf_principal (HasBasis.comap _ (HasBasis.sup atBot_basis atTop_basis)) _

lemma cocompact_strip.mem_sets {s : Set ℂ} : s ∈ cocompact_strip 0 1 ↔ ∃ T, ∀ (z : ℂ),
    z.re ∈ Icc 0 (1:ℝ) → T ≤ |z.im| → z ∈ s := by
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

lemma cocompact_strip.tendsto_sq_im_atTop : Tendsto (fun z : ℂ ↦ z.im^2) 
    (cocompact_strip 0 1) atTop := by
  apply tendsto_inf_left _
  change Tendsto ((fun x ↦ x^2) ∘ im) (comap im (cocompact ℝ)) atTop
  rw [tendsto_comap'_iff]
  · convert_to Tendsto (fun x ↦ ‖x‖ * ‖x‖) (cocompact ℝ) atTop
    · ext x; simp only [Real.rpow_two, pow_two, Real.norm_eq_abs, abs_mul_abs_self]
    · exact tendsto_norm_cocompact_atTop.atTop_mul_atTop tendsto_norm_cocompact_atTop
  ·  simp only [univ_mem, range_im] 

lemma cocompact_strip.eventually_sq_re_le_one : ∀ᶠ (z : ℂ) in 
    (cocompact_strip 0 1), z.re^2 ≤ 1 := by
  rw [cocompact_strip, comap_principal, eventually_inf_principal]
  apply eventually_of_forall
  rintro z hz
  simp only [Real.rpow_two]
  rw [sq_le_one_iff hz.1]
  exact hz.2

-- Smoothly decreasing function when the real part is bounded eventually ≤ 1
lemma expterm_eventually_le_one (C : ℝ) (n : ℕ) (hn: 1 ≤ n) : ∀ᶠ (z : ℂ)
    in (comap Complex.im (cocompact ℝ) ⊓ (comap Complex.re (principal  (Icc 0 1)))),
    C * abs (exp ((z^(2:ℕ)-1) * (n : ℝ)⁻¹) ) ≤ 1 := by
  apply eventually_le_of_tendsto_lt  (zero_lt_one' ℝ) _
  simp only [abs_exp]
  rw [ show (fun z : ℂ ↦ C * Real.exp (((z^(2:ℕ)-1) * (n : ℝ)⁻¹).re)) 
    = (fun z : ℂ ↦ C * Real.exp ((z.re^(2:ℕ) - z.im^(2:ℕ) - 1) * (n : ℝ)⁻¹)) by
      ext1 z
      nth_rewrite 1 [← re_add_im z]
      simp only [mul_re, sub_re, ofReal_im, mul_zero, tsub_zero, ofReal_re]
      rw [cpow_nat_cast, sq, mul_re]
      simp only [re_add_im, one_re, Nat.cast_ofNat, Real.rpow_two, mul_eq_mul_left_iff, 
      Real.exp_eq_exp, mul_eq_mul_right_iff, sub_left_inj, inv_eq_zero, Nat.cast_eq_zero, sq] ]
  nth_rewrite 2 [← mul_zero C] 
  apply Tendsto.const_mul C _
  rw [Real.tendsto_exp_comp_nhds_zero]
  apply Tendsto.atBot_mul_const (show 0 < (n:ℝ)⁻¹ by
    simp only [inv_pos, Nat.cast_pos, lt_of_lt_of_le zero_lt_one hn])
  -- x.re ^ 2 - x.im ^ 2 - 1 Tendsto at_bot
  apply tendsto_atBot_add_const_right _ (-1) _
  simp only [sub_eq_add_neg]
  apply tendsto_atBot_add_left_of_ge' _ (1 : ℝ) cocompact_strip.eventually_sq_re_le_one _
  rw [tendsto_neg_atBot_iff]
  exact cocompact_strip.tendsto_sq_im_atTop
 

-- The function F is bounded above because f is.
lemma F_BddAbove (f: ℂ → ℂ) (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1))) :
    BddAbove ((abs ∘ F f) '' (closed_strip 0 1)) := by
  -- Rewriting goal
  simp only [F, image_congr, comp_apply, map_mul]
  rw [bddAbove_def] at * 
  cases' hB with B hB
  -- Using bound
  use B * ((max 1 ((sSup_abs_im f 0)^ (-(1:ℝ)))) * max 1 ((sSup_abs_im f 1)^ (-(1:ℝ))))
  simp only [smul_eq_mul, map_mul, mem_image, forall_exists_index,
   and_imp, forall_apply_eq_imp_iff₂] 
  intros z hset
  specialize hB (abs (f z))
  specialize hB _
  simp only [image_congr, mem_image, comp_apply]; use z;-- refine ⟨hset , refl⟩
  -- Proof that the bound is correct
  apply mul_le_mul hB _ (map_nonneg abs _) (le_trans (map_nonneg abs _) hB)
  by_cases (sSup_abs_im f 0) = 0 ∨ (sSup_abs_im f 1) = 0
  -- Zero case
  · rw [inv_interp_strip_of_zero_def z f h]
    simp only [zero_le_one, true_or, le_max_iff, zero_le_mul_right, 
    map_zero, lt_max_iff, zero_lt_one]
  -- Positive case
  · push_neg at h
    replace h : (0 < sSup_abs_im f 0) ∧ (0 < sSup_abs_im f 1)
    cases' h with h1 h2;
    · rw [ne_comm] at h1; rw [ne_comm] at h2;
      exact ⟨ (lt_of_le_of_ne (sSup_abs_im_nonneg f 0) (h1)), 
      (lt_of_le_of_ne (sSup_abs_im_nonneg f 1) (h2)) ⟩ 
    simp only [inv_interp_strip_of_pos_def z f h.1 h.2, map_mul]
    apply mul_le_mul _ _ (map_nonneg _ _) (le_trans zero_le_one (le_max_left _ _))
    -- Bounding individual terms
    · by_cases hM0_one : 1 ≤ sSup_abs_im f 0
      -- 1 ≤ (sSup_abs_im f 0)
      · apply le_trans _ (le_max_left _ _)
        simp only [abs_cpow_eq_rpow_re_of_pos h.1, sub_re, one_re, 
        Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
      -- 0 < (sSup_abs_im f 0) < 1
      · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
        simp only [abs_cpow_eq_rpow_re_of_pos h.1, sub_re, one_re]
        apply Real.rpow_le_rpow_of_exponent_ge (h.1) (le_of_lt hM0_one) _
        simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1] 
    · by_cases hM1_one : 1 ≤ sSup_abs_im f 1
      -- 1 ≤ sSup_abs_im f 1
      · apply le_trans _ (le_max_left _ _)
        simp only [abs_cpow_eq_rpow_re_of_pos h.2, sub_re, one_re, neg_re,
        Real.rpow_le_one_of_one_le_of_nonpos hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
      -- 0 < sSup_abs_im f 1 < 1
      · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
        simp only [abs_cpow_eq_rpow_re_of_pos h.2, sub_re, one_re, neg_re,
        Real.rpow_le_rpow_of_exponent_ge (h.2) (le_of_lt hM1_one) 
          (neg_le_neg_iff.mpr hset.2)]


lemma F'_eventually_le_one (f: ℂ → ℂ) (n : ℕ) (hn: 1 ≤ n) 
    (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1))) : 
    ∀ᶠ (z : ℂ) in (cocompact_strip 0 1), (abs ∘ (F' n f)) z ≤ 1 := by
  simp only [F', comp_apply, map_mul, Algebra.id.smul_eq_mul, ofReal_nat_cast, map_mul] 
  cases' (F_BddAbove f hB) with C hF'
  rw [mem_upperBounds] at hF'
  apply Eventually.mp (expterm_eventually_le_one C n hn) (Eventually.filter_mono inf_le_right _)
  rw [comap_principal]
  apply eventually_of_mem (mem_principal_self _) _
  intros z hset hexp
  specialize hF' (abs (F f z))
  -- Showing abs (F f z) ∈ abs ∘ F f '' closed_strip 0 1
  specialize hF' _
  · simp only [image_congr, mem_image, comp_apply]; use z; refine ⟨hset , refl _⟩
  -- Combining hexp with hF' by trans
  · exact le_trans (mul_le_mul hF' (le_refl _) (map_nonneg _ _) 
      (le_trans (map_nonneg _ _) hF')) hexp

-- Proof that the edges are bounded by one
lemma F_edge_le_one (f: ℂ → ℂ) (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1)))
    (hz: z ∈ re ⁻¹' {0, 1}) :  abs (F f z) ≤ 1 := by
  simp only [F, Algebra.id.smul_eq_mul, map_mul]
  cases' lt_or_eq_of_le (sSup_abs_im_nonneg f 0) with hpos hzero
  · cases' lt_or_eq_of_le (sSup_abs_im_nonneg f 1) with h1pos h1zero
    -- Positive case
    · simp only [inv_interp_strip_of_pos_def z f hpos h1pos, map_mul, abs_cpow_eq_rpow_re_of_pos,
        hpos, h1pos, sub_re, one_re, neg_re]
      cases' hz with hz0 hz1
      -- z.re = 0 
      · simp only [hz0, mul_one, zero_sub, Real.rpow_zero, neg_zero,
        Real.rpow_neg_one, mul_inv_le_iff hpos]
        rw [← hz0]
        apply f_le_Sup f z _ hB
        simp only [closed_strip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
      -- z.re = 1
      · rw [mem_singleton_iff] at hz1
        simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
        mul_inv_le_iff h1pos, mul_one]
        rw [← hz1]
        apply f_le_Sup f z _ hB
        simp only [closed_strip, mem_preimage, zero_le_one, hz1, right_mem_Icc] 

    -- Handling cases where sSup_abs_im f 0 = 0 or sSup_abs_im f 1 = 0.
    · rw [inv_interp_strip_of_zero_def z f]
      simp only [zero_le_one, mul_zero, map_zero]
      right; simp only [h1zero, eq_self_iff_true]
  · rw [inv_interp_strip_of_zero_def z f]
    simp only [zero_le_one, mul_zero, map_zero]
    left; rw [eq_comm]; exact hzero



-- Edges of F' are constructed to be ≤ 1
lemma edges_le_one (f: ℂ → ℂ) (n : ℕ) (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1)))
    (hz: z ∈ re ⁻¹' {0, 1}) : (abs ∘ F' n f) z ≤ 1 := by
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
    · simp only [hz0]
      simp only [ofReal_zero, cpow_two, nat_cast_re, sq]
      simp only [zero_add, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        mul_im, add_zero, zero_sub]
      apply mul_nonpos_of_nonpos_of_nonneg _ hdivnat
      simp only [sub_nonpos, ofReal_zero, zero_add, cpow_two]
      apply le_trans _ zero_le_one
      rw [Right.neg_nonpos_iff, ← sq]
      apply sq_nonneg
    · rw [hz1.out]
      simp only [ofReal_one, cpow_two, nat_cast_re, sq]
      simp only [mul_re, add_re, one_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, 
        sub_self, add_zero, add_im, one_im, mul_im, zero_add, sub_sub_cancel_left, neg_mul,
        Left.neg_nonpos_iff, gt_iff_lt, mul_self_pos, ne_eq]
      simp only [hz1.out, Right.neg_nonpos_iff, one_pow, neg_mul, sub_sub_cancel_left,← sq]
      rw [mul_nonneg_iff]
      left
      exact ⟨sq_nonneg _, hdivnat ⟩

  -- Combining Expterm ≤ 1 with F ≤ 1 on edges
  simp only [Complex.HadamardThreeLines.F']
  simp only [cpow_two, ofReal_inv, ofReal_nat_cast, smul_eq_mul, comp_apply, map_mul, ge_iff_le]
  apply Left.mul_le_one_of_le_of_le (F_edge_le_one z f hB hz) _ (map_nonneg _ _)
  simp only [← cpow_two, hexp]

-- Show the Theorem on the members of the sequence (F') that tends to F.
lemma abs_le_interp_on_closed_strip_sequence (f : ℂ → ℂ) (z : ℂ)
    (hd : DiffContOnCl ℂ f (strip 0 1)) (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1)))
    (hz: z ∈ closed_strip 0 1) (n: ℕ) (hn: 1 ≤ n) : (abs ∘ F' n f) z ≤ 1 := by
  rcases (Eventually.exists_mem (F'_eventually_le_one f n hn hB)) with ⟨w, ⟨h_w, h_h⟩⟩
  rw [cocompact_strip.mem_sets] at h_w
  cases' h_w with B h_w
  -- Using positive bound to prevent pathologies
  let T := max B 1
  have h_w_pos (z : ℂ) (hset : z.re ∈ Icc 0 (1 : ℝ)) (him : T ≤ |z.im|) : z ∈ w := 
    h_w z hset (le_trans (le_max_left B 1) him)

  by_cases (|z.im| ≤ T) 
  -- First case |z.im| ≤ T  
  · have bdd_strip_is_bounded : Bornology.IsBounded (bdd_strip 0 1 (T)) := 
      ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _))

    --Function is DiffContOnCl on subset + multiplied by 'simple' function
    have hd_subset : DiffContOnCl ℂ (F' n f) (bdd_strip 0 1 (T)) := by
      apply DiffContOnCl.mono _ _
      · use strip 0 1
      · exact F'_diff_cont f n hd
      · exact inter_subset_left _ _

    apply norm_le_of_forall_mem_frontier_norm_le bdd_strip_is_bounded hd_subset _ _

    -- Frontier bounded by one
    · intros z hfz
      rw [bdd_strip, ← Set.reProdIm, frontier_reProdIm] at hfz
      cases' hfz with hfz1 hfz2
      · cases' hfz1 with hfz_re hfz_im
        rw [frontier_Ioo] at hfz_im 
        rw [closure_Ioo (zero_ne_one' ℝ)] at hfz_re
        apply h_h; apply h_w_pos z hfz_re
        -- |T| = |z.im|
        apply le_of_eq
        rwa [eq_comm, abs_eq (le_trans (zero_le_one' ℝ) (le_max_right B 1)),
         ← mem_singleton_iff, or_comm, ← mem_insert_iff, ← mem_preimage]
        -- -T < T
        exact neg_lt_self_iff.mpr (lt_of_lt_of_le (zero_lt_one' ℝ) (le_max_right B 1)) 
      · replace hfz_re := mem_of_mem_inter_left hfz2
        rw [frontier_Ioo (zero_lt_one' ℝ)] at hfz_re
        exact edges_le_one z f n hB hfz_re
    --Local goal: z ∈ closure (bdd_strip 0 1 T) with h: |z.im| ≤ T and hz: z ∈ strip 0 1.
    · rw [bdd_strip, ← Set.reProdIm, closure_reProdIm, closure_Ioo (zero_ne_one' ℝ), closure_Ioo,  
      Set.reProdIm, mem_inter_iff]
      refine ⟨hz, ?_⟩
      rwa [mem_preimage, mem_Icc, ← abs_le]
      apply ne_of_lt
      exact neg_lt_self_iff.mpr (lt_of_lt_of_le (zero_lt_one' ℝ) (le_max_right B 1))

  --Now : T < |z.im|.
  · simp only [not_le] at h; apply h_h; exact h_w_pos z hz (le_of_lt h)

--Proof that F' Tendsto F
lemma F_seq_to_F (f : ℂ → ℂ) (z : ℂ) : Tendsto (fun n : ℕ ↦ F' n f z ) atTop (nhds (F f z)) := 
  have mul_const : Tendsto (fun n : ℕ ↦ (z^2-1) * (n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero]
      using tendsto_const_nhds.mul (tendsto_algebraMap_inverse_atTop_nhds_0_nat ℂ)
  
  have comp_exp : Tendsto (fun n : ℕ ↦ exp ( (z^2-1) * (n : ℝ)⁻¹)) atTop (nhds 1) := by
    simpa only [exp_zero]
      using  (Continuous.tendsto continuous_exp 0).comp mul_const

  by simpa only [mul_one]
    using tendsto_const_nhds.mul comp_exp

-- Proof that |F_seq| Tendsto |F|
lemma F_seq_to_F_abs (f : ℂ → ℂ) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ (abs ∘ (F' n f)) z ) atTop (nhds ((abs ∘ (F f)) z)) :=
  (Continuous.tendsto continuous_abs (F f z)).comp (F_seq_to_F f z)

-- Combination of Hadamard_sequence with F_seq_to_F_abs
theorem abs_le_interp_on_closed_strip (f : ℂ → ℂ) (hd : DiffContOnCl ℂ f (strip 0 1))  
   (hB : BddAbove ((abs ∘ f) '' (closed_strip 0 1))) (z : ℂ) (hz: z ∈ closed_strip 0 1) :
   (abs (f z • inv_interp_strip f z)) ≤ 1 := by
  apply le_of_tendsto (F_seq_to_F_abs f z) _
  rw [eventually_iff_exists_mem]
  use {n : ℕ | 1 ≤ n}
  exact ⟨mem_atTop _ , abs_le_interp_on_closed_strip_sequence f z hd hB hz⟩ 

end HadamardThreeLines
end Complex