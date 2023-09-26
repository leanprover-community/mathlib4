/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
  

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.IsROrC
import Mathlib.Data.Complex.Basic

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

- `complex.hadamard_three_lines.strip` : The vertical strip defined by : re ⁻¹' Ioo a b

- `complex.hadamard_three_lines.closed_strip` : The vertical strip defined by : re ⁻¹' Icc a b

- `complex.hadamard_three_lines.bdd_strip` : 
    The rectangle defined by : re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T

- `complex.hadamard_three_lines.closed_bdd_strip` : 
    The rectangle defined by : re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T

- `complex.hadamard_three_lines.sSup_abs_im` : 
    The supremum function on vertical lines defined by : sup {|f(z)| : z.re = x}

- `complex.hadamard_three_lines.inv_interp_strip` : 
    Inverse of the interpolation between the sSup_abs_im on the edges of the strip.

- `complex.hadamard_three_lines.F` : 
    Function defined by f times inv_interp_strip. Convenient form for proofs.

- `complex.hadamard_three_lines.F'` : 
    'Easy' function converging to F.

- `complex.hadamard_three_lines.cocompact_strip` :
    The filter along the vertical strip re ⁻¹' Ioo a b and |z.im| at_top.

## References

This proof follows loosely the proof found on the wiki page:
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

/-- The filter along the vertical strip `re ⁻¹' Ioo a b` and `|z.im| at_top` -/
def cocompact_strip (a b : ℝ) : 
  Filter ℂ := comap im (cocompact ℝ) ⊓ (comap re (principal  (Icc a b)))

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
private noncomputable def F' (n: ℕ) (f: ℂ → ℂ) := λ z ↦ F f z • exp ((z^2-1) * (n : ℝ)⁻¹) 


-- Small lemma : Sup of abs is nonneg
lemma sSup_abs_im_nonneg (f : ℂ → ℂ) (x : ℝ) : 0 ≤ sSup_abs_im f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, hz1, hz2⟩
  simp only [← hz2, comp, map_nonneg]


-- Definition rewrites for inv_interp_strip
lemma inv_interp_strip_of_pos_def (f: ℂ → ℂ ) (h0: 0 < sSup_abs_im f 0) (h1 : 0 < sSup_abs_im f 1) :
  inv_interp_strip f z = (sSup_abs_im f 0)^(z-1) * (sSup_abs_im f 1)^(-z) :=
by simp only [ne_of_gt h0, ne_of_gt h1, inv_interp_strip, if_false, or_false]


lemma inv_interp_strip_of_zero_def (f: ℂ → ℂ ) (h: (sSup_abs_im f 0) = 0 ∨ (sSup_abs_im f 1) = 0) : 
  inv_interp_strip f z = 0 :=
  if_pos h

-- Differentiable continuous function inv_interp_strip
lemma inv_interp_strip_diff_cont (f: ℂ → ℂ) : 
  DiffContOnCl ℂ (inv_interp_strip f) (strip 0 1) := by
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
  have hpos: inv_interp_strip f = λ (z:ℂ) ↦ (sSup_abs_im f 0)^(z-1) * (sSup_abs_im f 1)^(-z) := by
    funext z
    rw [inv_interp_strip_of_pos_def z f (lt_of_le_of_ne (sSup_abs_im_nonneg f 0) h0)
    (lt_of_le_of_ne (sSup_abs_im_nonneg f 1) h1)]
  rw [hpos]
  apply DifferentiableAt.mul _ _
  apply DifferentiableAt.const_cpow (DifferentiableAt.sub_const (differentiableAt_id') 1) _ 
  left; simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]
  apply DifferentiableAt.const_cpow _ _
  rw [differentiableAt_neg_iff]
  apply differentiableAt_id'
  left
  simp only [Ne.def, ofReal_eq_zero]; rwa [eq_comm]



lemma F'_diff_cont (f: ℂ → ℂ) (n : ℕ) (hd : DiffContOnCl ℂ f (strip 0 1)) : 
  DiffContOnCl ℂ (F' n f) (strip 0 1):= by
  apply DiffContOnCl.smul (DiffContOnCl.smul hd (inv_interp_strip_diff_cont f) ) _ 
  apply Differentiable.diffContOnCl
  apply Differentiable.cexp
  apply Differentiable.mul
  rw [differentiable_sub_const_iff]
  apply Differentiable.pow _ 2
  apply differentiable_id'
  apply differentiable_const
      


-- The function f is bounded by sSup_abs_im 
lemma f_le_Sup (f : ℂ → ℂ) (z : ℂ) (hD: z ∈ (closed_strip 0 1)) 
  (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))): abs (f z) ≤ sSup_abs_im f (z.re) :=
begin
  refine le_cSup _ _, 
  { refine bdd_above.mono (image_subset (abs ∘ f) _) hB, 
    apply preimage_mono, simp only [singleton_subset_iff], exact hD, },
  { simp only [mem_image_of_mem (⇑abs ∘ f), mem_preimage, mem_singleton], },
end

lemma cocompact_strip.basis:
has_basis (cocompact_strip 0 1)
(λ T : ℝ × ℝ , true ) (λ T, (im ⁻¹' (Iic (T.1) ∪ Ici (T.2)) ∩ re ⁻¹' Icc 0 1) ):=
begin
  simp only [cocompact_strip, comap_principal, real.cocompact_eq],
  rw ← true_and true,
  exact has_basis.inf_principal (has_basis.comap _ (has_basis.sup at_bot_basis at_top_basis)) _,
end

lemma cocompact_strip.mem_sets {s : set ℂ}:
s ∈ cocompact_strip 0 1
 ↔ ∃ T, ∀ (z : ℂ), z.re ∈ Icc 0 (1:ℝ) → T ≤ |z.im| → z ∈ s :=
begin
rw has_basis.mem_iff cocompact_strip.basis, 
split, 
{ rintro ⟨⟨a,b⟩, h⟩, 
  simp only [preimage_union, exists_true_left, prod.exists] at h, 
  use linear_order.max (-a) b,
  intros z hset him, apply h, 
  refine mem_inter _ hset,
  simp only [mem_preimage, mem_Iic, mem_Ici, mem_union],
  simp only [abs_of_real, max_le_iff] at him,
  cases him with hima himb,
  by_cases 0 ≤ z.im, 
  { right, rwa ← _root_.abs_of_nonneg h },
  { left, rwa [← neg_le_neg_iff, ← abs_of_neg (not_le.mp h)] } },
{ rintro ⟨T, h⟩, 
  use (-T, T),
  simp only [preimage_union, true_and],
  rintro z ⟨him, hset⟩,
  apply h _ hset,
  rwa [le_abs, ← le_neg, or_comm, ← mem_Iic, ← mem_Ici,
   ← mem_union, ← mem_preimage, preimage_union] },
end

lemma _root_.real.tendsto_sq_cocompact_at_top : tendsto (λ x, x^2) (cocompact ℝ) at_top :=
begin
  convert_to tendsto (λ x, ‖x‖ * ‖x‖) (cocompact ℝ) at_top,
  { ext x, rw [pow_two], exact (abs_mul_abs_self _).symm },
  { exact tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top }
end

lemma cocompact_strip.tendsto_sq_im_at_top : tendsto (λ z : ℂ, z.im^2) 
(cocompact_strip 0 1) at_top :=
begin
  refine tendsto_inf_left _,
  change tendsto ((λ x, x^2) ∘ im) (comap im (cocompact ℝ)) at_top,
  rw tendsto_comap'_iff,
  { exact real.tendsto_sq_cocompact_at_top },
  { simp only [univ_mem, range_im] }
end

lemma cocompact_strip.eventually_sq_re_le_one : ∀ᶠ (z : ℂ) in 
(cocompact_strip 0 1), z.re^2 ≤ 1 :=
begin
  rw [cocompact_strip, comap_principal, eventually_inf_principal],
  apply eventually_of_forall, 
  rintro z hz,
  rw sq_le_one_iff hz.1,
  exact hz.2
end

-- Smoothly decreasing function when the real part is bounded eventually ≤ 1
lemma expterm_eventually_le_one (C : ℝ) (n : ℕ) (hn: 1 ≤ n) : ∀ᶠ (z : ℂ)
 in (comap complex.im (cocompact ℝ) ⊓ (comap complex.re (principal  (Icc 0 1)))),
  C * abs(exp ((z^2-1) * (n : ℝ)⁻¹) ) ≤ 1 :=
begin
  refine eventually_le_of_tendsto_lt  (zero_lt_one' ℝ) _,
  simp only [abs_exp], 
  rw show (λ z : ℂ, C * real.exp(((z^2-1) * (n : ℝ)⁻¹).re)) 
    = (λ z : ℂ, C*real.exp((z.re^2 - z.im^2 - 1) * (n : ℝ)⁻¹)),
    { ext1 z, nth_rewrite 0 ← re_add_im z, 
      simp only [tsub_zero, sub_re, one_re, mul_re, zero_div, re_add_im, of_real_nat_cast,
      one_im, nat_cast_im, inv_im, sq, sub_im, mul_im, mul_zero, neg_zero],
      rw [← of_real_nat_cast, ← of_real_inv, of_real_re], },
  nth_rewrite 1 ← mul_zero C, 
  refine tendsto.const_mul C _,
  rw real.tendsto_exp_comp_nhds_zero, 
  apply tendsto.at_bot_mul_const (show 0 < (n:ℝ)⁻¹, 
  { simp only [inv_pos, nat.cast_pos, lt_of_lt_of_le zero_lt_one hn] }),
  -- x.re ^ 2 - x.im ^ 2 - 1 tendsto at_bot
  refine tendsto_at_bot_add_const_right _ (-1) _,
  simp only [sub_eq_add_neg],
  refine tendsto_at_bot_add_left_of_ge' _ (1 : ℝ) cocompact_strip.eventually_sq_re_le_one _,
  rw [tendsto_neg_at_bot_iff], 
  exact cocompact_strip.tendsto_sq_im_at_top
end
 

-- The function F is bounded above because f is.
lemma F_bdd_above (f: ℂ → ℂ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))):
  bdd_above ((abs ∘ F f) '' (closed_strip 0 1)) :=
begin
  -- Rewriting goal
  simp only [F, image_congr, comp_app, map_mul], 
  rw bdd_above_def at *, cases hB with B hB,
  -- Using bound
  use B * ((max 1 ((sSup_abs_im f 0)^-(1:ℝ))) * max 1 ((sSup_abs_im f 1)^-(1:ℝ))), 
  simp only [smul_eq_mul, map_mul, mem_image, forall_exists_index,
   and_imp, forall_apply_eq_imp_iff₂], 
  intros z hset, specialize hB (abs(f z)),
  specialize hB _, 
  { simp only [image_congr, mem_image, comp_app], use z, refine ⟨hset , refl _⟩ },
  -- Proof that the bound is correct
  refine mul_le_mul hB _ (map_nonneg abs _) (le_trans (map_nonneg abs _) hB),
  by_cases (sSup_abs_im f 0) = 0 ∨ (sSup_abs_im f 1) = 0,
  -- Zero case
  { rw inv_interp_strip_of_zero_def z f h, 
    simp only [zero_le_one, true_or, le_max_iff, zero_le_mul_right, 
    map_zero, lt_max_iff, zero_lt_one] },
  -- Positive case
  { push_neg at h,  
    replace h : (0 < sSup_abs_im f 0) ∧ (0 < sSup_abs_im f 1), 
    { rw ne_comm at h, nth_rewrite 1 ne_comm at h,
      exact ⟨ (lt_of_le_of_ne (sSup_abs_im_nonneg f 0) (h.1)), 
      (lt_of_le_of_ne (sSup_abs_im_nonneg f 1) (h.2)) ⟩ },
    simp only [inv_interp_strip_of_pos_def z f h.1 h.2, map_mul],
    refine mul_le_mul _ _ (map_nonneg _ _) (le_trans zero_le_one (le_max_left _ _)), 
    -- Bounding individual terms
    { by_cases hM0_one : 1 ≤ sSup_abs_im f 0,
      -- 1 ≤ (sSup_abs_im f 0)
      { apply le_trans _ (le_max_left _ _),
        simp only [abs_cpow_eq_rpow_re_of_pos h.1, sub_re, one_re, 
        real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)] },
      -- 0 < (sSup_abs_im f 0) < 1
      { rw not_le at hM0_one, apply le_trans _ (le_max_right _ _),
        simp only [abs_cpow_eq_rpow_re_of_pos h.1, sub_re, one_re],
        refine real.rpow_le_rpow_of_exponent_ge (h.1) (le_of_lt hM0_one) _, 
        simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1] }, },
    { by_cases hM1_one : 1 ≤ sSup_abs_im f 1,
      -- 1 ≤ sSup_abs_im f 1
      { apply le_trans _ (le_max_left _ _),
        simp only [abs_cpow_eq_rpow_re_of_pos h.2, sub_re, one_re, neg_re,
        real.rpow_le_one_of_one_le_of_nonpos hM1_one (right.neg_nonpos_iff.mpr hset.1)] },
      -- 0 < sSup_abs_im f 1 < 1
      { rw not_le at hM1_one, apply le_trans _ (le_max_right _ _),
        simp only [abs_cpow_eq_rpow_re_of_pos h.2, sub_re, one_re, neg_re,
        real.rpow_le_rpow_of_exponent_ge (h.2) (le_of_lt hM1_one) 
          (neg_le_neg_iff.mpr hset.2)]  }, }, },
end


lemma F'_eventually_le_one (f: ℂ → ℂ) (n : ℕ) (hn: 1 ≤ n) 
  (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))):
  ∀ᶠ (z : ℂ) in (cocompact_strip 0 1),
  (abs ∘ (F' n f)) z ≤ 1 :=
begin
  simp only [F', comp_app, map_mul, algebra.id.smul_eq_mul, of_real_nat_cast, map_mul], 
  cases (F_bdd_above f hB) with C hF',
  rw mem_upper_bounds at hF',
  refine eventually.mp (expterm_eventually_le_one C n hn) (eventually.filter_mono inf_le_right _),
  rw comap_principal,
  refine eventually_of_mem (mem_principal_self _) _,
  intros z hset hexp,
  specialize hF' (abs (F f z)),
  -- Showing abs (F f z) ∈ abs ∘ F f '' closed_strip 0 1
  specialize hF' _, 
  { simp only [image_congr, mem_image, comp_app], use z, refine ⟨hset , refl _⟩, },
  -- Combining hexp with hF' by trans
  exact le_trans (mul_le_mul hF' (le_refl _) (map_nonneg _ _) 
    (le_trans (map_nonneg _ _) hF')) hexp,
end

-- Proof that the edges are bounded by one
lemma F_edge_le_one (f: ℂ → ℂ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hz: z ∈ re ⁻¹' {0, 1}) :  abs (F f z) ≤ 1 :=
begin
  rw F, simp only [algebra.id.smul_eq_mul, map_mul],
  cases lt_or_eq_of_le (sSup_abs_im_nonneg f 0) with hpos hzero, 
  { cases lt_or_eq_of_le (sSup_abs_im_nonneg f 1) with h1pos h1zero,
    -- Positive case
    { rw inv_interp_strip_of_pos_def z f hpos h1pos,
      simp only [map_mul, abs_cpow_eq_rpow_re_of_pos, hpos, h1pos, sub_re, 
      one_re, neg_re],
      cases hz with hz0 hz1,
      -- z.re = 0 
      { simp only [hz0, mul_one, zero_sub, real.rpow_zero, neg_zero,
        real.rpow_neg_one, mul_inv_le_iff hpos],
        rw ← hz0, refine f_le_Sup f z _ hB,
        simp only [closed_strip, mem_preimage, zero_le_one, left_mem_Icc, hz0], },
      -- z.re = 1
      { rw mem_singleton_iff at hz1,
        simp only [hz1, one_mul, real.rpow_zero, sub_self, real.rpow_neg_one,
        mul_inv_le_iff h1pos, mul_one],
        rw ← hz1, refine f_le_Sup f z _ hB, 
        simp only [closed_strip, mem_preimage, zero_le_one, hz1, right_mem_Icc], }, }, 

    -- Handling cases where sSup_abs_im f 0 = 0 or sSup_abs_im f 1 = 0.
    { rw inv_interp_strip_of_zero_def z f, simp only [zero_le_one, mul_zero, map_zero], 
      right, simp only [h1zero, eq_self_iff_true], }, },
  { rw inv_interp_strip_of_zero_def z f, simp only [zero_le_one, mul_zero, map_zero], 
    left, rw eq_comm, exact hzero, },
end

-- Edges of F' are constructed to be ≤ 1
lemma edges_le_one (f: ℂ → ℂ) (n : ℕ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hz: z ∈ re ⁻¹' {0, 1}) :  (abs ∘ F' n f) z ≤ 1 :=
begin
  -- Small useful lemma
  have hdivnat : 0 ≤ ((n:ℂ)⁻¹).re, 
  { simp only [← of_real_nat_cast n, ← of_real_inv n, of_real_re, inv_nonneg,nat.cast_nonneg], },

  -- Expterm ≤ 1
  have hexp : abs(exp ((z ^ 2 - 1) * (↑n)⁻¹)) ≤ 1, 
  { rw [abs_exp, ← re_add_im z],
    simp only [tsub_zero, sub_re, one_re, add_im, add_zero, mul_one, mul_re, 
      zero_div, zero_mul, of_real_re, add_re, one_im, nat_cast_im, of_real_im, I_im, 
      zero_add, inv_im, sq, sub_im, I_re, real.exp_le_one_iff, mul_im, mul_zero, neg_zero],
    cases hz with hz0 hz1,
    { simp only [hz0, zero_sub, nat_cast_re, mul_zero], 
      refine mul_nonpos_of_nonpos_of_nonneg _ hdivnat,
      simp only [← sq, sub_nonpos, neg_le,
       le_of_lt (lt_of_lt_of_le neg_one_lt_zero (sq_nonneg _))], },
    { simp only [hz1.out, right.neg_nonpos_iff, one_pow, neg_mul, sub_sub_cancel_left,← sq],
      rw mul_nonneg_iff, left, refine ⟨sq_nonneg _ , hdivnat ⟩, }, },

  -- Combining Expterm ≤ 1 with F ≤ 1 on edges
  rw F', 
  simp only [algebra.id.smul_eq_mul, of_real_nat_cast, map_mul, comp_app, map_mul], 
  exact left.mul_le_one_of_le_of_le (F_edge_le_one z f hB hz) hexp (map_nonneg _ _), 
end

-- Show the Theorem on the members of the sequence (F') that tends to F.
lemma abs_le_interp_on_closed_strip_sequence (f : ℂ → ℂ) (z : ℂ)
  (hd : diff_cont_on_cl ℂ f (strip 0 1)) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hz: z ∈ closed_strip 0 1) (n: ℕ) (hn: 1 ≤ n) : 
  (⇑abs ∘ F' n f) z ≤ 1 :=
begin
  rcases (eventually.exists_mem (F'_eventually_le_one f n hn hB)) with ⟨w, ⟨h_w, h_h⟩⟩,
  rw cocompact_strip.mem_sets at h_w,
  cases h_w with B h_w,
  -- Using positive bound to prevent pathologies
  let T := linear_order.max B 1, 
  have h_w_pos : ∀ (z : ℂ), z.re ∈ Icc 0 (1:ℝ)  → T ≤ |z.im| → z ∈ w,
  { intros z hset him, exact h_w z hset (le_trans (le_max_left B 1) him) },

  by_cases (|z.im| ≤ T), 
  -- First case |z.im| ≤ T  
  { have bdd_strip_is_bounded : metric.bounded (bdd_strip 0 1 (T)),
    { exact ((bounded_Ioo _ _).re_prod_im (bounded_Ioo _ _)), },

    --Function is diff_cont_on_cl on subset + multiplied by 'simple' function
    have hd_subset : diff_cont_on_cl ℂ (F' n f) (bdd_strip 0 1 (T)),
    { refine diff_cont_on_cl.mono _ _, use strip 0 1, apply F'_diff_cont f n hd, 
      apply inter_subset_left, },

    apply norm_le_of_forall_mem_frontier_norm_le bdd_strip_is_bounded hd_subset _ _, 

    -- Frontier bounded by one
    { intros z hfz,
      rw [bdd_strip, ← re_prod_im, frontier_re_prod_im] at hfz, 
      cases hfz with hfz1 hfz2,
      { cases hfz1 with hfz_re hfz_im, 
        rw frontier_Ioo at hfz_im, 
        rw closure_Ioo (zero_ne_one' ℝ) at hfz_re,
        apply h_h, apply h_w_pos z hfz_re,
        -- |T| = |z.im|
        apply le_of_eq, 
        rwa [eq_comm, abs_eq (le_trans (zero_le_one' ℝ) (le_max_right B 1)),
         ← mem_singleton_iff, or_comm, ← mem_insert_iff, ← mem_preimage], 
        -- -T < T
        exact neg_lt_self_iff.mpr (lt_of_lt_of_le (zero_lt_one' ℝ) (le_max_right B 1)) },
      { replace hfz_re := mem_of_mem_inter_left hfz2,
        rw frontier_Ioo (zero_lt_one' ℝ) at hfz_re,
        exact edges_le_one z f n hB hfz_re } },
    --Local goal: z ∈ closure (bdd_strip 0 1 T) with h: |z.im| ≤ T and hz: z ∈ strip 0 1.
    { rw [bdd_strip, ← re_prod_im, closure_re_prod_im, closure_Ioo (zero_ne_one' ℝ), closure_Ioo,  
      re_prod_im, mem_inter_iff],
      refine ⟨hz, _⟩,
      rwa [mem_preimage, mem_Icc, ← abs_le],  
      apply ne_of_lt, 
      exact neg_lt_self_iff.mpr (lt_of_lt_of_le (zero_lt_one' ℝ) (le_max_right B 1)), }, },

  --Now : T < |z.im|.
  { simp only [not_le] at h, apply h_h, apply h_w_pos z hz (le_of_lt h), },
end

--Proof that F' tendsto F
lemma F_seq_to_F (f : ℂ → ℂ) (z : ℂ) : tendsto (λ n : ℕ, F' n f z ) at_top (nhds (F f z)):=
begin
  have mul_const : tendsto (λ n : ℕ,  (z^2-1) * (n : ℝ)⁻¹) at_top (nhds 0), 
    { by simpa only [mul_zero]
      using tendsto_const_nhds.mul (tendsto_inverse_at_top_nhds_0_nat ℂ), },
  
  have comp_exp : tendsto (λ n : ℕ, exp( (z^2-1) * (n : ℝ)⁻¹)) at_top (nhds 1), 
    { by simpa only [exp_zero]
      using  (continuous.tendsto continuous_exp 0).comp mul_const, },

  by simpa only [mul_one]
    using tendsto_const_nhds.mul comp_exp,
end

-- Proof that |F_seq| tendsto |F|
lemma F_seq_to_F_abs (f : ℂ → ℂ) (z : ℂ) :
tendsto (λ n : ℕ, (abs ∘ (F' n f)) z ) at_top (nhds ((abs ∘ (F f)) z)):=
  (continuous.tendsto continuous_abs (F f z)).comp (F_seq_to_F f z)

-- Combination of Hadamard_sequence with F_seq_to_F_abs
theorem abs_le_interp_on_closed_strip (f : ℂ → ℂ) (hd : diff_cont_on_cl ℂ f (strip 0 1))  
   (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))) (z : ℂ) (hz: z ∈ closed_strip 0 1) :
   (abs (f z • inv_interp_strip f z)) ≤ 1 := 
begin
  refine le_of_tendsto (F_seq_to_F_abs f z) _,
  rw eventually_iff_exists_mem, 
  use {n:ℕ | 1 ≤ n}, 
  refine ⟨mem_at_top _ , abs_le_interp_on_closed_strip_sequence f z hd hB hz,⟩, 
end

end hadamard_three_lines
end complex