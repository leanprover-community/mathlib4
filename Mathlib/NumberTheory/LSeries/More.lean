/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Complex
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Topology.Instances.EReal
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# More results on L-series
-/

-- namespace ArithmeticFunction

open Complex Nat LSeries

/-!
### Convergence of L-series
-/

/-- An open right half plane is open. -/
lemma _root_.Complex.isOpen_rightHalfPlane (x : EReal) : IsOpen {z : ℂ | x < z.re} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_re

-- ATTN: the following needs the coercion of `log` to an arithmetic function over `ℂ`

/-- The (point-wise) product of `log : ℕ → ℂ` with `f`. -/
noncomputable abbrev LSeries.logMul (f : ℕ → ℂ) (n : ℕ) : ℂ := Complex.log n * f n

lemma norm_logMul_LSeriesTerm_le_of_re_lt_re (f : ℕ → ℂ) {w : ℂ} {z : ℂ}
    (h : w.re < z.re) (n : ℕ) :
    ‖LSeriesTerm (logMul f) z n‖ ≤ ‖LSeriesTerm f w n‖ / (z.re - w.re) := by
    -- ‖log n * f n / n ^ z‖ ≤ ‖f n / n ^ w‖ / (z.re - w.re) := by
  have hwz : 0 < z.re - w.re := sub_pos.mpr h
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeriesTerm_zero, norm_zero, zero_div, le_refl]
  simp only [LSeriesTerm_pos _ _ hn]
  rw [mul_div_assoc, norm_mul]
  refine mul_le_mul_of_nonneg_right (norm_log_natCast_le_rpow_div n hwz) (norm_nonneg _)|>.trans ?_
  rw [mul_comm_div, mul_div, div_le_div_right hwz]
  simp_rw [norm_div, norm_natCast_cpow_of_pos hn]
  rw [mul_div_left_comm, ← Real.rpow_sub <| Nat.cast_pos.mpr hn, sub_sub_cancel_left,
    Real.rpow_neg n.cast_nonneg, div_eq_mul_inv]

/-- If the L-series of `f` is summable at `w` and `re w < re z`, then the L-series of the
point-wise product of `log` with `f` is summable at `z`. -/
lemma LSeriesSummable.logMul_of_re_lt_re {f : ℕ → ℂ} {w : ℂ} {z : ℂ}
    (h : w.re < z.re) (hf : LSeriesSummable f w) :
    LSeriesSummable (logMul f) z := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact (hf.div_const _).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_logMul_LSeriesTerm_le_of_re_lt_re f h)

/-- If the L-series of the point-wise product of `log` with `f` is summable at `z`, then
so is the L-series of `f`. -/
lemma LSeriesSummable.of_LSeriesSummable_logMul  {f : ℕ → ℂ} {z : ℂ}
    (h : LSeriesSummable (fun n ↦ Complex.log n * f n) z) : LSeriesSummable f z := by
  refine h.norm.of_norm_bounded_eventually_nat (fun n ↦ ‖LSeriesTerm (logMul f) z n‖) ?_
  simp only [norm_div, natCast_log, norm_mul, Filter.eventually_atTop]
  refine ⟨3, fun n hn ↦ ?_⟩
  simp only [LSeriesTerm_pos _ _ (show 0 < n by linarith), LSeries.logMul, norm_div, norm_mul]
  conv => enter [1, 1]; rw [← one_mul (‖f n‖)]
  gcongr
  rw [← natCast_log, norm_eq_abs, abs_ofReal,
    _root_.abs_of_nonneg <| Real.log_nonneg <| by norm_cast; linarith]
  calc 1
    _ = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log 3 := Real.log_le_log (by positivity) <|
                       (Real.exp_one_lt_d9.trans <| by norm_num).le
    _ ≤ Real.log n := Real.log_le_log zero_lt_three <| by exact_mod_cast hn

/-- The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`. -/
lemma abscissaOfAbsConv_logMul {f : ℕ → ℂ} :
    abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f := by
  refine le_antisymm ?_ ?_
  · refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
    obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hy
    have hx₁' : abscissaOfAbsConv f < ↑((x : ℂ).re) := by simp only [ofReal_re, hx₁]
    have hx₂' : (x : ℂ).re < (y : ℂ).re := by simp only [ofReal_re, EReal.coe_lt_coe_iff.mp hx₂]
    exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁').logMul_of_re_lt_re hx₂'
  · refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
    have hy' : abscissaOfAbsConv (logMul f) < ↑((y : ℂ).re) := by simp only [ofReal_re, hy]
    exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hy').of_LSeriesSummable_logMul

/-- The (point-wise) product of the `n`th power of `log` with `f`. -/
noncomputable abbrev logPowMul (n : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  (Complex.log m) ^ n * f m

lemma logPowMul_zero (f : ℕ → ℂ) : logPowMul 0 f = f := by
  ext
  simp only [logPowMul, _root_.pow_zero, one_mul]

lemma logPowMul_succ (n : ℕ) (f : ℕ → ℂ) : logPowMul n.succ f = logMul (logPowMul n f) := by
  ext
  simp only [logPowMul, _root_.pow_succ, mul_assoc, logMul]

lemma logPowMul_succ' (n : ℕ) (f : ℕ → ℂ) : logPowMul n.succ f = logPowMul n (logMul f) := by
  ext n
  simp only [logPowMul, _root_.pow_succ, logMul, ← mul_assoc]
  rw [mul_comm (Complex.log n)]

/-- The abscissa of absolute convergence of the point-wise product of a power of `log` and `f`
is the same as that of `f`. -/
lemma absicssaOfAbsConv_pmul_ppow_log {f : ℕ → ℂ} {n : ℕ} :
    abscissaOfAbsConv (logPowMul n f) = abscissaOfAbsConv f := by
  induction' n with n ih
  · simp only [zero_eq, logPowMul_zero]
  · rwa [logPowMul_succ, abscissaOfAbsConv_logMul]

/-!
### Differentiability and derivatives of L-series
-/

/-- The derivative of the terms of an L-series. -/
lemma LSeriesTerm_hasDerivAt (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ LSeriesTerm f z n) (-(LSeriesTerm (logMul f) s n)) s := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp only [LSeriesTerm_zero, neg_zero, hasDerivAt_const]
  have hn : 0 < n := Nat.pos_of_ne_zero hn₀
  simp only [LSeriesTerm_ne_zero _ _ hn₀]
  rw [← neg_div, ← neg_mul, mul_comm, mul_div_assoc]
  simp_rw [div_eq_mul_inv, ← cpow_neg]
  refine HasDerivAt.const_mul (f n) ?_
  rw [mul_comm, ← mul_neg_one (Complex.log n), ← mul_assoc]
  exact (hasDerivAt_neg' s).const_cpow (Or.inl <| Nat.cast_ne_zero.mpr hn.ne')

/-- The derivative of the terms of an L-series. -/
lemma LSeriesTerm_deriv (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    deriv (fun z ↦ LSeriesTerm f z n) s = -(LSeriesTerm (logMul f) s n) :=
  (LSeriesTerm_hasDerivAt f n s).deriv

/-- The derivative of the terms of an L-series. -/
lemma LSeriesTerm_deriv' (f : ℕ → ℂ) (n : ℕ) :
    deriv (fun z ↦ LSeriesTerm f z n) = fun s ↦ -(LSeriesTerm (logMul f) s n) := by
  ext
  exact LSeriesTerm_deriv ..

section iterated

namespace deriv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open ContinuousLinearMap in
lemma comp_neg (f : 𝕜 → F) (a : 𝕜) : deriv (fun x ↦ f (-x)) a = -deriv f (-a) := by
  by_cases h : DifferentiableAt 𝕜 f (-a)
  · simp_rw [← fderiv_deriv]
    change (fderiv 𝕜 (f ∘ fun x ↦ -x) a) 1 = _
    rw [fderiv.comp _ h differentiable_neg.differentiableAt, show @Neg.neg 𝕜 _ = (- ·) from rfl,
      coe_comp', Function.comp_apply, fderiv_neg, fderiv_id', neg_apply, coe_id', id_eq, map_neg]
  · have H : ¬ DifferentiableAt 𝕜 (fun x ↦ f (-x)) a := by
      contrapose! h
      rw [← neg_neg a] at h
      convert h.comp (-a) differentiable_neg.differentiableAt
      ext
      simp only [Function.comp_apply, neg_neg]
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt H, neg_zero]

-- #find_home comp_neg -- [Mathlib.Analysis.Calculus.Deriv.Add]

/-- A variant of `deriv_const_smul` without differentiability assumption when the scalar
multiplication is by field elements. -/
lemma const_smul {f : 𝕜 → F} {x : 𝕜} {R : Type*} [Field R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] (c : R) :
    deriv (fun y ↦ c • f y) x = c • deriv f x := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact deriv_const_smul c hf
  · rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul, deriv_const']
    · have H : ¬DifferentiableAt 𝕜 (fun y ↦ c • f y) x := by
        contrapose! hf
        change DifferentiableAt 𝕜 (fun y ↦ f y) x
        conv => enter [2, y]; rw [← inv_smul_smul₀ hc (f y)]
        exact DifferentiableAt.const_smul hf c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt H, smul_zero]

-- #find_home const_smul -- [Mathlib.Analysis.Calculus.Deriv.Mul]

end deriv

namespace iteratedDeriv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  induction' n with n ih generalizing a
  · simp only [Nat.zero_eq, iteratedDeriv_zero]
  · have ih' : iteratedDeriv n (fun x ↦ -f x) = fun x ↦ -iteratedDeriv n f x := funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', deriv.neg]

lemma comp_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  induction' n with n ih generalizing a
  · simp only [Nat.zero_eq, iteratedDeriv_zero, _root_.pow_zero, one_smul]
  · have ih' : iteratedDeriv n (fun x ↦ f (-x)) = fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (-x) :=
      funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', _root_.pow_succ, neg_mul, one_mul,
      deriv.comp_neg (f := fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f x), deriv.const_smul, neg_smul]

end iteratedDeriv

end iterated

/-- The higher derivatives of the terms of an L-series. -/
lemma LSeriesTerm_iteratedDeriv (f : ℕ → ℂ) (m n : ℕ) (s : ℂ) :
    iteratedDeriv m (fun z ↦ LSeriesTerm f z n) s =
      (-1) ^ m * (LSeriesTerm (logPowMul m f) s n) := by
  induction' m with m ih generalizing f s
  · simp only [zero_eq, iteratedDeriv_zero, _root_.pow_zero, logPowMul_zero, one_mul]
  · have ih' : iteratedDeriv m (fun z ↦ LSeriesTerm (logMul f) z n) =
        fun s ↦ (-1) ^ m * (LSeriesTerm (logPowMul m (logMul f)) s n) :=
      funext <| ih (logMul f)
    rw [iteratedDeriv_succ', LSeriesTerm_deriv' f n, iteratedDeriv.neg, ih', neg_mul_eq_neg_mul,
      logPowMul_succ', _root_.pow_succ, neg_one_mul]

/-- If `re z` is greater than the abscissa of absolute convergence of `f`, then the L-series
of `f` is differentiable with derivative the negative of the L-series of the point-wise
product of `log` with `f`. -/
lemma LSeries.hasDerivAt {f : ℕ → ℂ} {z : ℂ} (h : abscissaOfAbsConv f < z.re) :
    HasDerivAt (LSeries f) (- LSeries (logMul f) z) z := by
  -- The L-series of `f` is summable at some real `x < re z`.
  obtain ⟨x, h', hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  change HasDerivAt (fun s ↦ LSeries f s) ..
  simp only [LSeries, ← tsum_neg]
  -- We work in the right half-plane `re s > (x + re z)/2`.
  let S : Set ℂ := {s | (x + z.re) / 2 < s.re}
  have hop : IsOpen S := isOpen_lt continuous_const continuous_re
  have hpr : IsPreconnected S := (convex_halfspace_re_gt _).isPreconnected
  have hmem : z ∈ S := by
    simp only [Set.mem_setOf_eq]
    linarith only [h']
  -- To get a uniform summable bound for the derivative series, we use that we
  -- have summability of the L-series of `pmul log f` at `(x + z)/2`.
  have hx : (x : ℂ).re < ((x + z) / 2).re := by
    simp only [add_re, ofReal_re, div_ofNat_re, sub_re]
    linarith only [h']
  have hf' := hf.logMul_of_re_lt_re hx
  rw [LSeriesSummable, ← summable_norm_iff] at hf'
  -- Show that the terms have the correct derivative.
  have hderiv (n : ℕ) :
      ∀ s ∈ S, HasDerivAt (fun z ↦ LSeriesTerm f z n) (-(LSeriesTerm (logMul f) s n)) s := by
    exact fun s _ ↦ LSeriesTerm_hasDerivAt f n s
  refine hasDerivAt_tsum_of_isPreconnected (F := ℂ) hf' hop hpr hderiv
    (fun n s hs ↦ ?_) hmem (hf.of_re_le_re <| ofReal_re x ▸ h'.le) hmem
  -- Show that the derivative series is uniformly bounded term-wise.
  simp only [norm_neg, norm_div, norm_mul]
  refine norm_LSeriesTerm_le_of_re_le_re _ ?_ _
  simp only [Set.mem_setOf_eq, div_ofNat_re, add_re, ofReal_re] at hs ⊢
  exact hs.le

/-- If `re z` is greater than the abscissa of absolute convergence of `f`, then
the derivative of this L-series is the negative of the L-series of `log * f`. -/
lemma LSeries_deriv {f : ℕ → ℂ} {z : ℂ} (h : abscissaOfAbsConv f < z.re) :
    deriv (LSeries f) z = - LSeries (logMul f) z :=
  (LSeries.hasDerivAt h).deriv

/-- The derivative of the L-series of `f` agrees with the negative of the L-series of
`log * f` on the right half-plane of absolute convergence. -/
lemma LSeries_deriv_eqOn {f : ℕ → ℂ} :
    {z | abscissaOfAbsConv f < z.re}.EqOn (deriv (LSeries f)) (- LSeries (logMul f)) :=
  deriv_eqOn (isOpen_rightHalfPlane _) fun _ hz ↦ HasDerivAt.hasDerivWithinAt <|
    LSeries.hasDerivAt hz

/-- If `re z` is greater than the abscissa of absolute convergence of `f`, then
the `n`th derivative of this L-series is `(-1)^n` times the L-series of `log^n * f`. -/
lemma LSeries_iteratedDeriv {f : ℕ → ℂ} (n : ℕ) {z : ℂ}
    (h : abscissaOfAbsConv f < z.re) :
    iteratedDeriv n (LSeries f) z = (-1) ^ n * LSeries (logPowMul n f) z := by
  induction' n with n ih generalizing z
  · simp only [zero_eq, iteratedDeriv_zero, _root_.pow_zero, logPowMul_zero, one_mul]
  · have ih' : {z | abscissaOfAbsConv f < z.re}.EqOn (iteratedDeriv n (LSeries f))
        ((-1) ^ n * LSeries (logPowMul n f)) := by
      exact fun _ hs ↦ ih hs
    rw [iteratedDeriv_succ]
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOpen_rightHalfPlane _) h] at this
    rw [this]
    change deriv (fun z ↦ (-1) ^ n * LSeries (logPowMul n f) z) z = _
    rw [deriv_const_mul_field', _root_.pow_succ', mul_assoc, neg_one_mul]
    simp only [LSeries_deriv <| absicssaOfAbsConv_pmul_ppow_log.symm ▸ h, logPowMul_succ]

/-- The L-series of `f` is complex differentiable in its open half-plane of absolute
convergence. -/
lemma LSeries.differentiableOn {f : ℕ → ℂ} :
    DifferentiableOn ℂ (LSeries f) {z | abscissaOfAbsConv f < z.re} :=
  fun _ hz ↦ (LSeries.hasDerivAt hz).differentiableAt.differentiableWithinAt

/-!
### Multiplication of L-series
-/

open BigOperators

/-- Dirichlet convolution of two sequences. -/
noncomputable def LSeries.convolution (f g : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2

@[inherit_doc]
infixl:70 " ⍟ " => convolution

lemma convolution_def (f g : ℕ → ℂ) (n : ℕ) :
    (f ⍟ g) n = ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2 :=
  rfl

lemma convolution_def' (f g : ℕ → ℂ) :
    f ⍟ g = fun n ↦ ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2 :=
  rfl

open Set in
lemma LSeriesTerm_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeriesTerm (f ⍟ g) s n =
      ∑' (b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}),
        LSeriesTerm f s b.val.1 * LSeriesTerm g s b.val.2 := by
  let m : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  let h : ℕ × ℕ → ℂ := fun x ↦ LSeriesTerm f s x.1 * LSeriesTerm g s x.2
  rcases n.eq_zero_or_pos with rfl | hn
  · trans 0 -- show that both sides vanish when `n = 0`
    · -- by definition, the left hand sum is over the empty set
      exact LSeriesTerm_zero ..
    · -- the right hand sum is over the union below, but in each term, one factor is always zero
      have hS : m ⁻¹' {0} = {0} ×ˢ univ ∪ (univ \ {0}) ×ˢ {0} := by
        ext
        simp only [m, mem_preimage, mem_singleton_iff, _root_.mul_eq_zero, mem_union, mem_prod,
          mem_univ, mem_diff]
        tauto
      rw [tsum_congr_set_coe h hS,
        tsum_union_disjoint (Disjoint.set_prod_left disjoint_sdiff_right ..) ?_ ?_,
          -- (hsum.subtype _) (hsum.subtype _),
        tsum_setProd_singleton_left 0 _ h, tsum_setProd_singleton_right _ 0 h]
      · simp only [LSeriesTerm_zero, zero_mul, tsum_zero, mul_zero, add_zero]
      · simp only [Function.comp_def]
        convert summable_zero with p
        rw [Set.mem_singleton_iff.mp p.prop.1, LSeriesTerm_zero, zero_mul]
      · simp only [Function.comp_def]
        convert summable_zero with p
        rw [Set.mem_singleton_iff.mp p.prop.2, LSeriesTerm_zero, mul_zero]
  -- now `n > 0`
  have H : n.divisorsAntidiagonal = m ⁻¹' {n} := by
    ext x
    replace hn := hn.ne' -- for `tauto` below
    simp only [Finset.mem_coe, mem_divisorsAntidiagonal, m, mem_preimage, mem_singleton_iff]
    tauto
  rw [← H, Finset.tsum_subtype' n.divisorsAntidiagonal h, LSeriesTerm_pos _ _ hn, convolution_def,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp only [h]
  obtain ⟨hp, hn₀⟩ := mem_divisorsAntidiagonal.mp hp
  have ⟨hp₁, hp₂⟩ := mul_ne_zero_iff.mp <| hp.symm ▸ hn₀
  rw [LSeriesTerm_ne_zero f s hp₁, LSeriesTerm_ne_zero g s hp₂, mul_comm_div, div_div,
    ← mul_div_assoc, ← natCast_mul_natCast_cpow, ← Nat.cast_mul, mul_comm p.2, hp]

open Set in
/-- The L-series of the convolution product `f ⍟ g` of two arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum.mul {f g : ℕ → ℂ} {s a b : ℂ}
    (hf : LSeriesHasSum f s a) (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  simp only [LSeriesHasSum]
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  let m : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  convert (HasSum.mul hf hg hsum).tsum_fiberwise m with n
  exact LSeriesTerm_convolution ..

/-- The L-series of the convolution product `f ⍟ g` of two arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_mul {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.mul hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/-- The L-series of the convolution product `f ⍟ g` of two arithmetic functions `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_mul' {f g : ℕ → ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_mul (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/-- The L-series of the convolution product `f ⍟ g` of two arithmetic functions `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable_mul {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.mul hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

-- end ArithmeticFunction
