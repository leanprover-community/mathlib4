/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Basic
import Mathlib.NumberTheory.ZetaValues

#align_import number_theory.zeta_function from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `riemannCompletedZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `riemannCompletedZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points (which are not arbitrary, but
I haven't checked exactly what they are).

## Main results:

* `differentiable_completed_zeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completed_zeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `riemannCompletedZeta₀_one_sub`, `riemannCompletedZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`
* `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
* `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## Outline of proofs:

We define two related functions on the reals, `zetaKernel₁` and `zetaKernel₂`. The first is
`(θ (t * I) - 1) / 2`, where `θ` is Jacobi's theta function; its Mellin transform is exactly the
completed zeta function. The second is obtained by subtracting a linear combination of powers on
the interval `Ioc 0 1` to give a function with exponential decay at both `0` and `∞`. We then define
`riemannCompletedZeta₀` as the Mellin transform of the second zeta kernel, and define
`riemannCompletedZeta` and `riemannZeta` from this.

Since `zetaKernel₂` has rapid decay and satisfies a functional equation relating its values at `t`
and `1 / t`, we deduce the analyticity of `riemannCompletedZeta₀` and the functional equation
relating its values at `s` and `1 - s`. On the other hand, since `zetaKernel₁` can be expanded in
powers of `exp (-π * t)` and the Mellin transform integrated term-by-term, we obtain the relation
to the naive Dirichlet series `∑' (n : ℕ), 1 / (n + 1) ^ s`.
-/


open MeasureTheory Set Filter Asymptotics TopologicalSpace Real Asymptotics

open Complex hiding exp norm_eq_abs abs_of_nonneg abs_two continuous_exp

open scoped Topology Real Nat

noncomputable section

/-!
## Definition of the Riemann zeta function and related functions
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- Function whose Mellin transform is `π ^ (-s) * Γ(s) * zeta (2 * s)`, for `1 / 2 < Re s`. -/
def zetaKernel₁ (t : ℝ) : ℂ :=
  ∑' n : ℕ, rexp (-π * t * ((n : ℝ) + 1) ^ 2)
#align zeta_kernel₁ zetaKernel₁

/-- Modified zeta kernel, whose Mellin transform is entire. --/
def zetaKernel₂ : ℝ → ℂ :=
  zetaKernel₁ + indicator (Ioc 0 1) fun t => ((1 - 1 / sqrt t) / 2 : ℂ)
#align zeta_kernel₂ zetaKernel₂

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def riemannCompletedZeta₀ (s : ℂ) : ℂ :=
  mellin zetaKernel₂ (s / 2)
#align riemann_completed_zeta₀ riemannCompletedZeta₀

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
def riemannCompletedZeta (s : ℂ) : ℂ :=
  riemannCompletedZeta₀ s - 1 / s + 1 / (s - 1)
#align riemann_completed_zeta riemannCompletedZeta

/-- The Riemann zeta function `ζ(s)`. We set this to be irreducible to hide messy implementation
details. -/
irreducible_def riemannZeta :=
  Function.update (fun s : ℂ =>
    (π : ℂ) ^ (s / 2) * riemannCompletedZeta s / Gamma (s / 2)) 0 (-1 / 2)
#align riemann_zeta riemannZeta

/- Note the next lemma is true by definition; what's hard is to show that with this definition, `ζ`
is continuous (and indeed analytic) at 0, see `differentiableAt_riemannZeta` below. -/
/-- We have `ζ(0) = -1 / 2`. -/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  rw [riemannZeta_def]
  exact Function.update_same _ _ _
#align riemann_zeta_zero riemannZeta_zero

/-!
## First properties of the zeta kernels
-/



/-- The sum defining `zetaKernel₁` is convergent. -/
theorem summable_exp_neg_pi_mul_nat_sq {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => rexp (-π * t * ((n : ℝ) + 1) ^ 2) := by
  have : 0 < (↑t * I).im := by rwa [ofReal_mul_im, I_im, mul_one]
  convert summable_norm_iff.mpr (hasSum_nat_jacobiTheta this).summable using 1
  ext1 n
  rw [Complex.norm_eq_abs, Complex.abs_exp]
  rw [show ↑π * I * ((n : ℂ) + 1) ^ 2 * (↑t * I) = ((π * t * ((n : ℝ) + 1) ^ 2) : ℝ) * I ^ 2 by
    push_cast; ring]
  rw [I_sq, mul_neg_one, ← ofReal_neg, ofReal_re, neg_mul, neg_mul]
#align summable_exp_neg_pi_mul_nat_sq summable_exp_neg_pi_mul_nat_sq

/-- Relate `zetaKernel₁` to the Jacobi theta function on `ℍ`. (We don't use this as the definition
of `zetaKernel₁`, since the sum over `ℕ` rather than `ℤ` is more convenient for relating zeta to
the Dirichlet series for `re s > 1`.) -/
theorem zetaKernel₁_eq_jacobiTheta {t : ℝ} (ht : 0 < t) :
    zetaKernel₁ t = (jacobiTheta (t * I) - 1) / 2 := by
  rw [jacobiTheta_eq_tsum_nat ((mul_I_im t).symm ▸ ht : 0 < (↑t * I).im), add_comm, add_sub_cancel,
    mul_div_cancel_left _ (two_ne_zero' ℂ), zetaKernel₁]
  congr 1 with n : 1
  push_cast
  rw [(by ring : ↑π * I * ((n : ℂ) + 1) ^ 2 * (t * I) = I ^ 2 * π * t * ((n : ℂ) + 1) ^ 2),
    I_sq, neg_one_mul]
#align zeta_kernel₁_eq_jacobi_theta zetaKernel₁_eq_jacobiTheta

/-- Continuity of `zetaKernel₁`. -/
theorem continuousAt_zetaKernel₁ {t : ℝ} (ht : 0 < t) : ContinuousAt zetaKernel₁ t := by
  have : ContinuousAt (fun u : ℝ => (jacobiTheta (u * I) - 1) / 2) t := by
    refine' (ContinuousAt.sub _ continuousAt_const).div_const _
    refine' (continuousAt_jacobiTheta _).comp (ContinuousAt.mul _ continuousAt_const)
    · rwa [mul_I_im, ofReal_re]
    · exact continuous_ofReal.continuousAt
  refine' this.congr (eventually_of_mem (Ioi_mem_nhds ht) fun u hu => _)
  rw [zetaKernel₁_eq_jacobiTheta hu]
#align continuous_at_zeta_kernel₁ continuousAt_zetaKernel₁

/-- Local integrability of `zetaKernel₁`. -/
theorem locally_integrable_zetaKernel₁ : LocallyIntegrableOn zetaKernel₁ (Ioi 0) :=
  (ContinuousAt.continuousOn fun _ ht => continuousAt_zetaKernel₁ ht).locallyIntegrableOn
    measurableSet_Ioi
#align locally_integrable_zeta_kernel₁ locally_integrable_zetaKernel₁

/-- Local integrability of `zetaKernel₂`. -/
theorem locally_integrable_zetaKernel₂ : LocallyIntegrableOn zetaKernel₂ (Ioi 0) := by
  refine (locallyIntegrableOn_iff (Or.inr isOpen_Ioi)).mpr fun k hk hk' => Integrable.add ?_ ?_
  · refine ContinuousOn.integrableOn_compact hk' ?_
    exact ContinuousAt.continuousOn fun x hx => continuousAt_zetaKernel₁ (hk hx)
  · refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict, ← IntegrableOn]
    swap; · exact measurableSet_Ioc
    apply ContinuousOn.integrableOn_compact
    · convert (isCompact_Icc : IsCompact <| Icc (0 : ℝ) 1).inter hk' using 1
      exact
        Set.ext fun t => ⟨fun h => ⟨Ioc_subset_Icc_self h.1, h.2⟩, fun h => ⟨⟨hk h.2, h.1.2⟩, h.2⟩⟩
    · refine ContinuousOn.mono ?_ ((inter_subset_right _ _).trans hk)
      refine (continuousOn_const.sub ?_).div_const _
      refine ContinuousOn.div continuousOn_const ?_ fun x hx => ?_
      · exact (continuous_ofReal.comp continuous_sqrt).continuousOn
      exact ofReal_ne_zero.mpr (sqrt_ne_zero'.mpr hx)
#align locally_integrable_zeta_kernel₂ locally_integrable_zetaKernel₂

/-- Functional equation for `zetaKernel₂`. -/
theorem zetaKernel₂_one_div {t : ℝ} (ht : 0 < t) :
    zetaKernel₂ (1 / t) = sqrt t * zetaKernel₂ t := by
  have aux : ∀ {u : ℝ} (_ : 1 < u), zetaKernel₂ (1 / u) = sqrt u * zetaKernel₂ u := by
    intro u hu
    simp_rw [zetaKernel₂, Pi.add_apply]
    rw [indicator_of_mem, indicator_of_not_mem (not_mem_Ioc_of_gt hu), add_zero]
    swap; · exact ⟨one_div_pos.mpr (zero_lt_one.trans hu), (one_div u).symm ▸ inv_le_one hu.le⟩
    rw [zetaKernel₁_eq_jacobiTheta (one_div_pos.mpr <| zero_lt_one.trans hu),
      zetaKernel₁_eq_jacobiTheta (zero_lt_one.trans hu), ← add_div, ← mul_div_assoc, add_sub,
      sub_add_cancel, sqrt_div zero_le_one, sqrt_one, one_div (sqrt _), ofReal_inv, ← one_div,
      one_div_one_div, mul_sub, mul_one]
    congr 2
    let τ : UpperHalfPlane := .mk (u * I) ((mul_I_im u).symm ▸ zero_lt_one.trans hu)
    convert jacobiTheta_S_smul τ using 2
    · rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk, ← neg_inv,
        mul_inv, inv_I, mul_neg, neg_neg, one_div, ofReal_inv]
    · rw [UpperHalfPlane.coe_mk, mul_comm, mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one,
        sqrt_eq_rpow, ofReal_cpow (zero_lt_one.trans hu).le]
      push_cast
      rfl
  rcases lt_trichotomy 1 t with (h | h | h)
  · exact aux h
  · simp only [← h, div_self, Ne.def, one_ne_zero, not_false_iff, sqrt_one, ofReal_one, one_mul]
  · have := aux (show 1 < 1 / t by rwa [lt_one_div (zero_lt_one' ℝ) ht, div_one])
    rw [one_div_one_div] at this
    rw [this, ← mul_assoc, ← ofReal_mul, ← sqrt_mul ht.le, mul_one_div_cancel ht.ne', sqrt_one,
      ofReal_one, one_mul]
#align zeta_kernel₂_one_div zetaKernel₂_one_div

/-!
## Bounds for zeta kernels

We now establish asymptotic bounds for the zeta kernels as `t → ∞` and `t → 0`, and use these to
show holomorphy of their Mellin transforms (for `1 / 2 < re s` for `zetaKernel₁`, and all `s` for
`zetaKernel₂`). -/

/-- Bound for `zetaKernel₁` for large `t`. -/
theorem isBigO_atTop_zetaKernel₁ : IsBigO atTop zetaKernel₁ fun t => exp (-π * t) := by
  have h := isBigO_at_im_infty_jacobiTheta_sub_one.const_mul_left (1 / 2)
  simp_rw [mul_comm (1 / 2 : ℂ) _, mul_one_div] at h
  have h' : Tendsto (fun t : ℝ => ↑t * I) atTop (comap im atTop) := by
    rw [tendsto_comap_iff]
    convert tendsto_id
    ext1 t
    rw [Function.comp_apply, mul_I_im, ofReal_re, id.def]
  convert ((h.norm_left.comp_tendsto h').congr' (eventually_of_mem (Ioi_mem_atTop 0) fun t ht => _)
        (eventually_of_mem (Ioi_mem_atTop 0) fun t _ => _)).of_norm_left (E' := ℂ)
  · rw [Function.comp_apply, ← zetaKernel₁_eq_jacobiTheta ht]
  · rw [Function.comp_apply, mul_I_im, ofReal_re]
set_option linter.uppercaseLean3 false in
#align is_O_at_top_zeta_kernel₁ isBigO_atTop_zetaKernel₁

/-- Bound for `zetaKernel₂` for large `t`. -/
theorem isBigO_atTop_zetaKernel₂ : IsBigO atTop zetaKernel₂ fun t => exp (-π * t) := by
  refine'
    (eventuallyEq_of_mem (Ioi_mem_atTop (1 : ℝ)) fun t ht => _).trans_isBigO
      isBigO_atTop_zetaKernel₁
  rw [zetaKernel₂, Pi.add_apply, indicator_of_not_mem (not_mem_Ioc_of_gt (Set.mem_Iio.mp ht)),
    add_zero]
set_option linter.uppercaseLean3 false in
#align is_O_at_top_zeta_kernel₂ isBigO_atTop_zetaKernel₂

/-- Precise but awkward-to-use bound for `zetaKernel₂` for `t → 0`. -/
theorem isBigO_zero_zetaKernel₂ : IsBigO (𝓝[>] 0) zetaKernel₂ fun t => exp (-π / t) / sqrt t := by
  have h1 := isBigO_atTop_zetaKernel₂.comp_tendsto tendsto_inv_zero_atTop
  simp_rw [← one_div] at h1
  have h2 : zetaKernel₂ ∘ Div.div 1 =ᶠ[𝓝[>] 0] fun t => sqrt t * zetaKernel₂ t :=
    eventually_of_mem self_mem_nhdsWithin fun t ht => by
      dsimp only; rw [← zetaKernel₂_one_div ht]; rfl
  have h3 := h1.congr' h2 (EventuallyEq.refl _ _)
  have h4 := h3.mul (isBigO_refl (fun t : ℝ => 1 / (sqrt t : ℂ)) (𝓝[>] 0)).norm_right
  refine h4.congr' ?_ ?_
  · refine eventually_of_mem self_mem_nhdsWithin fun x hx => ?_
    dsimp
    rw [mul_comm, ← mul_assoc, one_div_mul_cancel, one_mul]
    exact ofReal_ne_zero.mpr ((sqrt_ne_zero <| le_of_lt hx).mpr (ne_of_gt hx))
  · refine eventually_of_mem self_mem_nhdsWithin fun x _ => ?_
    dsimp only
    rw [Function.comp_apply, mul_one_div, one_div (sqrt x : ℂ), norm_inv, Complex.norm_eq_abs,
      abs_ofReal, abs_of_nonneg (sqrt_nonneg _), ← div_eq_mul_inv]
set_option linter.uppercaseLean3 false in
#align is_O_zero_zeta_kernel₂ isBigO_zero_zetaKernel₂

/-- Weaker but more usable bound for `zetaKernel₂` for `t → 0`. -/
theorem isBigO_zero_zetaKernel₂_rpow (a : ℝ) : IsBigO (𝓝[>] 0) zetaKernel₂ fun t => t ^ a := by
  have aux1 : IsBigO atTop (fun t => exp (-π * t)) fun t => t ^ (-a - 1 / 2) :=
    (isLittleO_exp_neg_mul_rpow_atTop pi_pos _).isBigO
  have aux2 : IsBigO atTop (fun t => exp (-π * t) * sqrt t) fun t => t ^ (-a) := by
    refine (aux1.mul (isBigO_refl sqrt _)).congr' (EventuallyEq.refl _ _) ?_
    refine (eventually_gt_atTop 0).mp (eventually_of_forall fun t ht => ?_)
    simp_rw [sqrt_eq_rpow, ← rpow_add ht, sub_add_cancel]
  refine isBigO_zero_zetaKernel₂.trans ((aux2.comp_tendsto tendsto_inv_zero_atTop).congr' ?_ ?_)
  · refine eventually_of_mem self_mem_nhdsWithin fun x _ => ?_
    simp_rw [Function.comp_apply, sqrt_inv, ← div_eq_mul_inv]
  · refine eventually_of_mem self_mem_nhdsWithin fun x hx => ?_
    simp_rw [Function.comp_apply, inv_rpow (le_of_lt hx), rpow_neg (le_of_lt hx), inv_inv]
set_option linter.uppercaseLean3 false in
#align is_O_zero_zeta_kernel₂_rpow isBigO_zero_zetaKernel₂_rpow

/-- Bound for `zetaKernel₁` for `t → 0`. -/
theorem isBigO_zero_zetaKernel₁ : IsBigO (𝓝[>] 0) zetaKernel₁ fun t => t ^ (-(1 / 2) : ℝ) := by
  have : zetaKernel₁ =ᶠ[𝓝[>] 0] zetaKernel₂ + fun t => ((1 / sqrt t - 1) / 2 : ℂ) := by
    refine
      eventuallyEq_of_mem (Ioc_mem_nhdsWithin_Ioi <| left_mem_Ico.mpr zero_lt_one) fun t h => ?_
    rw [Pi.add_apply, zetaKernel₂, Pi.add_apply, indicator_of_mem h]
    ring
  refine ((isBigO_zero_zetaKernel₂_rpow _).add ?_).congr' this.symm (EventuallyEq.refl _ _)
  simp_rw [sub_div]
  apply IsBigO.sub
  · apply IsBigO.of_norm_left
    simp_rw [norm_div, norm_one, div_eq_mul_inv, one_mul, mul_comm _ ‖(2 : ℂ)‖⁻¹]
    refine ((isBigO_refl _ _).congr' (EventuallyEq.refl _ _)
        (eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => ?_)).const_mul_left _
    rw [Complex.norm_eq_abs, abs_ofReal, abs_of_nonneg (sqrt_nonneg _), sqrt_eq_rpow,
      rpow_neg (le_of_lt hx), one_div]
  · refine isBigO_iff.mpr ⟨‖(1 / 2 : ℂ)‖, ?_⟩
    refine eventually_of_mem (Ioc_mem_nhdsWithin_Ioi <| left_mem_Ico.mpr zero_lt_one) fun t ht => ?_
    refine le_mul_of_one_le_right (norm_nonneg _) ?_
    rw [norm_of_nonneg (rpow_nonneg_of_nonneg ht.1.le _), rpow_neg ht.1.le]
    exact one_le_inv (rpow_pos_of_pos ht.1 _) (rpow_le_one ht.1.le ht.2 one_half_pos.le)
set_option linter.uppercaseLean3 false in
#align is_O_zero_zeta_kernel₁ isBigO_zero_zetaKernel₁

/-!
## Differentiability of the completed zeta function
-/

/-- The Mellin transform of the first zeta kernel is holomorphic for `1 / 2 < re s`. -/
theorem differentiableAt_mellin_zetaKernel₁ {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (mellin zetaKernel₁) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp pi_pos locally_integrable_zetaKernel₁
    isBigO_atTop_zetaKernel₁ isBigO_zero_zetaKernel₁ hs
#align differentiable_at_mellin_zeta_kernel₁ differentiableAt_mellin_zetaKernel₁

/-- The Mellin transform of the second zeta kernel is entire. -/
theorem differentiable_mellin_zetaKernel₂ : Differentiable ℂ (mellin zetaKernel₂) := fun _ =>
  mellin_differentiableAt_of_isBigO_rpow_exp pi_pos locally_integrable_zetaKernel₂
    isBigO_atTop_zetaKernel₂ (isBigO_zero_zetaKernel₂_rpow _) ((sub_lt_self_iff _).mpr zero_lt_one)
#align differentiable_mellin_zeta_kernel₂ differentiable_mellin_zetaKernel₂

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s - 1 / (s - 1)` is entire. -/
theorem differentiable_completed_zeta₀ : Differentiable ℂ riemannCompletedZeta₀ :=
  differentiable_mellin_zetaKernel₂.comp (Differentiable.div_const differentiable_id 2)
#align differentiable_completed_zeta₀ differentiable_completed_zeta₀

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`
(where it has simple poles). -/
theorem differentiableAt_completed_zeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ riemannCompletedZeta s := by
  refine (differentiable_completed_zeta₀.differentiableAt.sub ?_).add ?_
  · exact (Differentiable.differentiableAt (differentiable_const _)).div differentiableAt_id hs
  · refine (differentiable_const _).differentiableAt.div ?_ (sub_ne_zero.mpr hs')
    exact differentiableAt_id.sub (differentiableAt_const _)
#align differentiable_at_completed_zeta differentiableAt_completed_zeta

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s := by
  /- First claim: the result holds at `t` for `t ≠ 0`. Note we will need to use this for the case
    `s = 0` also, as a hypothesis for the removable-singularity criterion. -/
  have c1 : ∀ (t : ℂ) (_ : t ≠ 0) (_ : t ≠ 1),
      DifferentiableAt ℂ
        (fun u : ℂ => (π : ℂ) ^ (u / 2) * riemannCompletedZeta u / Gamma (u / 2)) t := by
    intro t ht ht'
    apply DifferentiableAt.mul
    · refine (DifferentiableAt.const_cpow ?_ ?_).mul (differentiableAt_completed_zeta ht ht')
      · exact DifferentiableAt.div_const differentiableAt_id _
      · exact Or.inl (ofReal_ne_zero.mpr pi_pos.ne')
    · refine differentiable_one_div_Gamma.differentiableAt.comp t ?_
      exact DifferentiableAt.div_const differentiableAt_id _
  -- Second claim: the limit at `s = 0` exists and is equal to `-1 / 2`.
  have c2 : Tendsto (fun s : ℂ => (π : ℂ) ^ (s / 2) * riemannCompletedZeta s / Gamma (s / 2))
      (𝓝[≠] 0) (𝓝 <| -1 / 2) := by
    have h1 : Tendsto (fun z : ℂ => (π : ℂ) ^ (z / 2)) (𝓝 0) (𝓝 1) := by
      convert (ContinuousAt.comp (f := fun z => z/2)
        (continuousAt_const_cpow (ofReal_ne_zero.mpr pi_pos.ne')) ?_).tendsto using 2
      · simp_rw [Function.comp_apply, zero_div, cpow_zero]
      · exact continuousAt_id.div continuousAt_const two_ne_zero
    suffices h2 : Tendsto (fun z => riemannCompletedZeta z / Gamma (z / 2)) (𝓝[≠] 0) (𝓝 <| -1 / 2)
    · convert (h1.mono_left nhdsWithin_le_nhds).mul h2 using 1
      · ext1 x; rw [mul_div]
      · simp only [one_mul]
    suffices h3 :
      Tendsto (fun z => riemannCompletedZeta z * (z / 2) / (z / 2 * Gamma (z / 2))) (𝓝[≠] 0)
        (𝓝 <| -1 / 2)
    · refine Tendsto.congr' (eventuallyEq_of_mem self_mem_nhdsWithin fun z hz => ?_) h3
      rw [← div_div, mul_div_cancel _ (div_ne_zero hz two_ne_zero)]
    have h4 : Tendsto (fun z : ℂ => z / 2 * Gamma (z / 2)) (𝓝[≠] 0) (𝓝 1) := by
      refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
      rw [tendsto_nhdsWithin_iff, (by simp : 𝓝 (0 : ℂ) = 𝓝 (0 / 2))]
      exact
        ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
          eventually_of_mem self_mem_nhdsWithin fun x hx => div_ne_zero hx two_ne_zero⟩
    suffices Tendsto (fun z => riemannCompletedZeta z * z / 2) (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)) by
      have := this.div h4 one_ne_zero
      simp_rw [div_one, mul_div_assoc] at this
      exact this
    refine Tendsto.div ?_ tendsto_const_nhds two_ne_zero
    simp_rw [riemannCompletedZeta, add_mul, sub_mul]
    rw [show 𝓝 (-1 : ℂ) = 𝓝 (0 - 1 + 0) by rw [zero_sub, add_zero]]
    refine (Tendsto.sub ?_ ?_).add ?_
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have : ContinuousAt riemannCompletedZeta₀ 0 :=
        differentiable_completed_zeta₀.continuous.continuousAt
      simpa only [id.def, mul_zero] using Tendsto.mul this tendsto_id
    · refine tendsto_const_nhds.congr' (eventuallyEq_of_mem self_mem_nhdsWithin fun t ht => ?_)
      simp_rw [one_div_mul_cancel ht]
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices ContinuousAt (fun z : ℂ => 1 / (z - 1)) 0 by
        simpa only [id.def, mul_zero] using Tendsto.mul this tendsto_id
      refine continuousAt_const.div (continuousAt_id.sub continuousAt_const) ?_
      simpa only [zero_sub] using neg_ne_zero.mpr one_ne_zero
  -- Now the main proof.
  rcases ne_or_eq s 0 with (hs | rfl)
  · -- The easy case: `s ≠ 0`
    have : {(0 : ℂ)}ᶜ ∈ 𝓝 s := isOpen_compl_singleton.mem_nhds hs
    refine (c1 s hs hs').congr_of_eventuallyEq (eventuallyEq_of_mem this fun x hx => ?_)
    rw [riemannZeta_def]
    apply Function.update_noteq hx
  · -- The hard case: `s = 0`.
    rw [riemannZeta, ← (lim_eq_iff ⟨-1 / 2, c2⟩).mpr c2]
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
        (fun t ht => (c1 t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [zero_div, div_zero, Complex.Gamma_zero, mul_zero, cpow_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto c2 <| one_ne_zero' ℂ).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x => by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' => (hx <| inv_eq_zero.mp hx').elim
#align differentiable_at_riemann_zeta differentiableAt_riemannZeta

/-- The trivial zeroes of the zeta function. -/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [riemannZeta, Function.update_noteq this,
    show -2 * ((n : ℂ) + 1) / 2 = -↑(n + 1) by push_cast; ring, Complex.Gamma_neg_nat_eq_zero,
    div_zero]
#align riemann_zeta_neg_two_mul_nat_add_one riemannZeta_neg_two_mul_nat_add_one

/-- A formal statement of the Riemann hypothesis – constructing a term of this type is worth a
million dollars. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannCompletedZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)), s.re = 1 / 2
#align riemann_hypothesis RiemannHypothesis

/-!
## Relating the Mellin transforms of the two zeta kernels
-/


theorem hasMellin_one_div_sqrt_Ioc {s : ℂ} (hs : 1 / 2 < re s) :
    HasMellin (indicator (Ioc 0 1) (fun t => 1 / ↑(sqrt t) : ℝ → ℂ)) s (1 / (s - 1 / 2)) := by
  have h1 : EqOn (fun t => 1 / ↑(sqrt t) : ℝ → ℂ) (fun t => (t : ℂ) ^ (-1 / 2 : ℂ)) (Ioc 0 1) := by
    intro t ht
    simp_rw [neg_div, cpow_neg, ← one_div, sqrt_eq_rpow, ofReal_cpow ht.1.le]
    norm_num
  simp_rw [indicator_congr h1, (by ring : s - 1 / 2 = s + -1 / 2)]
  convert hasMellin_cpow_Ioc (-1 / 2) _
  rwa [(by norm_num : (-1 / 2 : ℂ) = (-1 / 2 : ℝ)), ofReal_re, neg_div, ← sub_eq_add_neg,
    sub_pos]
#align has_mellin_one_div_sqrt_Ioc hasMellin_one_div_sqrt_Ioc

/-- Evaluate the Mellin transform of the "fudge factor" in `zetaKernel₂` -/
theorem hasMellin_one_div_sqrt_sub_one_div_two_Ioc {s : ℂ} (hs : 1 / 2 < s.re) :
    HasMellin ((Ioc 0 1).indicator fun t => (1 - 1 / (sqrt t : ℂ)) / 2) s
      (1 / (2 * s) - 1 / (2 * s - 1)) := by
  have step1 :
    HasMellin (indicator (Ioc 0 1) (fun t => 1 - 1 / ↑(sqrt t) : ℝ → ℂ)) s
      (1 / s - 1 / (s - 1 / 2)) := by
    have a := hasMellin_one_Ioc (one_half_pos.trans hs)
    have b := hasMellin_one_div_sqrt_Ioc hs
    simpa only [a.2, b.2, ← indicator_sub] using hasMellin_sub a.1 b.1
  -- todo: implement something like "indicator.const_div" (blocked by the port for now)
  rw [show
      ((Ioc 0 1).indicator fun t => (1 - 1 / (sqrt t : ℂ)) / 2) = fun t =>
        (Ioc 0 1).indicator (fun t => 1 - 1 / (sqrt t : ℂ)) t / 2
      by ext1 t; simp_rw [div_eq_inv_mul, indicator_mul_right]]
  simp_rw [HasMellin, mellin_div_const, step1.2, sub_div, div_div]
  refine ⟨step1.1.div_const _, ?_⟩
  rw [mul_comm, sub_mul, div_mul_cancel _ (two_ne_zero' ℂ), mul_comm s 2]
#align has_mellin_one_div_sqrt_sub_one_div_two_Ioc hasMellin_one_div_sqrt_sub_one_div_two_Ioc

theorem mellin_zetaKernel₂_eq_of_lt_re {s : ℂ} (hs : 1 / 2 < s.re) :
    mellin zetaKernel₂ s = mellin zetaKernel₁ s + 1 / (2 * s) - 1 / (2 * s - 1) := by
  have h :=
    mellinConvergent_of_isBigO_rpow_exp pi_pos locally_integrable_zetaKernel₁
      isBigO_atTop_zetaKernel₁ isBigO_zero_zetaKernel₁ hs
  have h' := hasMellin_one_div_sqrt_sub_one_div_two_Ioc hs
  simp_rw [zetaKernel₂, Pi.add_def, add_sub_assoc, (hasMellin_add h h'.1).2, h'.2]
#align mellin_zeta_kernel₂_eq_of_lt_re mellin_zetaKernel₂_eq_of_lt_re

theorem completed_zeta_eq_mellin_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    riemannCompletedZeta s = mellin zetaKernel₁ (s / 2) := by
  have : 1 / 2 < (s / 2).re := by
    rw [show s / 2 = ↑(2⁻¹ : ℝ) * s by push_cast; rw [mul_comm]; rfl]
    rwa [ofReal_mul_re, ← div_eq_inv_mul, div_lt_div_right (zero_lt_two' ℝ)]
  rw [riemannCompletedZeta, riemannCompletedZeta₀, mellin_zetaKernel₂_eq_of_lt_re this, sub_add,
    sub_sub, ← add_sub]
  conv_rhs => rw [← add_zero (mellin zetaKernel₁ <| s / 2)]
  congr 1
  rw [mul_div_cancel' _ (two_ne_zero' ℂ)]
  abel
#align completed_zeta_eq_mellin_of_one_lt_re completed_zeta_eq_mellin_of_one_lt_re

/-!
## Relating the first zeta kernel to the Dirichlet series
-/


/-- Auxiliary lemma for `mellin_zetaKernel₁_eq_tsum`, computing the Mellin transform of an
individual term in the series. -/
theorem integral_cpow_mul_exp_neg_pi_mul_sq {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * rexp (-π * t * ((n : ℝ) + 1) ^ 2) =
      (π : ℂ) ^ (-s) * Complex.Gamma s * (1 / ((n : ℂ) + 1) ^ (2 * s)) := by
  rw [Complex.Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  conv_rhs =>
    congr
    rw [← smul_eq_mul, ← mellin_comp_mul_left _ _ pi_pos]
  have : 1 / ((n : ℂ) + 1) ^ (2 * s) = (((n : ℝ) + 1) ^ (2 : ℝ) : ℂ) ^ (-s) := by
    rw [(by norm_num : (n : ℂ) + 1 = ↑((n : ℝ) + 1)), (by norm_num : 2 * s = ↑(2 : ℝ) * s),
      cpow_mul_ofReal_nonneg, one_div, cpow_neg]
    rw [← Nat.cast_succ]
    exact Nat.cast_nonneg _
  conv_rhs => rw [this, mul_comm, ← smul_eq_mul]
  rw [← mellin_comp_mul_right _ _ (show 0 < ((n : ℝ) + 1) ^ (2 : ℝ) by positivity)]
  refine set_integral_congr measurableSet_Ioi fun t _ => ?_
  simp_rw [smul_eq_mul]
  congr 3
  conv_rhs => rw [← Nat.cast_two, rpow_nat_cast]
  ring
#align integral_cpow_mul_exp_neg_pi_mul_sq integral_cpow_mul_exp_neg_pi_mul_sq

theorem mellin_zetaKernel₁_eq_tsum {s : ℂ} (hs : 1 / 2 < s.re) :
    mellin zetaKernel₁ s = (π : ℂ) ^ (-s) * Gamma s * ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * s) := by
  let bd : ℕ → ℝ → ℝ := fun n t => t ^ (s.re - 1) * exp (-π * t * ((n : ℝ) + 1) ^ 2)
  let f : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s - 1) * exp (-π * t * ((n : ℝ) + 1) ^ 2)
  have hm : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  have h_norm : ∀ (n : ℕ) {t : ℝ} (_ : 0 < t), ‖f n t‖ = bd n t := by
    intro n t ht
    rw [norm_mul, Complex.norm_eq_abs, Complex.norm_eq_abs, Complex.abs_of_nonneg (exp_pos _).le,
      abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  have hf_meas : ∀ n : ℕ, AEStronglyMeasurable (f n) (volume.restrict <| Ioi 0) := by
    intro n
    refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable hm
    · exact ContinuousAt.continuousOn fun x hx =>
          continuousAt_ofReal_cpow_const _ _ <| Or.inr <| ne_of_gt hx
    · apply Continuous.continuousOn
      exact continuous_ofReal.comp
          (continuous_exp.comp ((continuous_const.mul continuous_id').mul continuous_const))
  have h_le : ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ‖f n t‖ ≤ bd n t := fun n =>
    (ae_restrict_iff' hm).mpr (ae_of_all _ fun t ht => le_of_eq (h_norm n ht))
  have h_sum0 : ∀ {t : ℝ} (_ : 0 < t), HasSum (fun n => f n t)
      ((t : ℂ) ^ (s - 1) * zetaKernel₁ t) := by
    intro t ht
    rw [zetaKernel₁]
    convert
      (hasSum_ofReal.mpr (summable_exp_neg_pi_mul_nat_sq ht).hasSum).mul_left ((t : ℂ) ^ (s - 1))
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_pow, ofReal_add,
      ofReal_nat_cast, ofReal_one, ofReal_tsum]
  have h_sum' : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), HasSum (fun n : ℕ => f n t)
      ((t : ℂ) ^ (s - 1) * zetaKernel₁ t) :=
    (ae_restrict_iff' hm).mpr (ae_of_all _ fun t ht => h_sum0 ht)
  have h_sum : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), Summable fun n : ℕ => bd n t := by
    refine (ae_restrict_iff' hm).mpr (ae_of_all _ fun t ht => ?_)
    simpa only [fun n => h_norm n ht] using summable_norm_iff.mpr (h_sum0 ht).summable
  have h_int : Integrable (fun t : ℝ => ∑' n : ℕ, bd n t) (volume.restrict (Ioi 0)) := by
    refine IntegrableOn.congr_fun
        (mellinConvergent_of_isBigO_rpow_exp pi_pos locally_integrable_zetaKernel₁
            isBigO_atTop_zetaKernel₁ isBigO_zero_zetaKernel₁ hs).norm (fun t ht => ?_) hm
    rw [tsum_mul_left, norm_smul, Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos ht, sub_re,
      one_re, zetaKernel₁, ← ofReal_tsum, Complex.norm_eq_abs, Complex.abs_of_nonneg]
    exact tsum_nonneg fun n => (exp_pos _).le
  rw [← tsum_mul_left]
  simp_rw [← integral_cpow_mul_exp_neg_pi_mul_sq (one_half_pos.trans hs)]
  rw [← (hasSum_integral_of_dominated_convergence bd hf_meas h_le h_sum h_int h_sum').tsum_eq.symm]
  rfl
#align mellin_zeta_kernel₁_eq_tsum mellin_zetaKernel₁_eq_tsum

theorem completed_zeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    riemannCompletedZeta s =
      (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s := by
  rw [completed_zeta_eq_mellin_of_one_lt_re hs, mellin_zetaKernel₁_eq_tsum, neg_div,
    mul_div_cancel' _ (two_ne_zero' ℂ)]
  rw [show s / 2 = ↑(2⁻¹ : ℝ) * s by push_cast; rw [mul_comm]; rfl]
  rwa [ofReal_mul_re, ← div_eq_inv_mul, div_lt_div_right (zero_lt_two' ℝ)]
#align completed_zeta_eq_tsum_of_one_lt_re completed_zeta_eq_tsum_of_one_lt_re

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s := by
  have : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]; exact zero_le_one
  rw [riemannZeta, Function.update_noteq this, completed_zeta_eq_tsum_of_one_lt_re hs, ← mul_assoc,
    neg_div, cpow_neg, mul_inv_cancel_left₀, mul_div_cancel_left]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_eq_mul_inv, mul_comm, show (2⁻¹ : ℂ) = (2⁻¹ : ℝ) by norm_num, ofReal_mul_re]
    exact mul_pos (inv_pos_of_pos two_pos) (zero_lt_one.trans hs)
  · rw [Ne.def, cpow_eq_zero_iff, not_and_or, ← Ne.def, ofReal_ne_zero]
    exact Or.inl pi_pos.ne'
#align zeta_eq_tsum_one_div_nat_add_one_cpow zeta_eq_tsum_one_div_nat_add_one_cpow

/-- Alternate formulation of `zeta_eq_tsum_one_div_nat_add_one_cpow` without the `+ 1`, using the
fact that for `s ≠ 0` we define `0 ^ s = 0`.  -/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have hs' : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]; exact zero_le_one
  rw [tsum_eq_zero_add]
  · simp_rw [Nat.cast_zero, zero_cpow hs', div_zero, zero_add,
      zeta_eq_tsum_one_div_nat_add_one_cpow hs, Nat.cast_add, Nat.cast_one]
  · rw [← summable_norm_iff]
    simp_rw [norm_div, norm_one, Complex.norm_eq_abs, ← ofReal_nat_cast,
      abs_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _) (zero_lt_one.trans hs).ne',
      summable_one_div_nat_rpow]
    assumption
#align zeta_eq_tsum_one_div_nat_cpow zeta_eq_tsum_one_div_nat_cpow

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_nat_cast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_nat_cast]
#align zeta_nat_eq_tsum_of_gt_one zeta_nat_eq_tsum_of_gt_one

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`: we have
`ζ (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)!`.
Compare `hasSum_zeta_nat` for a version formulated explicitly as a sum, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent to the above via
the functional equation). -/
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  convert congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one]
    · rw [ofReal_tsum]
      norm_num
    · refine one_lt_two.trans_le ?_
      conv_lhs => rw [← mul_one 2]
      rwa [mul_le_mul_left (zero_lt_two' ℕ), Nat.one_le_iff_ne_zero]
  · norm_num
#align riemann_zeta_two_mul_nat riemannZeta_two_mul_nat

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two, ofReal_tsum]
    norm_num
  · norm_num
#align riemann_zeta_two riemannZeta_two

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : ℂ) = (4 : ℕ) by norm_num,
      zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < 4), ofReal_tsum]
    norm_num
  · norm_num
#align riemann_zeta_four riemannZeta_four

/-!
## Functional equation
-/


/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
theorem riemannCompletedZeta₀_one_sub (s : ℂ) :
    riemannCompletedZeta₀ (1 - s) = riemannCompletedZeta₀ s := by
  have := mellin_comp_rpow zetaKernel₂ (s / 2 - 1 / 2) neg_one_lt_zero.ne
  simp_rw [rpow_neg_one, ← one_div, abs_neg, abs_one, div_one, one_smul, ofReal_neg, ofReal_one,
    div_neg, div_one, neg_sub] at this
  conv_lhs => rw [riemannCompletedZeta₀, sub_div, ← this]
  refine set_integral_congr measurableSet_Ioi fun t ht => ?_
  simp_rw [zetaKernel₂_one_div ht, smul_eq_mul, ← mul_assoc, sqrt_eq_rpow,
    ofReal_cpow (le_of_lt ht), ← cpow_add _ _ (ofReal_ne_zero.mpr <| ne_of_gt ht)]
  congr 2
  push_cast
  ring
#align riemann_completed_zeta₀_one_sub riemannCompletedZeta₀_one_sub

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
theorem riemannCompletedZeta_one_sub (s : ℂ) :
    riemannCompletedZeta (1 - s) = riemannCompletedZeta s := by
  simp_rw [riemannCompletedZeta, riemannCompletedZeta₀_one_sub, sub_add, (by abel : 1 - s - 1 = -s),
    (by abel : 1 - s = -(s - 1)), div_neg, neg_sub_neg]
#align riemann_completed_zeta_one_sub riemannCompletedZeta_one_sub

/-- Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we have
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`. -/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) =
      (2 : ℂ) ^ (1 - s) * (π : ℂ) ^ (-s) * Gamma s * sin (π * (1 - s) / 2) * riemannZeta s := by
  -- Deducing this from the previous formulations is quite involved. The proof uses two
  -- nontrivial facts (the doubling formula and reflection formula for Gamma) and a lot of careful
  -- rearrangement, requiring several non-vanishing statements as input to `field_simp`.
  have hs_ne : s ≠ 0 := by contrapose! hs; rw [hs]; exact ⟨0, by rw [Nat.cast_zero, neg_zero]⟩
  have h_sqrt : (sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sqrt_ne_zero'.mpr pi_pos)
  have h_pow : (2 : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne.def, cpow_eq_zero_iff, not_and_or]
    exact Or.inl two_ne_zero
  have h_Ga_ne1 : Gamma (s / 2) ≠ 0 := by
    rw [Ne.def, Complex.Gamma_eq_zero_iff]
    contrapose! hs
    obtain ⟨m, hm⟩ := hs
    rw [div_eq_iff (two_ne_zero' ℂ), ← Nat.cast_two, neg_mul, ← Nat.cast_mul] at hm
    exact ⟨m * 2, by rw [hm]⟩
  have h_Ga_eq : Gamma s = Gamma (s / 2) * Gamma ((s + 1) / 2) * (2 : ℂ) ^ (s - 1) / sqrt π := by
    rw [add_div, Complex.Gamma_mul_Gamma_add_half, mul_div_cancel' _ (two_ne_zero' ℂ),
      (by ring : 1 - s = -(s - 1)), cpow_neg, ← div_eq_mul_inv, eq_div_iff h_sqrt,
      div_mul_eq_mul_div₀, div_mul_cancel _ h_pow]
  have h_Ga_ne3 : Gamma ((s + 1) / 2) ≠ 0 := by
    have h_Ga_aux : Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    contrapose! h_Ga_aux
    rw [h_Ga_eq, h_Ga_aux, mul_zero, zero_mul, zero_div]
  rw [riemannZeta, Function.update_noteq (by rwa [sub_ne_zero, ne_comm] : 1 - s ≠ 0),
    Function.update_noteq hs_ne, riemannCompletedZeta_one_sub, mul_div, eq_div_iff h_Ga_ne1,
    mul_comm, ← mul_div_assoc]
  -- Now rule out case of s = positive odd integer & deduce further non-vanishing statements
  by_cases hs_pos_odd : ∃ n : ℕ, s = 1 + 2 * n
  · -- Note the case n = 0 (i.e. s = 1) works OK here, but only because we have used
    -- `Function.update_noteq` to change the goal; the original goal is genuinely false for s = 1.
    obtain ⟨n, rfl⟩ := hs_pos_odd
    have : (1 - (1 + 2 * (n : ℂ))) / 2 = -↑n := by
      rw [← sub_sub, sub_self, zero_sub, neg_div, mul_div_cancel_left _ (two_ne_zero' ℂ)]
    rw [this, Complex.Gamma_neg_nat_eq_zero, div_zero]
    have : (π : ℂ) * (1 - (1 + 2 * ↑n)) / 2 = ↑(-n : ℤ) * π := by push_cast; field_simp; ring
    rw [this, Complex.sin_int_mul_pi, mul_zero, zero_mul]
  have h_Ga_ne4 : Gamma ((1 - s) / 2) ≠ 0 := by
    rw [Ne.def, Complex.Gamma_eq_zero_iff]
    contrapose! hs_pos_odd
    obtain ⟨m, hm⟩ := hs_pos_odd
    rw [div_eq_iff (two_ne_zero' ℂ), sub_eq_iff_eq_add, neg_mul, ← sub_eq_neg_add,
      eq_sub_iff_add_eq] at hm
    exact ⟨m, by rw [← hm, mul_comm]⟩
  -- At last the main proof
  rw [show sin (↑π * (1 - s) / 2) = π * (Gamma ((1 - s) / 2) * Gamma (s / 2 + 1 / 2))⁻¹ by
      have := congr_arg Inv.inv (Complex.Gamma_mul_Gamma_one_sub ((1 - s) / 2)).symm
      rwa [(by ring : 1 - (1 - s) / 2 = s / 2 + 1 / 2), inv_div,
        div_eq_iff (ofReal_ne_zero.mpr pi_pos.ne'), mul_comm _ (π : ℂ), mul_div_assoc'] at this]
  rw [(by rw [← neg_sub] : (2 : ℂ) ^ (1 - s) = (2 : ℂ) ^ (-(s - 1))), cpow_neg, h_Ga_eq]
  suffices (π : ℂ) ^ ((1 - s) / 2) = (π : ℂ) ^ (-s) * sqrt π * (π : ℂ) ^ (s / 2) by
    rw [this]; field_simp;
    ring_nf; rw [← ofReal_pow, sq_sqrt pi_pos.le]; ring
  simp_rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ← cpow_add _ _ (ofReal_ne_zero.mpr pi_pos.ne')]
  congr 1
  push_cast
  field_simp
  ring
#align riemann_zeta_one_sub riemannZeta_one_sub

theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · cases' m with m m
    ·-- k = 0 : evaluate explicitly
      rw [Nat.zero_eq, mul_zero, Nat.cast_zero, pow_zero, one_mul, zero_add, neg_zero, zero_add,
        div_one, bernoulli_one, riemannZeta_zero]
      norm_num
    · -- k = 2 * (m + 1) : both sides "trivially" zero
      rw [Nat.cast_mul, ← neg_mul, Nat.cast_two, Nat.cast_succ, riemannZeta_neg_two_mul_nat_add_one,
        bernoulli_eq_bernoulli'_of_ne_one]
      swap; · apply ne_of_gt; norm_num
      rw [bernoulli'_odd_eq_zero ⟨m + 1, rfl⟩ (by norm_num), Rat.cast_zero, mul_zero,
        zero_div]
  · -- k = 2 * m + 1 : the interesting case
    rw [Odd.neg_one_pow ⟨m, rfl⟩]
    rw [show -(↑(2 * m + 1) : ℂ) = 1 - (2 * m + 2) by push_cast; ring]
    rw [riemannZeta_one_sub]
    rotate_left
    · intro n
      rw [(by norm_cast : 2 * (m : ℂ) + 2 = ↑(2 * m + 2)), ← Int.cast_neg_natCast, ← Int.cast_ofNat,
        Ne.def, Int.cast_inj]
      apply ne_of_gt
      exact lt_of_le_of_lt (by norm_num : (-n : ℤ) ≤ 0) (by positivity)
    · rw [(by norm_cast : 2 * (m : ℂ) + 2 = ↑(2 * m + 2)), Ne.def, Nat.cast_eq_one]; norm_num
    -- get rid of sine term
    rw [show Complex.sin (↑π * (1 - (2 * ↑m + 2)) / 2) = -(-1 : ℂ) ^ m by
        rw [(by field_simp; ring : (π : ℂ) * (1 - (2 * ↑m + 2)) / 2 = π / 2 - (π * m + π))]
        rw [Complex.sin_pi_div_two_sub, Complex.cos_add_pi, neg_inj]
        rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
        · rw [pow_mul, neg_one_sq, one_pow]
          convert Complex.cos_nat_mul_two_pi t using 2
          push_cast; ring_nf
        · rw [pow_add, pow_one, pow_mul, neg_one_sq, one_pow, one_mul]
          convert Complex.cos_nat_mul_two_pi_add_pi t using 2
          push_cast; ring_nf]
    -- substitute in what we know about zeta values at positive integers
    have step1 := congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat (by norm_num : m + 1 ≠ 0)).tsum_eq
    have step2 := zeta_nat_eq_tsum_of_gt_one (by rw [mul_add]; norm_num : 1 < 2 * (m + 1))
    simp_rw [ofReal_tsum, ofReal_div, ofReal_one, ofReal_pow, ofReal_nat_cast] at step1
    rw [step1, (by norm_cast : (↑(2 * (m + 1)) : ℂ) = 2 * ↑m + 2)] at step2
    rw [step2, mul_div]
    -- now the rest is just a lengthy but elementary rearrangement
    rw [show ((2 * (m + 1))! : ℂ) = Complex.Gamma (2 * m + 2) * (↑(2 * m + 1) + 1) by
        rw [(by push_cast; ring : (2 * m + 2 : ℂ) = ↑(2 * m + 1) + 1),
          Complex.Gamma_nat_eq_factorial, (by ring : 2 * (m + 1) = 2 * m + 1 + 1),
          Nat.factorial_succ, Nat.cast_mul, mul_comm]
        norm_num]
    rw [← div_div, neg_one_mul]
    congr 1
    rw [div_eq_iff (Gamma_ne_zero_of_re_pos _)]
    swap; · rw [(by norm_num : 2 * (m : ℂ) + 2 = ↑(2 * (m : ℝ) + 2)), ofReal_re]; positivity
    simp_rw [ofReal_mul, ← mul_assoc, ofReal_rat_cast, mul_add, Nat.add_assoc, mul_one,
      one_add_one_eq_two, mul_neg, neg_mul, neg_inj]
    conv_rhs => rw [mul_comm]
    congr 1
    rw [ofReal_pow, ofReal_neg, ofReal_one, pow_add, neg_one_sq, mul_one]
    conv_lhs =>
      congr
      congr
      rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [show (2 : ℂ) ^ (1 - (2 * (m : ℂ) + 2)) = (↑((2 : ℝ) ^ (2 * m + 2 - 1)))⁻¹ by
        rw [ofReal_pow, ← cpow_nat_cast, ← cpow_neg, show (2 : ℝ) = (2 : ℂ) by norm_num]
        congr 1
        rw [Nat.add_sub_assoc one_le_two, Nat.cast_add, Nat.cast_mul, Nat.cast_two,
          (by norm_num : 2 - 1 = 1)]
        push_cast; ring]
    rw [show (π : ℂ) ^ (-(2 * (m : ℂ) + 2)) = (↑(π ^ (2 * m + 2)))⁻¹ by
        rw [ofReal_pow, ← cpow_nat_cast, ← cpow_neg, Nat.cast_add, Nat.cast_mul, Nat.cast_two]]
    rw [(by intros; ring : ∀ a b c d e : ℂ, a * b * c * d * e = a * d * (b * e) * c)]
    rw [inv_mul_cancel (ofReal_ne_zero.mpr <| pow_ne_zero _ pi_pos.ne'),
      inv_mul_cancel (ofReal_ne_zero.mpr <| pow_ne_zero _ two_ne_zero), one_mul, one_mul]
#align riemann_zeta_neg_nat_eq_bernoulli riemannZeta_neg_nat_eq_bernoulli
