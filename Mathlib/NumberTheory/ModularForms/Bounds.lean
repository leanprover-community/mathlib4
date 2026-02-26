/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Bounds for the norm of a modular form

We prove bounds for the norm of a modular form `f τ` in terms of `im τ`, and deduce polynomial
bounds for its q-expansion coefficients. The main results are

* `ModularFormClass.exists_bound`: a modular form of weight `k` (for an arithmetic subgroup `Γ`)
  is bounded by a constant multiple of `max 1 (1 / (im τ) ^ k))`.
* `CuspFormClass.exists_bound`: a cusp form of weight `k` (for an arithmetic subgroup `Γ`)
  is bounded by a constant multiple of `1 / (im τ) ^ (k / 2)`.
* `ModularFormClass.qExpansion_isBigO`: for a a modular form of weight `k` (for an arithmetic
  subgroup `Γ`), the `n`-th q-expansion coefficient is `O(n ^ k)`.
* `CuspFormClass.qExpansion_isBigO`: **Hecke's bound** for a a cusp form of weight `k` (for
  an arithmetic subgroup `Γ`): the `n`-th q-expansion coefficient is `O(n ^ (k / 2))`.
-/
public section

open Filter Topology Asymptotics Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

open UpperHalfPlane hiding I

open Matrix hiding mul_smul

open scoped Modular MatrixGroups ComplexConjugate ModularForm

variable {E : Type*} [AddCommGroup E] [SeminormedAddCommGroup E]

namespace ModularGroup

lemma exists_bound_fundamental_domain_of_isBigO
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (hf_infinity : f =O[atImInfty] fun z ↦ z.im ^ t) :
    ∃ F, ∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t := by
  -- Extract a bound for large `im τ` using `hf_infty`.
  obtain ⟨D, hD, hf_infinity⟩ := hf_infinity.exists_pos
  rw [IsBigOWith, atImInfty, eventually_comap, eventually_atTop] at hf_infinity
  obtain ⟨y, hy⟩ := hf_infinity
  simp only [Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le] at hy
  -- Extract a bound for the rest of `𝒟` using continuity and compactness.
  have hfm : ContinuousOn (fun τ ↦ ‖f τ‖ / (im τ) ^ t) (truncatedFundamentalDomain y) := by
    apply (hf_cont.norm.div ?_ fun τ ↦ by positivity).continuousOn
    exact continuous_im.rpow_const fun τ ↦ .inl τ.im_ne_zero
  obtain ⟨E, hE⟩ : ∃ E, ∀ τ ∈ truncatedFundamentalDomain y, ‖f τ‖ / (im τ) ^ t ≤ E := by
    simpa [norm_mul, norm_norm, Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le]
      using (isCompact_truncatedFundamentalDomain y).exists_bound_of_continuousOn hfm
  -- Put the two bounds together.
  refine ⟨max D E, fun τ hτ ↦ ?_⟩
  rcases le_total y (im τ) with hτ' | hτ'
  · exact (hy _ hτ' _ rfl).trans <| mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
  · rw [← div_le_iff₀ (by positivity)]
    exact (hE τ ⟨hτ, hτ'⟩).trans (le_max_right _ _)

/-- A function on `ℍ` which is invariant under `SL(2, ℤ)`, and is `O ((im τ) ^ t)` at `I∞` for
some `0 ≤ t`, is bounded on `ℍ` by a constant multiple of `(max (im τ) (1 / im τ)) ^ t`.

This will be applied to `f τ * (im τ) ^ (k / 2)` for `f` a modular form of weight `k`, taking
`t = 0` if `f` is cuspidal, and `t = k / 2` otherwise. -/
lemma exists_bound_of_invariant_of_isBigO {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : f =O[atImInfty] fun z ↦ (im z) ^ t)
    (hf_inv : ∀ (g : SL(2, ℤ)) τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * (max (im τ) (1 / im τ)) ^ t := by
  -- First find an `F` such that `∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t`.
  obtain ⟨F, hF𝒟⟩ : ∃ F, ∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t :=
    exists_bound_fundamental_domain_of_isBigO hf_cont hf_infinity
  refine ⟨F, fun τ ↦ ?_⟩
  -- Given `τ`, choose a `g = [a, b; c, d] ∈ SL(2, ℤ)` that translates `τ` into `𝒟`.
  obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
  specialize hF𝒟 (g • τ) hg
  rw [hf_inv g τ] at hF𝒟
  grw [hF𝒟]
  gcongr
  · rw [← div_le_iff₀ (by positivity)] at hF𝒟
    exact le_trans (by positivity) hF𝒟
  -- It remains to show `(g • τ).im ≤ max τ.im (1 / τ.im)`.
  -- We split into two cases depending whether `c = g 1 0` is zero.
  rw [im_smul_eq_div_normSq, denom_apply]
  by_cases hg : g 1 0 = 0
  · -- If `c = 0`, then `(g • τ).im = τ.im / d ^ 2` and `d ^ 2 ≥ 1`.
    -- (In fact `d = ±1`, but we do not need this stronger statement).
    have : g 1 1 ≠ 0 := fun hg' ↦ zero_ne_one <| by
      simpa only [Matrix.det_fin_two, hg, hg', mul_zero, mul_zero, sub_zero] using g.det_coe
    have : (1 : ℝ) ≤ g 1 1 ^ 2 := mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs this)
    refine le_trans ?_ <| le_max_left _ _
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) = (g 1 1) ^ 2 by simp [hg, sq]]
    simpa [field] using inv_le_one_of_one_le₀ this
  · -- If `c ≠ 0`, then `1 ≤ c ^ 2`, so
    -- `(g • τ).im = τ.im / (c ^ 2 * τ.im ^ 2 +  ...) ≤ 1 / τ.im`.
    refine le_trans ?_ <| le_max_right _ _
    rw [show 1 / τ.im = τ.im / τ.im ^ 2 by field_simp]
    gcongr
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) =
      ((g 1 0) * τ.re + (g 1 1)) ^ 2 + (g 1 0) ^ 2 * τ.im ^ 2 by simp [Complex.normSq_apply]; ring]
    have : (1 : ℝ) ≤ g 1 0 ^ 2 := mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hg)
    nlinarith

/-- A function on `ℍ` which is invariant under a finite-index subgroup of `SL(2, ℤ)`, and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bounded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`. -/
lemma exists_bound_of_subgroup_invariant_of_isBigO
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : ∀ (g : SL(2, ℤ)), (fun τ ↦ f (g • τ)) =O[atImInfty] fun z ↦ (im z) ^ t)
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * max τ.im (1 / τ.im) ^ t := by
  -- marshall the info we have in terms of a function on the quotient
  let f' τ : SL(2, ℤ) ⧸ Γ → E := Quotient.lift (fun g ↦ f (g⁻¹ • τ)) fun g h hgh ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hgh
      exact ⟨g⁻¹ * h, hgh, (mul_inv_cancel_left g h).symm⟩
    simp [-sl_moeb, hj', mul_smul, hf_inv j⁻¹ (inv_mem hj)]
  have hf'_cont γ : Continuous (f' · γ) := QuotientGroup.induction_on γ fun g ↦ by
    simp only [sl_moeb, Quotient.lift_mk, f']
    fun_prop
  have hf'_inv τ (g : SL(2, ℤ)) γ : f' (g • τ) (g • γ) = f' τ γ := by
    induction γ using QuotientGroup.induction_on
    simp [-sl_moeb, f', mul_smul]
  have hf'_infty γ : (f' · γ) =O[_] _ := γ.induction_on fun h ↦ hf_infinity h⁻¹
  -- now take the sum over the quotient
  have : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  -- Now the conclusion is very simple.
  obtain ⟨C, hC⟩ := exists_bound_of_invariant_of_isBigO (by fun_prop) ht
    (.sum fun i _ ↦ (hf'_infty i).norm_left)
    (fun g τ ↦ (Fintype.sum_equiv (MulAction.toPerm g) _ _ (by simp [-sl_moeb, hf'_inv])).symm)
  refine ⟨C, fun τ ↦ le_trans ?_ (hC τ)⟩
  simpa [Real.norm_of_nonneg <| show 0 ≤ ∑ γ, ‖f' τ γ‖ by positivity, -sl_moeb, f'] using
    Finset.univ.single_le_sum (fun γ _ ↦ norm_nonneg (f' τ γ)) (Finset.mem_univ ⟦1⟧)

/-- A function on `ℍ` which is invariant under an arithmetic subgroup of `GL(2, ℝ)`, and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bounded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`. -/
lemma exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : ∀ (g : SL(2, ℤ)), (fun τ ↦ f (g • τ)) =O[atImInfty] fun z ↦ (im z) ^ t)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * max τ.im (1 / τ.im) ^ t :=
  exists_bound_of_subgroup_invariant_of_isBigO hf_cont ht hf_infinity (Γ := Γ.comap (mapGL ℝ))
    (hf_inv ·)

/-- A function on `ℍ` which is invariant under `SL(2, ℤ)`, and bounded at `∞`, is uniformly
bounded. -/
lemma exists_bound_of_invariant
    {f : ℍ → E} (hf_cont : Continuous f) (hf_infinity : IsBoundedAtImInfty f)
    (hf_inv : ∀ (g : SL(2, ℤ)) τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  simpa using exists_bound_of_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using hf_infinity) hf_inv

/-- A function on `ℍ` which is invariant under an arithmetic subgroup and bounded at all cusps,
is uniformly bounded. -/
lemma exists_bound_of_subgroup_invariant {f : ℍ → E} (hf_cont : Continuous f)
    (hf_infinity : ∀ (g : SL(2, ℤ)), IsBoundedAtImInfty fun τ ↦ f (g • τ))
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  simpa using exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using hf_infinity) hf_inv

end ModularGroup

/-- If `f, f'` are modular forms, then `petersson k f f'` is bounded by a constant multiple of
`max τ.im (1 / τ.im) ^ k`. -/
lemma ModularFormClass.exists_petersson_le {k : ℤ} (hk : 0 ≤ k) (Γ : Subgroup (GL (Fin 2) ℝ))
    [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C * max τ.im (1 / τ.im) ^ k := by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine mod_cast ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    (show Continuous (‖petersson k f f' ·‖) by fun_prop) (mod_cast hk : 0 ≤ (k : ℝ))
    (fun g ↦ ?_) (fun g hg τ ↦ SlashInvariantFormClass.norm_petersson_smul hg)
  simp_rw [← UpperHalfPlane.petersson_slash_SL, Real.rpow_intCast]
  simpa [petersson, Real.norm_of_nonneg (_ : ℍ).im_pos.le]
    using (bdd_at_infty_slash f g).norm_left.mul (bdd_at_infty_slash f' g).norm_left
      |>.mul (isBigO_refl ..)

open ConjAct Pointwise in
/-- If `f` is a cusp form and `f'` a modular form, then `petersson k f f'` is bounded. -/
lemma CuspFormClass.petersson_bounded_left
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine ModularGroup.exists_bound_of_subgroup_invariant (by fun_prop) (fun g ↦ ?_)
    fun g hg τ ↦ SlashInvariantFormClass.norm_petersson_smul hg
  apply IsZeroAtImInfty.isBoundedAtImInfty
  rw [IsZeroAtImInfty, ZeroAtFilter, ← tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← UpperHalfPlane.petersson_slash_SL]
  have : ((toConjAct (g : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj Γ (mapGL ℚ g)⁻¹
  exact (zero_at_infty <| CuspForm.translate f g).petersson_isZeroAtImInfty_left k _
    (ModularForm.translate f' g)

/-- If `f` is a modular form and `f'` a cusp form, then `petersson k f f'` is bounded. -/
lemma CuspFormClass.petersson_bounded_right
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [CuspFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  simpa [petersson_norm_symm] using petersson_bounded_left k Γ f' f

/-- A weight `k` cusp form is bounded in norm by a constant multiple of `(im τ) ^ (-k / 2)`. -/
lemma CuspFormClass.exists_bound {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C / τ.im ^ (k / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  specialize hC τ
  rw [← sq_le_sq₀ (by positivity) (by positivity), div_pow, Real.sq_sqrt ((norm_nonneg _).trans hC)]
  grw [← hC]
  rw [petersson, ← Real.rpow_mul_natCast τ.im_pos.le]
  simp [abs_of_pos τ.im_pos, field]

set_option backward.isDefEq.respectTransparency false in
open Real in
/-- A weight `k` modular form is bounded in norm by a constant multiple of
`max 1 (1 / (τ.im) ^ k)`. -/
lemma ModularFormClass.exists_bound {k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * (max 1 (1 / (τ.im) ^ k)) := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_petersson_le hk Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  lift k to ℕ using hk
  specialize hC τ
  have hC' : 0 ≤ C := le_trans (by positivity) <| (div_le_iff₀ (by positivity)).mpr hC
  have h : 0 < ‖(τ.im : ℂ) ^ (k : ℤ)‖ := mod_cast norm_pos_iff.mpr (pow_ne_zero _ τ.im_ne_zero)
  rw [petersson, norm_mul, norm_mul, Complex.norm_conj, ← sq, ← le_div_iff₀ h, mul_div_assoc] at hC
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, sq_sqrt hC']
  refine hC.trans (congrArg (C * ·) ?_).le
  -- remains to show `(max τ.im (1 / τ.im)) ^ k / ‖τ.im ^ k‖ = (max 1 (1 / τ.im ^ k)) ^ 2`,
  -- which is easier after lifting to `NNReal`
  generalize h : τ.im = t
  have ht : 0 < t := h ▸ τ.im_pos
  lift t to NNReal using ht.le
  rw [← coe_nnnorm]
  norm_cast at ⊢ ht
  rw [(pow_left_mono k).map_max, (pow_left_mono 2).map_max, ← max_div_div_right (by positivity)]
  congr <;> simp [field, ht.ne']

local notation "𝕢" => Function.Periodic.qParam

open Complex ModularFormClass

set_option backward.isDefEq.respectTransparency false in
/-- General result on bounding q-expansion coefficients using a bound on the norm of the function.
This will get used twice over, once for cusp forms (with `e = k / 2`) and once for modular forms
(with `e = k`). -/
lemma qExpansion_coeff_isBigO_of_norm_isBigO {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) (e : ℝ)
    (hF : IsBigO (comap UpperHalfPlane.im (𝓝 0)) f (fun τ ↦ τ.im ^ (-e))) :
    (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ e := by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have : NeZero h := ⟨hh.ne'⟩
  have hΓ : h ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  obtain ⟨C, Cpos, hC⟩ := hF.exists_pos
  rw [isBigO_iff]
  rw [IsBigOWith, eventually_comap] at hC
  use (1 / Real.exp (-2 * Real.pi / ↑h)) * C
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually hC] with n hn hn'
  rw [qExpansion_coeff_eq_intervalIntegral (t := 1 / n) f hh hΓ _ (by positivity),
    ← intervalIntegral.integral_const_mul]
  simp only [ofReal_div, ofReal_one, ofReal_natCast]
  refine intervalIntegral.norm_integral_le_integral_norm (by positivity) |>.trans ?_
  let F (x : ℝ) : ℝ := ‖1 / ↑h * (1 / 𝕢 h ((x : ℂ) + 1 / n * I) ^ n
      * f ⟨(x : ℂ) + 1 / n * Complex.I, by simp [hn]⟩)‖
  have hne : ‖(n : ℝ) ^ e‖ = n ^ e := Real.norm_of_nonneg (by positivity)
  have (x : ℝ) : F x ≤ 1 / h * (1 / Real.exp (-2 * Real.pi / ↑h)) * (C * n ^ e) := by
    simp only [F, norm_mul, norm_div, norm_real, norm_one, norm_pow, mul_assoc]
    rw [Real.norm_of_nonneg hh.le, Function.Periodic.norm_qParam, ← Real.exp_nat_mul]
    gcongr
    · simp [field]
    · grw [hn' _ (by simp [← UpperHalfPlane.coe_im])]
      simp [← UpperHalfPlane.coe_im, Real.rpow_neg_eq_inv_rpow, hne]
  refine (intervalIntegral.integral_mono (by positivity) ?_ ?_ this).trans (le_of_eq ?_)
  · apply Continuous.intervalIntegrable
    fun_prop (disch := simp [Function.Periodic.qParam_ne_zero])
  · exact continuous_const.intervalIntegrable ..
  · simp [field, intervalIntegral.integral_const, hne]

/-- Bound for the coefficients of a modular form: if `f` is a weight `k` modular form for an
arithmetic subgroup, then its `q`-expansion coefficients are `O (n ^ k)`.

This is not optimal -- the optimal exponent is `k - 1 + ε` for any `0 < ε`, at least for congruence
levels -- but is much easier to prove than the optimal result.

See `CuspFormClass.qExpansion_isBigO` for a sharper bound assuming `f` is cuspidal. -/
lemma ModularFormClass.qExpansion_isBigO {k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ k := by
  simp only [← Real.rpow_intCast]
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound hk f
  simp_rw [IsBigO, ← Int.cast_neg, Real.rpow_intCast, IsBigOWith, eventually_comap]
  use C
  filter_upwards [eventually_le_nhds zero_lt_one] with _ hτ τ rfl
  refine (hC τ).trans (le_of_eq ?_)
  rw [max_eq_right, zpow_neg, Real.norm_of_nonneg (by positivity), one_div]
  exact one_le_one_div (by positivity) (zpow_le_one₀ τ.im_pos hτ hk)

/-- **Hecke's bound** for the coefficients of a cusp form: if `f` is a weight `k` modular form for
an arithmetic subgroup, then its `q`-expansion coefficients are `O (n ^ (k / 2))`.

This is not optimal -- the optimal exponent is `(k - 1) / 2 + ε` for any `0 < ε`, at least for
congruence levels -- but is much easier to prove than the optimal result. -/
lemma CuspFormClass.qExpansion_isBigO {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    (fun n ↦ (ModularFormClass.qExpansion Γ.strictWidthInfty f).coeff n)
      =O[atTop] fun n ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound f
  refine isBigO_of_le' (c := C) _ fun τ ↦ (hC τ).trans (of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg τ.im_pos.le, div_eq_mul_inv]
