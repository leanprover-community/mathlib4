/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Bounds for the norm of a modular form

We prove bounds for the norm of a modular form `f τ` in terms of `im τ`. The main results are

* `ModularFormClass.exists_bound`: a modular form of weight `k` (for a finite-index subgroup `Γ`)
  is bounded by a constant multiple of `max 1 (1 / (im τ) ^ k))`.
* `CuspFormClass.exists_bound`: a cusp form of weight `k` (for a finite-index subgroup `Γ`)
  is bounded by a constant multiple of `1 / (im τ) ^ (k / 2)`.

-/

open Filter Topology Asymptotics

open UpperHalfPlane hiding I

open scoped Modular MatrixGroups ComplexConjugate ModularForm

namespace ModularGroup

/-- The standard fundamental domain truncated at height `y`. -/
def truncatedFundamentalDomain (y : ℝ) : Set ℍ := { τ | τ ∈ 𝒟 ∧ τ.im ≤ y }

/-- Explicit description of the truncated fundamental domain as a subset of `ℂ`, given by
obviously closed conditions. -/
lemma coe_truncatedFundamentalDomain (y : ℝ) :
    Subtype.val '' truncatedFundamentalDomain y =
    {z | 0 ≤ z.im ∧ z.im ≤ y ∧ |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖} := by
  ext z
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz.le, h.2, h.1.2, by simpa [Complex.normSq_eq_norm_sq] using h.1.1⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have hz' : 0 < z.im := by
      apply hz.lt_of_ne
      contrapose! h3
      simpa [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq,
        ← h3, ← sq] using h2.trans_lt (by norm_num)
    exact ⟨⟨z, hz'⟩, ⟨⟨by simpa [Complex.normSq_eq_norm_sq], h2⟩, h1⟩, rfl⟩

/-- For any `y : ℝ`, the standard fundamental domain truncated at height `y` is compact. -/
lemma isCompact_truncatedFundamentalDomain (y : ℝ) :
    IsCompact (truncatedFundamentalDomain y) := by
  rw [Subtype.isCompact_iff, coe_truncatedFundamentalDomain, Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- show closed
    apply (isClosed_le continuous_const Complex.continuous_im).inter
    apply (isClosed_le Complex.continuous_im continuous_const).inter
    apply (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    exact isClosed_le continuous_const continuous_norm
  · -- show bounded
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨√((1 / 2) ^ 2 + y ^ 2), fun z hz ↦ ?_⟩
    simp only [mem_closedBall_zero_iff]
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [Real.sq_sqrt (by positivity), Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
    apply add_le_add
    · rw [sq_le_sq, abs_of_pos <| one_half_pos (α := ℝ)]
      exact hz.2.2.1
    · rw [sq_le_sq₀ hz.1 (hz.1.trans hz.2.1)]
      exact hz.2.1

lemma exists_bound_fundamental_domain_of_isBigO {E : Type*} [inst : SeminormedAddCommGroup E]
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
`t = 0` if `f` is cuspidal, and `t = k/2` otherwise. -/
lemma exists_bound_of_invariant_of_isBigO {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
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
  refine hF𝒟.trans ?_
  have hF : 0 ≤ F := by
    rw [← div_le_iff₀ (by positivity)] at hF𝒟
    refine le_trans ?_ hF𝒟
    positivity
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (g • τ).im_pos.le ?_ ht) hF
  -- It remains to show `(g • τ).im ≤ max τ.im (1 / τ.im)`.
  -- We split into two cases depending whether `c = g 1 0` is zero.
  rw [im_smul_eq_div_normSq, denom_apply]
  by_cases hg : g 1 0 = 0
  · -- If `c = 0`, then `(g • τ).im = τ.im / d ^ 2` and `d ^ 2 ≥ 1`.
    -- (In fact `d = ±1`, but we do not need this stronger statement).
    have : g 1 1 ≠ 0 := fun hg' ↦ zero_ne_one <| by
      simpa only [Matrix.det_fin_two, hg, hg', mul_zero, mul_zero, sub_zero] using g.det_coe
    have : 1 ≤ g 1 1 ^ 2 := (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs this)
    refine le_trans ?_ <| le_max_left _ _
    rw [hg, Int.cast_zero, zero_mul, zero_add, ← Complex.ofReal_intCast, Complex.normSq_ofReal]
    refine div_le_of_le_mul₀ (mul_self_nonneg _) τ.im_pos.le ?_
    apply le_mul_of_one_le_right τ.im_pos.le (by
      rwa [← sq, ← Int.cast_pow, ← Int.cast_one, Int.cast_le])
  · -- If `c ≠ 0`, then `1 ≤ c ^ 2`, so
    -- `(g • τ).im = τ.im / (c ^ 2 * τ.im ^ 2 +  ...) ≤ 1 / τ.im`.
    refine le_trans ?_ <| le_max_right _ _
    rw [div_le_div_iff₀ (by exact normSq_denom_pos g τ.im_ne_zero) τ.im_pos, one_mul,
      Complex.normSq_apply]
    apply le_add_of_nonneg_of_le (mul_self_nonneg _)
    simp only [← sq, Complex.add_im, ← Complex.ofReal_intCast, Complex.ofReal_im,
      add_zero, Complex.mul_im, zero_mul, Complex.ofReal_re, mul_pow,
      UpperHalfPlane.coe_im]
    apply le_mul_of_one_le_left (sq_nonneg _)
    rw [one_le_sq_iff_one_le_abs]
    exact_mod_cast Int.one_le_abs hg

/-- A function on `ℍ` which is invariant under a finite-index subgroup of `SL(2, ℤ)`, and satisfies
an `O((im τ) ^ t)` bound at all cusps for some `0 ≤ t`, is in fact uniformly bounded by a multiple
of `(max (im τ) (1 / im τ)) ^ t`. -/
lemma exists_bound_of_subgroup_invariant_of_isBigO {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hf_infinity : ∀ (g : SL(2, ℤ)), (fun τ ↦ f (g • τ)) =O[atImInfty] fun z ↦ (im z) ^ t)
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * max τ.im (1 / τ.im) ^ t := by
  -- marshall the info we have in terms of a function on the quotient
  let f' (τ) : SL(2, ℤ) ⧸ Γ → E := Quotient.lift (fun g ↦ f (g⁻¹ • τ)) fun g h hgh ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hgh
      exact ⟨g⁻¹ * h, hgh, (mul_inv_cancel_left g h).symm⟩
    simp [-sl_moeb, hj', mul_smul, hf_inv j⁻¹ (inv_mem hj)]
  have hf'_cont (γ) : Continuous (f' · γ) := QuotientGroup.induction_on γ fun g ↦ by
    simp [f']
    fun_prop
  have hf'_inv (τ) (g : SL(2, ℤ)) (γ) : f' (g • τ) (g • γ) = f' τ γ := by
    induction γ using QuotientGroup.induction_on
    simp [-sl_moeb, f', mul_smul]
  have hf'_infty (γ) : (f' · γ) =O[_] _ := γ.induction_on fun h ↦ hf_infinity h⁻¹
  -- now take the sum over the quotient
  have : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  -- Now the conclusion is very simple.
  obtain ⟨C, hC⟩ := exists_bound_of_invariant_of_isBigO (by fun_prop) ht
    (.sum fun i _ ↦ (hf'_infty i).norm_left)
    (fun g τ ↦ (Fintype.sum_equiv (MulAction.toPerm g) _ _ (by simp [-sl_moeb, hf'_inv])).symm)
  refine ⟨C, fun τ ↦ le_trans ?_ (hC τ)⟩
  simpa [Real.norm_of_nonneg <| show 0 ≤ ∑ γ, ‖f' τ γ‖ by positivity, -sl_moeb, f'] using
    Finset.univ.single_le_sum (fun γ _ ↦ norm_nonneg (f' τ γ)) (Finset.mem_univ ⟦1⟧)

/-- A function on `ℍ` which is invariant under `SL(2, ℤ)`, and bounded at `∞`, is bounded. -/
lemma exists_bound_of_invariant {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} (hf_cont : Continuous f) (hf_infinity : IsBoundedAtImInfty f)
    (hf_inv : ∀ (g : SL(2, ℤ)) τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  simpa using exists_bound_of_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using hf_infinity) hf_inv

/-- A function on `ℍ` which is invariant under a finite-index subgroup of `SL(2, ℤ)`, and bounded
at all cusps, is bounded. -/
lemma exists_bound_of_subgroup_invariant {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} (hf_cont : Continuous f)
    (hf_infinity : ∀ (g : SL(2, ℤ)), IsBoundedAtImInfty fun τ ↦ f (g • τ))
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  simpa using exists_bound_of_subgroup_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using hf_infinity) hf_inv

end ModularGroup

/-- If `f, f'` are modular forms, then `petersson k f f'` is bounded by a constant multiple of
`max τ.im (1 / τ.im) ^ k`. -/
lemma ModularFormClass.exists_petersson_le
    {k : ℤ} (hk : 0 ≤ k) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C * max τ.im (1 / τ.im) ^ k := by
  have := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO
      (ModularFormClass.petersson_continuous k Γ f f') (mod_cast hk : 0 ≤ (k : ℝ))
      (fun g ↦ ?_) (fun g hg τ ↦ SlashInvariantFormClass.petersson_smul hg)
  · simpa using this
  · simp_rw [← UpperHalfPlane.petersson_slash_SL, Real.rpow_intCast]
    have hft := bdd_at_infty f g
    have hf't := bdd_at_infty f' g
    apply IsBigO.of_norm_left
    simpa [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le] using (hft.norm_left.mul hf't.norm_left).mul
      (isBigO_refl (fun τ ↦ τ.im ^ k) atImInfty)

/-- If `f` is a cusp form and `f'` a modular form, then `petersson k f f'` is bounded. -/
lemma CuspFormClass.petersson_bounded_left
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  refine ModularGroup.exists_bound_of_subgroup_invariant
    (ModularFormClass.petersson_continuous k Γ f f') (fun g ↦ ?_)
    fun g hg τ ↦ SlashInvariantFormClass.petersson_smul hg
  apply IsZeroAtImInfty.isBoundedAtImInfty
  simp_rw [← UpperHalfPlane.petersson_slash_SL]
  let Γ' : Subgroup SL(2, ℤ) := Subgroup.map (MulAut.conj g⁻¹) Γ
  let ft₀ : CuspForm Γ' k := CuspForm.translate f g
  have : Γ'.FiniteIndex := by
    constructor
    rw [Γ.index_map_of_bijective (EquivLike.bijective _)]
    apply Subgroup.FiniteIndex.index_ne_zero
  convert UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left k Γ'
    (by simpa using CuspFormClass.zero_at_infty ft₀ 1)
    (ModularForm.translate f' g) -- "exact" fails here -- why?

/-- If `f` is a modular form and `f'` a cusp form, then `petersson k f f'` is bounded. -/
lemma CuspFormClass.petersson_bounded_right
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [CuspFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  simpa [petersson, mul_comm] using petersson_bounded_left k Γ f' f

/-- A weight `k` cusp form is bounded in norm by a constant multiple of `(im τ) ^ (-k / 2)`. -/
lemma CuspFormClass.exists_bound {k : ℤ} {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C / τ.im ^ (k / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  specialize hC τ
  rw [← Real.sqrt_le_sqrt_iff ((norm_nonneg _).trans hC)] at hC
  rw [le_div_iff₀ (by positivity)]
  refine (le_of_eq ?_).trans hC
  simp only [petersson, norm_mul, Complex.norm_conj]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity), norm_zpow,
    Complex.norm_real, Real.sqrt_eq_rpow, ← Real.rpow_intCast_mul (by positivity), mul_one_div,
    Real.norm_of_nonneg τ.im_pos.le]

open Real in
/-- A weight `k` modular form is bounded in norm by a constant multiple of
`max 1 (1 / (τ.im) ^ k)`. -/
lemma ModularFormClass.exists_bound {k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C * (max 1 (1 / (τ.im) ^ k)) := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_petersson_le hk Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  specialize hC τ
  have hC' : 0 ≤ C := le_trans (by positivity) <| (div_le_iff₀ (by positivity)).mpr hC
  rw [← sqrt_le_sqrt_iff ((norm_nonneg _).trans hC), petersson, norm_mul, sqrt_mul (norm_nonneg _),
    norm_mul, Complex.norm_conj, sqrt_mul_self (norm_nonneg _), norm_zpow, Complex.norm_real,
    norm_of_nonneg τ.im_pos.le, ← rpow_intCast, sqrt_eq_rpow, ← rpow_mul τ.im_pos.le, mul_one_div,
    sqrt_mul hC', ← le_div_iff₀ (by positivity)] at hC
  refine hC.trans (le_of_eq ?_)
  -- Now just a slightly tedious manipulation of `rpow`'s to finish
  rw [mul_div_assoc]
  congr 1
  have aux : 1 / τ.im ^ k * τ.im ^ (k / 2 : ℝ) = (1 / τ.im) ^ (k / 2 : ℝ) := by
    rw [one_div_mul_eq_div, div_rpow zero_le_one τ.im_pos.le, one_rpow,
      div_eq_div_iff (zpow_ne_zero _ τ.im_ne_zero) (by positivity), one_mul, ← rpow_add τ.im_pos,
      add_halves, rpow_intCast]
  rw [div_eq_iff (by positivity), max_mul_of_nonneg _ _ (by positivity), one_mul,
    sqrt_eq_rpow, ← rpow_intCast, ← rpow_mul (by positivity), mul_one_div, aux]
  exact MonotoneOn.map_max (fun _ ha _ _ h ↦ rpow_le_rpow ha h (by positivity)) τ.im_pos.le
    (show 0 ≤ 1 / τ.im by positivity)

local notation "𝕢" => Function.Periodic.qParam

open Complex in
lemma ModularFormClass.qExpansion_isBigO {k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup SL(2, ℤ)}
    [Γ.FiniteIndex] {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    (fun n ↦ (ModularFormClass.qExpansion Γ.width f).coeff ℂ n) =O[atTop] fun n ↦ (n : ℝ) ^ k := by
  let h := Γ.width
  haveI : NeZero h := ⟨Γ.width_ne_zero⟩
  have hΓ : Γ.width ∣ h := dvd_refl _
  obtain ⟨C, hC⟩ := exists_bound hk f
  rw [isBigO_iff]
  use (1 / Real.exp (-2 * Real.pi / ↑h)) * C
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [qExpansion_coeff_eq_intervalIntegral (t := 1 / n) f hΓ _ (by positivity),
    ← intervalIntegral.integral_const_mul]
  simp only [ofReal_div, ofReal_one, ofReal_natCast]
  refine intervalIntegral.norm_integral_le_integral_norm (by positivity) |>.trans ?_
  let F (x : ℝ) : ℝ := ‖1 / ↑h * (1 / 𝕢 h ((x : ℂ) + 1 / n * I) ^ n
      * f ⟨(x : ℂ) + 1 / n * Complex.I, by simp [hn]⟩)‖
  have (x : ℝ) : F x ≤ 1 / h * ((1 / Real.exp (-2 * Real.pi / ↑h))) * (C * n ^ k) := by
    simp only [F]
    rw [norm_mul, norm_mul, norm_div, norm_natCast, norm_one, norm_div, norm_one, norm_pow,
      mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul
    · rw [Function.Periodic.norm_qParam, add_im, ofReal_im, zero_add,
        mul_I_im, ← ofReal_one, ← ofReal_natCast, ← ofReal_div, ofReal_re, mul_one_div,
        div_right_comm, ← Real.exp_nat_mul, mul_div_cancel₀]
      exact_mod_cast hn.ne'
    · refine (hC _).trans (le_of_eq ?_)
      congr 1
      rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_mk_subtype, add_im, ofReal_im, zero_add,
        mul_I_im, ← ofReal_one, ← ofReal_natCast, ← ofReal_div, ofReal_re, div_zpow, one_zpow,
        one_div_one_div]
      exact max_eq_right <| one_le_zpow₀ (mod_cast hn) hk
    · exact norm_nonneg _
    · positivity
  refine (intervalIntegral.integral_mono (by positivity) ?_ ?_ this).trans (le_of_eq ?_)
  · apply Continuous.intervalIntegrable
    unfold F
    apply Continuous.norm
    apply continuous_const.mul
    apply Continuous.mul
    · unfold Function.Periodic.qParam
      simp_rw [← Complex.exp_nat_mul, one_div, ← Complex.exp_neg]
      fun_prop
    · have : Continuous f := (ModularFormClass.holo f).continuous
      apply this.comp
      rw [continuous_induced_rng]
      simp [Function.comp_def]
      fun_prop -- integrability
  · apply continuous_const.intervalIntegrable
  · rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    simp only [← mul_assoc, mul_one_div_cancel (NeZero.ne (h : ℝ)), one_mul,
      Real.norm_of_nonneg (show 0 ≤ (n : ℝ) ^ k by positivity)]
