/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Bounds for cusp forms
-/

open UpperHalfPlane Filter Topology
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

/-- A function `ℍ → ℝ` which is invariant under `SL(2, ℤ)`, and bounded at `∞`, is bounded. -/
lemma exists_bound_of_invariant {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} (hf_cont : Continuous f) (hf_infinity : IsBoundedAtImInfty f)
    (hf_inv : ∀ (g : SL(2, ℤ)) τ, f (g • τ) = f τ) : ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  obtain ⟨D, y, hDy⟩ := isBoundedAtImInfty_iff.mp hf_infinity
  obtain ⟨E, hE⟩ : ∃ E, ∀ x ∈ truncatedFundamentalDomain y, ‖f x‖ ≤ E :=
    (isCompact_truncatedFundamentalDomain y).exists_bound_of_continuousOn hf_cont.continuousOn
  refine ⟨max D E, fun τ ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
  rw [← hf_inv g τ]
  by_cases h : (g • τ).im ≤ y
  · exact (hE _ ⟨hg, h⟩).trans <| le_max_right _ _
  · exact (hDy _ (le_of_not_ge h)).trans <| le_max_left _ _

/-- A function `ℍ → ℝ` which is invariant under a finite-index subgroup of `SL(2, ℤ)`, and bounded
at all cusps, is bounded. -/
lemma exists_bound_of_subgroup_invariant {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} (hf_cont : Continuous f)
    (hf_infinity : ∀ (g : SL(2, ℤ)), IsBoundedAtImInfty fun τ ↦ f (g • τ))
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  -- marshall the info we have in terms of a function on the quotient
  let f' (τ) : SL(2, ℤ) ⧸ Γ → E := Quotient.lift (fun g ↦ f (g⁻¹ • τ)) fun g h hgh ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hgh
      exact ⟨g⁻¹ * h, hgh, (mul_inv_cancel_left g h).symm⟩
    simp only [hj', mul_inv_rev, mul_smul, hf_inv j⁻¹ (inv_mem hj)]
  have hf'_cont (γ) : Continuous (f' · γ) := QuotientGroup.induction_on γ fun g ↦ by
    simp [f']
    fun_prop
  have hf'_inv (τ) (g : SL(2, ℤ)) (γ) : f' (g • τ) (g • γ) = f' τ γ := by
    induction γ using QuotientGroup.induction_on
    simp [-sl_moeb, f', mul_smul]
  have hf'_infty (γ) : IsBoundedAtImInfty (f' · γ) := γ.induction_on fun h ↦ hf_infinity h⁻¹
  -- now take the sum over the quotient
  have : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  -- Now the conclusion is very simple.
  obtain ⟨C, hC⟩ := exists_bound_of_invariant (show Continuous (∑ γ, ‖f' · γ‖) by fun_prop)
    (.sum fun i _ ↦ (hf'_infty i).norm_left)
    (fun g τ ↦ (Fintype.sum_equiv (MulAction.toPerm g) _ _ (by simp [-sl_moeb, hf'_inv])).symm)
  refine ⟨C, fun τ ↦ le_trans ?_ (hC τ)⟩
  simpa [Real.norm_of_nonneg <| show 0 ≤ ∑ γ, ‖f' τ γ‖ by positivity, -sl_moeb, f'] using
    Finset.univ.single_le_sum (fun γ _ ↦ norm_nonneg (f' τ γ)) (Finset.mem_univ ⟦1⟧)

end ModularGroup

/-- The integrand in the Petersson scalar product of two modular forms. -/
noncomputable def UpperHalfPlane.petersson (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :=
  conj (f τ) * f' τ * τ.im ^ k

lemma UpperHalfPlane.petersson_continuous (k : ℤ) {f f' : ℍ → ℂ}
    (hf : Continuous f) (hf' : Continuous f') :
    Continuous (petersson k f f') := by
  apply ((Complex.continuous_conj.comp hf).mul hf').mul
  apply (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).zpow₀
  exact fun τ ↦ .inl <| Complex.ofReal_ne_zero.mpr τ.im_ne_zero

lemma UpperHalfPlane.petersson_slash (k : ℤ) (f f' : ℍ → ℂ) (g : GL(2, ℝ)⁺) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ = (↑ₘ[ℝ] g).det ^ (k - 2) * petersson k f f' (g • τ) := by
  let D := (↑ₘ[ℝ] g).det
  have hD : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr <| Matrix.GLPos.det_ne_zero g
  let j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = conj (f (g • τ) * D ^ (k - 1) * j^(-k)) *
        (f' (g • τ) * D ^ (k - 1) * j ^ (-k)) * τ.im ^ k := rfl
  _ = D ^ (2 * k - 2) * conj (f (g • τ)) * (f' (g • τ)) * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp only [Complex.normSq_eq_conj_mul_self, (by ring : 2 * k - 2 = (k - 1) + (k - 1)),
      zpow_add₀ hD, mul_zpow, map_mul, map_zpow₀, Complex.conj_ofReal]
    ring
  _ = D ^ (k - 2) * (conj (f (g • τ)) * (f' (g • τ)) * (D * τ.im / j.normSq) ^ k) := by
    rw [div_zpow, mul_zpow, zpow_neg, div_eq_mul_inv, (by ring : 2 * k - 2 = k + (k - 2)),
      zpow_add₀ hD]
    ring
  _ = D ^ (k - 2) * (conj (f (g • τ)) * (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq, Complex.ofReal_div, Complex.ofReal_mul]

lemma UpperHalfPlane.petersson_slash_SL (k : ℤ) (f f' : ℍ → ℂ) (g : SL(2, ℤ)) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ = petersson k f f' (g • τ) := by
  simp [UpperHalfPlane.petersson_slash]

lemma UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] {f : F} (h_bd : IsZeroAtImInfty f)
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f' : F) :
    IsZeroAtImInfty (petersson k f f') := by
  unfold petersson
  simp only [IsZeroAtImInfty, ZeroAtFilter, ← Asymptotics.isLittleO_one_iff (F := ℝ),
    ← Asymptotics.isLittleO_norm_left (E' := ℂ), norm_mul, Complex.norm_conj]
  have hf' : IsBoundedAtImInfty f' := by simpa using ModularFormClass.bdd_at_infty f' 1
  simp only [mul_comm ‖f _‖ ‖f' _‖, mul_assoc, norm_zpow, Complex.norm_real,
      Real.norm_of_nonneg (fun {τ : ℍ} ↦ τ.im_pos).le]
  rw [(by simp : (1 : ℝ) = 1 * 1)]
  apply hf'.norm_left.mul_isLittleO
  obtain ⟨a, ha, haf⟩ := h_bd.exp_decay_atImInfty
  refine (haf.norm_left.mul <| Asymptotics.isBigO_refl (fun τ ↦ (im τ) ^ k) _).trans_isLittleO ?_
  rw [Asymptotics.isLittleO_one_iff]
  refine .comp (g := fun t ↦ Real.exp (-a * t) * t ^ k) ?_ tendsto_comap
  exact (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k a ha).congr fun t ↦ by norm_cast; ring

lemma UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_right
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {F : Type*}
    [FunLike F ℍ ℂ] [ModularFormClass F Γ k] {f f' : F}
    (h_bd : IsZeroAtImInfty f') : IsZeroAtImInfty (petersson k f f') := by
  have := h_bd.petersson_isZeroAtImInfty_left k Γ f
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero] at this ⊢
  refine this.congr fun τ ↦ ?_
  simp only [petersson, norm_mul, Complex.norm_conj, mul_comm]

lemma SlashInvariantFormClass.petersson_smul {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F F' : Type*}
    [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ k] {f : F}
    [FunLike F' ℍ ℂ] [SlashInvariantFormClass F' Γ k] {f' : F'}
    {g : SL(2, ℤ)} (hg : g ∈ Γ) {τ : ℍ} :
    petersson k f f' (g • τ) = petersson k f f' τ := by
  simpa [← ModularForm.SL_slash, SlashInvariantFormClass.slash_action_eq _ _ hg]
    using (petersson_slash k f f' g τ).symm

lemma ModularFormClass.petersson_continuous (k : ℤ) (Γ : Subgroup SL(2, ℤ)) {F F' : Type*}
    [FunLike F ℍ ℂ] [ModularFormClass F Γ k]
    [FunLike F' ℍ ℂ] [ModularFormClass F' Γ k] (f : F) (f' : F') :
    Continuous (petersson k f f') :=
  UpperHalfPlane.petersson_continuous k
    (ModularFormClass.holo f).continuous (ModularFormClass.holo f').continuous

/-- If `f` is a cusp form and `f'` a modular form, then `petersson k f f'` is bounded. -/
lemma CuspFormClass.petersson_bounded_left
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] :
    ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C := by
  refine ModularGroup.exists_bound_of_subgroup_invariant (Γ := Γ)
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

/-- A weight `k` cusp form is bounded in norm by `(im τ) ^ (k / 2)`. -/
lemma CuspFormClass.exists_bound {k : ℤ} {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    ∃ C, ∀ τ, ‖f τ‖ * τ.im ^ (k / 2 : ℝ) ≤ C := by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ ↦ ?_⟩
  specialize hC τ
  rw [← Real.sqrt_le_sqrt_iff ((norm_nonneg _).trans hC)] at hC
  refine (le_of_eq ?_).trans hC
  simp only [petersson, norm_mul, Complex.norm_conj]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity), norm_zpow,
    Complex.norm_real, Real.sqrt_eq_rpow, ← Real.rpow_intCast_mul (by positivity), mul_one_div,
    Real.norm_of_nonneg τ.im_pos.le]
