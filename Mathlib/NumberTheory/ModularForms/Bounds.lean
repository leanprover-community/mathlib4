/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.GroupTheory.Complement

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
    refine (isClosed_le continuous_const Complex.continuous_im).inter ?_
    refine (isClosed_le Complex.continuous_im continuous_const).inter ?_
    refine (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter ?_
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

lemma SlashInvariantFormClass.petersson_smul {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*}
    [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ k] {f f' : F} {g : SL(2, ℤ)} (hg : g ∈ Γ) (τ : ℍ) :
    petersson k f f' (g • τ) = petersson k f f' τ := by
  simpa [← ModularForm.SL_slash, SlashInvariantFormClass.slash_action_eq _ _ hg]
    using (petersson_slash k f f' g τ).symm

lemma SlashInvariantFormClass.petersson_continuous {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*}
    [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ k] {f f' : F}
    (hf : Continuous f) (hf' : Continuous f') : Continuous (petersson k f f') := by
  apply ((Complex.continuous_conj.comp hf).mul hf').mul
  apply (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).zpow₀
  exact fun τ ↦ .inl <| Complex.ofReal_ne_zero.mpr τ.im_ne_zero

lemma CuspFormClass.exists_bound {k : ℤ} {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] {f : F} :
    ∃ C, ∀ τ, ‖f τ‖ * τ.im ^ (k / 2 : ℝ) ≤ C := by
  conv =>
    enter [1, C, τ]
    rw [← Real.norm_of_nonneg τ.im_pos.le, ← Real.norm_rpow_of_nonneg τ.im_pos.le,
      ← Complex.norm_real, ← norm_mul, ← norm_norm]
  apply ModularGroup.exists_bound_of_subgroup_invariant (Γ := Γ)
  · apply continuous_norm.comp
    apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr fun τ ↦ (ModularFormClass.holo f τ).continuousAt
    · apply Complex.continuous_ofReal.comp
      rw [continuous_iff_continuousAt]
      exact fun τ ↦ UpperHalfPlane.continuous_im.continuousAt.rpow_const (.inl τ.im_ne_zero)
  · sorry
  · intro g hg τ
    have := SlashInvariantForm.slash_action_eqn'' f hg τ
    rw [this, ModularGroup.sl_moeb, UpperHalfPlane.im_smul_eq_div_normSq,
      ModularGroup.det_coe, one_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.div_rpow (by positivity) (Complex.normSq_nonneg _),
      norm_div, mul_div, mul_div_right_comm, mul_div_right_comm, Complex.normSq_eq_norm_sq,
      ← Real.rpow_natCast, Nat.cast_two, ← Real.rpow_mul (norm_nonneg _),
      mul_div_cancel₀ _ two_ne_zero, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
      Real.rpow_intCast, norm_zpow, div_self, one_mul]
    exact zpow_ne_zero _ <| norm_ne_zero_iff.mpr <| denom_ne_zero _ _



namespace SlashInvariantFormClass
  -- by
  --   simpa [ModularForm.SL_slash, ModularForm.slash_def, ModularForm.slash] using
  --     congr_fun (slash_action_eq f g (by tauto)) τ

/-- A function on `ℍ` which is weight 0 invariant under `SL(2, ℤ)` and bounded at `∞` is in fact
bounded. -/
lemma isBounded_of_level_one {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F ⊤ 0]
    {f : F} (hf_cont : Continuous f) (hf_infinity : IsBoundedUnder LE.le atImInfty (‖f ·‖)) :
    ∃ C, ∀ τ, ‖f τ‖ ≤ C := by
  obtain ⟨D, hD⟩ := hf_infinity
  rw [eventually_map, atImInfty, eventually_comap, eventually_atTop] at hD
  obtain ⟨y, hy⟩ := hD
  let S := {τ | τ ∈ 𝒟 ∧ τ.im ≤ y}
  obtain ⟨E, hE⟩ := (ModularGroup.isCompact_truncatedFundamentalDomain
    y).exists_bound_of_continuousOn hf_cont.continuousOn
  use max D E
  intro τ
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have hg' : f (g • τ) = f τ := by
    simpa [ModularForm.SL_slash, ModularForm.slash_def, ModularForm.slash] using
      congr_fun (slash_action_eq f g (by tauto)) τ
  by_cases h : (g • τ).im ≤ y
  · rw [← hg']
    refine (hE _ ⟨hg, h⟩).trans (le_max_right _ _)
  · rw [← hg']
    exact (hy (g • τ).im (by linarith) _ rfl).trans (le_max_left _ _)

end SlashInvariantFormClass
