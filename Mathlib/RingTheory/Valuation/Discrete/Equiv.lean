/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.ValuativeRel.Quotient
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Equivalent discrete valuations. -/

namespace Valuation

open IsRankOneDiscrete MonoidWithZeroHom

variable {R Γ Γ' : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ'] {v : Valuation R Γ} {w : Valuation R Γ'}
  [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]

section IsEquiv

theorem IsEquiv.orderMonoidIso'_generator' (h : v.IsEquiv w) :
    h.orderMonoidIso' (generator' v) = generator' w := by
  simp [← valueGroup_genLTOne_eq_generator', LinearOrderedCommGroup.genLTOne_eq_of_top,
    h.orderMonoidIso'.map_genLTOne]

theorem IsUniformizer.iff' {π : R} : v.IsUniformizer π ↔ v.restrict π = generator' v := by
  rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective.eq_iff,
    IsUniformizer.iff, embedding_restrict, embedding_generator']

lemma IsEquiv.isUniformizer (h : v.IsEquiv w) {π : R} (hπ : v.IsUniformizer π) :
    w.IsUniformizer π := by
  rw [IsUniformizer.iff'] at hπ ⊢
  rw [← orderMonoidIso'_generator' h, orderMonoidIso'_eq, ← hπ, orderMonoidIso_spec]

theorem IsEquiv.isUniformizer_iff (h : v.IsEquiv w) {π : R} :
    v.IsUniformizer π ↔ w.IsUniformizer π :=
  ⟨h.isUniformizer, h.symm.isUniformizer⟩

theorem IsUniformizer.eq_one_iff_mul_isUniformizer {π : R} (hπ : v.IsUniformizer π) (y : R) :
    v y = 1 ↔ v.IsUniformizer (π * y) := by
  rw [IsUniformizer.iff, map_mul, hπ.val]
  exact ⟨fun h ↦ h ▸ mul_one _,
    fun h ↦ mul_left_cancel₀ (generator_ne_zero v) (h.trans (mul_one _).symm)⟩

theorem isEquiv_iff_isUniformizer {K Γ Γ' : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Γ'] {v : Valuation K Γ} {w : Valuation K Γ'}
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete] :
    v.IsEquiv w ↔ ∀ π : K, v.IsUniformizer π ↔ w.IsUniformizer π := by
  refine ⟨fun h _ ↦ h.isUniformizer_iff, fun h ↦ ?_⟩
  rw [isEquiv_iff_valuationSubring, ValuationSubring.eq_iff_unitGroup]
  obtain ⟨π, hπ₁⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  have hπ₂ : w.IsUniformizer (π : K) := (h _).mp hπ₁
  ext x
  simp [ValuationSubring.mem_unitGroup_iff, hπ₁.eq_one_iff_mul_isUniformizer,
    hπ₂.eq_one_iff_mul_isUniformizer, h,
    ← (isEquiv_valuation_valuationSubring _).eq_one_iff_eq_one]

end IsEquiv

section AbsoluteValue

-- TODO: generalize to `Ring K`
variable {K Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Field K] {v w : Valuation K Γ}
  [hv : IsRankOneDiscrete v] [hw : IsRankOneDiscrete w] {e : NNReal} (he : 1 < e)

/-- Absolute value corresponding to a discrete valuation. -/
@[simps!]
noncomputable def IsRankOneDiscrete.absoluteValue : AbsoluteValue K ℝ :=
  let : v.RankOne := hv.rankOne v he
  v.absoluteValue

lemma isEquiv_iff_absoluteValue_isEquiv :
    v.IsEquiv w ↔ (hv.absoluteValue he).IsEquiv (hw.absoluteValue he) := by
  let : v.RankOne := hv.rankOne v he
  let : w.RankOne := hw.rankOne w he
  simp [IsEquiv, AbsoluteValue.IsEquiv, v.norm_def, w.norm_def,
    (RankOne.strictMono v).le_iff_le, (RankOne.strictMono w).le_iff_le]

-- TODO: PR to [Mathlib.RingTheory.Valuation.Discrete.RankOne]
lemma IsRankOneDiscrete.rankOne_hom_eq :
    (hv.rankOne v he).hom =
      (WithZeroMulInt.toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
        (ofClass (valueGroup₀_equiv_withZeroMulInt v)) :=
  rfl

end AbsoluteValue

section WithZeroMulInt

open WithZero WithZeroMulInt

private theorem IsRankOneDiscrete.eq_of_isEquiv_of_mem_range' {K : Type*} [Field K]
    {v w : Valuation K ℤᵐ⁰} [hv : IsRankOneDiscrete v] [hw : IsRankOneDiscrete w]
    (h : v.IsEquiv w) (hv : WithZero.exp (-1) ∈ Set.range v)
    (hw : WithZero.exp (-1) ∈ Set.range w) : v = w := by
  have h_gen_eq : generator v = generator w := by
    rw [generator_eq_exp_neg_one_of_mem_range hv, generator_eq_exp_neg_one_of_mem_range hw]
  ext x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨π, hπ₁⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  have hπ₂ : w.IsUniformizer (π : K) := h.isUniformizer_iff.mp hπ₁
  obtain ⟨n, u, hn₁⟩ := exists_zpow_Uniformizer (by simpa using hx) (Uniformizer.mk' hπ₁)
  have h1 : v ((u : v.valuationSubring) : K) = 1 := by
    simp [isEquiv_iff_val_eq_one.mp v.isEquiv_valuation_valuationSubring]
  simp [hn₁,  hπ₁.val, hπ₂.val, h_gen_eq, h1, h.eq_one_iff_eq_one.mp h1, Uniformizer.mk']

section Ring

variable {R : Type*} [CommRing R] {v w : Valuation R ℤᵐ⁰} [hv : IsRankOneDiscrete v]
  [hw : IsRankOneDiscrete w]

theorem IsRankOneDiscrete.eq_of_isEquiv_of_mem_range {v w : Valuation R ℤᵐ⁰}
    [IsRankOneDiscrete v] [IsRankOneDiscrete w] (h : v.IsEquiv w)
    (hv : WithZero.exp (-1) ∈ Set.range v) (hw : WithZero.exp (-1) ∈ Set.range w) : v = w := by
  let vr := ValuativeRel.ofValuation v
  have : v.Compatible := Compatible.ofValuation v
  have : w.Compatible := by
    rw [compatible_iff_isEquiv]
    apply h.symm.trans
    rwa [← compatible_iff_isEquiv]
  let K := FractionRing (R ⧸ vr.supp)
  have hvK : (onQuotSuppExtend R v K).IsRankOneDiscrete := onQuotSuppExtend_isRankOneDiscrete K
  have hwK : (onQuotSuppExtend R w K).IsRankOneDiscrete := onQuotSuppExtend_isRankOneDiscrete K
  ext x
  calc v x
    _ = onQuotSuppExtend R v K (algebraMap R K x) := by
      simp [onQuotSuppExtend, IsScalarTower.algebraMap_apply R (R ⧸ vr.supp) K x, onQuotSupp_mk]
    _ = onQuotSuppExtend R w K (algebraMap R K x) := by
      rw [IsRankOneDiscrete.eq_of_isEquiv_of_mem_range' (onQuotSuppExtend_isEquiv v w K)
        (onQuotSuppExtend_mem_range K hv) (onQuotSuppExtend_mem_range K hw)]
    _ = w x := by
      simp [onQuotSuppExtend, IsScalarTower.algebraMap_apply R (R ⧸ vr.supp) K x, onQuotSupp_mk]

lemma valueGroup₀_equiv_withZeroMulInt_restrict_zpow_eq {v : Valuation R ℤᵐ⁰}
    [hv : IsRankOneDiscrete v] (hv0 : ∀ x ≠ 0, v x ≠ 0) (x : R) :
    ((hv.valueGroup₀_equiv_withZeroMulInt v) (v.restrict x)) ^ (- logEquiv hv.generator) = v x := by
  by_cases hx : x = 0
  · simp only [hx, map_zero, logEquiv_apply, zpow_neg, inv_eq_zero]
    rw [zero_zpow]
    simp [ne_eq, ← exp_inj (y := (0 : ℤ)), (IsRankOneDiscrete.generator_lt_one v).ne]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (hv.generator' : ValueGroup₀ (ofClass v))⁻¹ ^ c = v.restrict x := by
    rw [restrict_def, ValueGroup₀.restrict₀_of_ne_zero (by simp [hv0, hx])]
    simp [← coe_inv, ← coe_zpow, coe_inj,-inv_zpow', ← Subgroup.mem_zpowers_iff,
       hv.generator'_zpowers_eq_top, Subgroup.mem_top]
  have hc' : hv.generator ^ (- c) = v x := by
    simp [← v.embedding_restrict, ← hc, hv.embedding_generator']
  rw [restrict_def, ValueGroup₀.restrict₀_of_ne_zero (by simp [hv0, hx])] at hc ⊢
  simp only [← coe_inv, ← coe_zpow, coe_inj] at hc
  rw [IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply, map'_coe, MonoidHom.coe_coe]
  have hg' : Subgroup.zpowers (hv.generator' v)⁻¹ = ⊤ := by
    simp [Subgroup.zpowers_inv, IsRankOneDiscrete.generator'_zpowers_eq_top v]
  rw [← hc, mulintEquivOfZPowersEqTop_symm_apply_zpow hg' c]
  simp only [logEquiv_apply, ← hc', zpow_neg]
  nth_rw 2 [← exp_log (hv.generator_ne_zero v)]
  simp [exp, ← WithZero.coe_zpow, ← Int.ofAdd_mul, mul_comm c]

end Ring

lemma isEquiv_iff_of_withZeroMulInt {K : Type*} [Field K] {v w : Valuation K ℤᵐ⁰}
    [hv : IsRankOneDiscrete v] [hw : IsRankOneDiscrete w] :
    v.IsEquiv w ↔ ∃ (n : ℤ) (d : ℤ), 0 < n ∧ 0 < d ∧ ∀ (r : K), v r ^ d = w r ^ n := by
  let : v.RankOne := hv.rankOne v one_lt_two
  let : w.RankOne := hw.rankOne w one_lt_two
  /- Since w is nontrivial, there exists `a : K` with `w a ≠ 0` and `w a ≠ 1`. -/
  obtain ⟨a, ha0'', ha1⟩  : w.IsNontrivial := inferInstance
  have ha0 : ((hw.valueGroup₀_equiv_withZeroMulInt w) (w.restrict a)) ≠ 0 := by
    simp [w.restrict_eq_zero_iff, ha0'']
  have ha0' : ((hv.valueGroup₀_equiv_withZeroMulInt v) (v.restrict a)) ≠ 0 := by
    simpa [v.restrict_eq_zero_iff] using ha0''
  refine ⟨fun h ↦ ?_, fun ⟨n, d, hn, hd, h⟩ r s ↦ by rw [← zpow_le_zpow_iff_left₀
    zero_le zero_le hd, h r, h s, zpow_le_zpow_iff_left₀ zero_le zero_le hn]⟩
  have ha1' :  ((hv.valueGroup₀_equiv_withZeroMulInt v) (v.restrict a)) ≠ 1 := by
    rw [← map_one (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v),
      ← OrderMonoidIso.coe_mulEquiv, ← OrderMonoidIso.toMulEquiv_eq_coe,
      (hv.valueGroup₀_equiv_withZeroMulInt v).injective.ne_iff , ne_eq, restrict_eq_one_iff]
    simpa [IsEquiv.eq_one_iff_eq_one h]
  have ha1'' : ¬unzero ha0' = 1 := by
      rw [← WithZero.coe_inj]
      simp [- IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply, ha1']
  have h0' : Multiplicative.toAdd (unzero ha0') ≠ 0 := by
    simpa [valueGroup₀_equiv_withZeroMulInt_apply, ne_eq, toAdd_eq_zero]
  rw [v.isEquiv_iff_absoluteValue_isEquiv one_lt_two, AbsoluteValue.isEquiv_iff_exists_rpow_eq] at h
  /- Since the absolute values associated to `v` and `w` are equivalent, there exists `c : ℝ`
    such that `0 < c` and `|x|_v ^ c = |x|_w` for all `x : K`. -/
  obtain ⟨c, hc_pos, h_eq⟩ := h
  simp only [IsRankOneDiscrete.absoluteValue_apply, v.norm_def, IsRankOneDiscrete.rankOne_hom_eq,
    MonoidWithZeroHom.coe_comp, Function.comp_apply, funext_iff, w.norm_def] at h_eq
  /- In particular, `|a|_v ^ c = |a|_w`. Since `|a|_v` is equal to 2 raised to the negative
    of the additive valuation `a_v(a)` associated to `v` (and analogously for `w`), we can take
    log_2 on both sides and simplify to deduce that `c` is the coercion of a rational number. -/
  have hc := h_eq a -- take log_2 and deduce c is rational.
  simp only [MonoidWithZeroHom.coe_ofClass] at hc
  rw [toNNReal_neg_apply _ ha0, toNNReal_neg_apply _ ha0'] at hc
  · simp_rw [NNReal.coe_zpow, NNReal.coe_ofNat, ← Real.rpow_intCast] at hc
    rw [← Real.rpow_mul zero_le_two, Real.rpow_right_inj zero_lt_two (by linarith), mul_comm,
      ← eq_mul_inv_iff_mul_eq₀ (by simpa)] at hc
    /- We take `n` and `d` to be the absolute values of the denominator and the numerator of the
      (positive) rational number found in the previous step. -/
    -- TODO: update comment
    · refine ⟨- log hv.generator * |Multiplicative.toAdd (unzero ha0')|,
        - log hw.generator * |Multiplicative.toAdd (unzero ha0)|, ?_, ?_, ?_⟩
      · apply mul_pos _ (by simpa [abs_pos, ne_eq])
        simp only [Int.neg_pos, log_lt_iff_lt_exp (hv.generator_ne_zero v), exp_zero]
        exact hv.generator_lt_one v
      · apply mul_pos
        · simp only [Int.neg_pos, log_lt_iff_lt_exp (hw.generator_ne_zero w), exp_zero]
          exact hw.generator_lt_one w
        · rw [abs_pos, ne_eq, toAdd_eq_zero, ← WithZero.coe_inj]
          simp [- IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply,
            w.restrict_eq_one_iff, ha1]
      · have (a b c d : ℝ) : a * ((b * c) * d) = (c * d) * (b * a) := by ring
        /- We use the definitions of `c`, `n` and `d` to conclude the result. -/
        intro x
        simp only [← (toNNReal_strictMono one_lt_two).injective.eq_iff, ← NNReal.coe_inj,
          map_zpow₀, NNReal.coe_zpow, ← Real.rpow_intCast]
        rw [← Real.rpow_left_inj (z := (↑|Multiplicative.toAdd (unzero ha0')|)⁻¹)
          (by positivity) (by positivity) (by simpa),
          ← Real.rpow_mul NNReal.zero_le_coe, ← Real.rpow_mul NNReal.zero_le_coe]
        conv_rhs => rw [Int.cast_mul, mul_assoc, mul_inv_cancel₀ (by simpa), mul_one]
        rw [← NNReal.coe_rpow, ← valueGroup₀_equiv_withZeroMulInt_restrict_zpow_eq (by simp),
          ← valueGroup₀_equiv_withZeroMulInt_restrict_zpow_eq (by simp)]
        simp only [logEquiv_apply, map_zpow₀,  Int.cast_mul, Int.cast_abs, NNReal.coe_rpow,
            NNReal.coe_zpow]
        rw [← Real.rpow_intCast, ← Real.rpow_mul (NNReal.zero_le_coe),
          ← Real.rpow_intCast, ← Real.rpow_mul (NNReal.zero_le_coe), this,
          Real.rpow_mul NNReal.zero_le_coe]
        simp only [MonoidWithZeroHom.coe_ofClass, valueGroup₀_equiv_withZeroMulInt_apply] at h_eq
        simp only [valueGroup₀_equiv_withZeroMulInt_apply, ← h_eq]
        rw [← abs_eq_self.mpr (le_of_lt hc_pos)]
        simp [hc, valueGroup₀_equiv_withZeroMulInt_apply]

end WithZeroMulInt

end Valuation
