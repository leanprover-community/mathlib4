/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Valuation.ValuativeRel.Quotient

/-! # Equivalent discrete valuations.

## Main Definitions and Results

* `Valuation.isEquiv_iff_isUniformizer`: two discrete valuations are equivalent if and only if
  they have the same uniformizers.
* `Valuation.isEquiv_iff_of_withZeroMulInt `: two `ℤᵐ⁰`-valued valuations `v`
  and `w` are equivalent if and only if there exist positive integers `n` and `d` such that
  `v r ^ d = w r ^ n` for all `r` in the domain.

## Tags

valuation, discrete, equivalent

-/

@[expose] public section

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

/-- Two discrete valuations are equivalent if and only if they have the same uniformizers. -/
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

variable {K Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [DivisionRing K] {v w : Valuation K Γ}
  [hv : IsRankOneDiscrete v] [hw : IsRankOneDiscrete w] {e : NNReal} (he : 1 < e)

lemma isEquiv_iff_absoluteValue_isEquiv :
    v.IsEquiv w ↔ (hv.absoluteValue he).IsEquiv (hw.absoluteValue he) := by
  let : v.RankOne := hv.rankOne v he
  let : w.RankOne := hw.rankOne w he
  simp [IsEquiv, AbsoluteValue.IsEquiv, v.norm_def, w.norm_def,
    (RankOne.strictMono v).le_iff_le, (RankOne.strictMono w).le_iff_le]

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

end Ring

open NNReal Real in
/-- Two `ℤᵐ⁰`-valued valuations `v` and `w` are equivalent if and only if there exist positive
  integers `n` and `d` such that `v r ^ d = w r ^ n` for all `r` in the domain. -/
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
  have h0' : ((valueGroup₀_equiv_withZeroMulInt v) (v.restrict a)).log ≠ 0 := by
    rw [← toAdd_unzero_eq_log ha0']
    simpa
  /- `v` and `w` being equivalent if and only if the associated absolute values are. We use `2` as
    the basis for these absolute values, but any `e : ℝ≥0` with `1 < e` would work. -/
  rw [v.isEquiv_iff_absoluteValue_isEquiv one_lt_two, AbsoluteValue.isEquiv_iff_exists_rpow_eq] at h
  /- Since the absolute values associated to `v` and `w` are equivalent, there exists `c : ℝ`
    such that `0 < c` and `|x|_v ^ c = |x|_w` for all `x : K`. -/
  obtain ⟨c, hc_pos, h_eq⟩ := h
  simp only [IsRankOneDiscrete.absoluteValue_apply, v.norm_def, IsRankOneDiscrete.rankOne_hom_eq,
    MonoidWithZeroHom.coe_comp, Function.comp_apply, funext_iff, w.norm_def] at h_eq
  /- In particular, `|a|_v ^ c = |a|_w`. Since `|a|_v` is equal to 2 raised to the negative
    of the additive valuation `a_v(a)` associated to `v` (and analogously for `w`), we can take
    log_2 on both sides and simplify to deduce that `c` is the coercion of a rational number. -/
  have hc := h_eq a
  simp only [MulEquiv.coe_toMonoidWithZeroHom, OrderMonoidIso.coe_mulEquiv] at hc
  rw [toNNReal_neg_apply _ ha0, toNNReal_neg_apply _ ha0'] at hc
  · simp_rw [coe_zpow, NNReal.coe_ofNat, ← Real.rpow_intCast] at hc
    rw [← rpow_mul zero_le_two, rpow_right_inj zero_lt_two (by linarith), mul_comm,
      ← eq_mul_inv_iff_mul_eq₀ (by simpa)] at hc
    /- We take `n` and `d` to be the absolute values of the denominator and the numerator of the
      (positive) rational number `c` found in the previous step. -/
    set n := log ((valueGroup₀_equiv_withZeroMulInt w) (w.restrict a))
    set d := log ((valueGroup₀_equiv_withZeroMulInt v) (v.restrict a))
    · refine ⟨- log hv.generator * |d|, - log hw.generator * |n|, ?_, ?_, ?_⟩
      · apply mul_pos _ (by simpa [abs_pos, ne_eq])
        simp only [Int.neg_pos, log_lt_iff_lt_exp (hv.generator_ne_zero v)]
        exact hv.generator_lt_one v
      · apply mul_pos
        · simp only [Int.neg_pos, log_lt_iff_lt_exp (hw.generator_ne_zero w)]
          exact hw.generator_lt_one w
        · simp only [n]
          rw [abs_pos, ne_eq, ← toAdd_unzero_eq_log ha0, toAdd_eq_zero, ← WithZero.coe_inj]
          simp [- IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply,
            w.restrict_eq_one_iff, ha1]
      · have (a b c d : ℝ) : a * ((b * c) * d) = (c * d) * (b * a) := by ring
        /- We use the definitions of `c`, `n` and `d` to conclude the result. -/
        intro x
        simp only [← (toNNReal_strictMono one_lt_two).injective.eq_iff, ← NNReal.coe_inj,
          map_zpow₀, coe_zpow, ← Real.rpow_intCast]
        rw [← rpow_left_inj (z := (↑|d|)⁻¹) (by positivity) (by positivity) (by simpa),
          ← rpow_mul zero_le_coe, ← rpow_mul zero_le_coe]
        conv_rhs => rw [Int.cast_mul, mul_assoc, mul_inv_cancel₀ (by simpa), mul_one]
        rw [← NNReal.coe_rpow, ← valueGroup₀_equiv_withZeroMulInt_restrict_zpow_eq (by simp),
          ← valueGroup₀_equiv_withZeroMulInt_restrict_zpow_eq (by simp)]
        simp only [logEquiv_apply, map_zpow₀,  Int.cast_mul, Int.cast_abs, coe_rpow, coe_zpow]
        rw [← Real.rpow_intCast, ← rpow_mul zero_le_coe, ← Real.rpow_intCast,
          ← rpow_mul zero_le_coe, this, rpow_mul zero_le_coe]
        simp only [MulEquiv.coe_toMonoidWithZeroHom, OrderMonoidIso.coe_mulEquiv,
          valueGroup₀_equiv_withZeroMulInt_apply] at h_eq
        simp only [valueGroup₀_equiv_withZeroMulInt_apply, ← h_eq]
        rw [← abs_eq_self.mpr (le_of_lt hc_pos)]
        simp [n, d, hc, valueGroup₀_equiv_withZeroMulInt_apply]

end WithZeroMulInt

end Valuation
