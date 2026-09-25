/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Equiv

/-! # Normalized discrete valuations.

* `Valuation.normalized`: the surjective valuation onto `ℤᵐ⁰` which is equivalent to a
  given discrete valuation.
* `Valuation.normalized_eq_self`: a rank-one discrete valuation into `ℤᵐ⁰` attaining `exp (-1)`
  is its own normalization.
* `Valuation.IsEquiv.normalized_eq`: the normalization of a rank-one discrete valuation is an
  invariant of its equivalence class.

## Tags

valuation, discrete, normalized

-/

@[expose] public section

namespace Valuation

section map

variable {R Γ₀ Γ'₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
  [LinearOrderedCommMonoidWithZero Γ'₀] {f : Γ₀ →*₀o Γ'₀} (v : Valuation R Γ₀)

lemma IsEquiv.map_self (hf : StrictMono f) : v.IsEquiv (v.map f) :=
  fun a b ↦ by aesop (add norm StrictMono.le_iff_le)

end map

open Valuation Valuation.IsRankOneDiscrete MonoidWithZeroHom WithZero Function

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Ring

variable {R : Type*} [Ring R] (v : Valuation R Γ₀) [hv : v.IsRankOneDiscrete]

/-- The surjective valuation onto `ℤᵐ⁰` which is equivalent to a given discrete valuation. -/
noncomputable def normalized : Valuation R ℤᵐ⁰ :=
  v.restrict.map (hv.valueGroup₀_equiv_withZeroMulInt v)

theorem normalized_isEquiv : v.IsEquiv v.normalized :=
  v.isEquiv_restrict.trans (IsEquiv.map_self v.restrict
    (valueGroup₀_equiv_withZeroMulInt_strictMono v) )

instance : v.normalized.IsNontrivial := by
  rw [← v.normalized_isEquiv.isNontrivial_iff]
  infer_instance

instance normalized_isRankOneDiscrete : v.normalized.IsRankOneDiscrete := inferInstance

@[simp]
lemma normalized_inj {x y : R} : v.normalized x = v.normalized y ↔ v x = v y := by
  have h : Monotone (valueGroup₀_equiv_withZeroMulInt v) := by
    simp [(OrderHomClass.mono (valueGroup₀_equiv_withZeroMulInt v))]
  simp only [normalized, map_apply _ v.restrict,
    OrderMonoidWithZeroHom.coe_toOrderMonoidWithZeroHom, valueGroup₀_equiv_withZeroMulInt_apply]
  rw [(map'_injective (EquivLike.injective _)).eq_iff, v.restrict_inj]

@[simp, grind =]
lemma normalized_eq_zero_iff {x : R} : v.normalized x = 0 ↔ v x = 0 :=
  v.normalized_isEquiv.symm.eq_zero

@[simp, grind =]
lemma normalized_eq_one_iff {x : R} : v.normalized x = 1 ↔ v x = 1 :=
  v.normalized_isEquiv.symm.eq_one_iff_eq_one

@[simp, grind =]
lemma normalized_le_one_iff {x : R} : v.normalized x ≤ 1 ↔ v x ≤ 1 :=
  v.normalized_isEquiv.symm.le_one_iff_le_one

@[simp, grind =]
lemma normalized_lt_one_iff {x : R} : v.normalized x < 1 ↔ v x < 1 :=
  v.normalized_isEquiv.symm.lt_one_iff_lt_one

@[simp, grind =]
lemma normalized_one_le_iff {x : R} : 1 ≤ v.normalized x ↔ 1 ≤ v x :=
  v.normalized_isEquiv.symm.one_le_iff_one_le

@[simp, grind =]
lemma normalized_one_lt_iff {x : R} : 1 < v.normalized x ↔ 1 < v x :=
  v.normalized_isEquiv.symm.one_lt_iff_one_lt

open  MonoidWithZeroHom.ValueGroup₀

/-- `exp(-1) ∈ Set.range v.normalized` for any `IsRankOneDiscrete` valuation `v` on a ring
  containing a uniformizer for `v`. -/
lemma normalized_exp_neg_one_mem_range (π : v.Uniformizer) :
    WithZero.exp (-1 : ℤ) ∈ Set.range v.normalized := by
  obtain ⟨u, hu⟩ := IsRankOneDiscrete.exists_generator_lt_one v
  simp only [Int.reduceNeg, exp_neg, Set.mem_range]
  use π.val
  have hπ := π.2
  have h : Monotone (valueGroup₀_equiv_withZeroMulInt v) := by
    simp [(OrderHomClass.mono (valueGroup₀_equiv_withZeroMulInt v))]
  rw [IsUniformizer, ← embedding_generator', ← embedding_restrict,
    embedding_strictMono.injective.eq_iff] at hπ
  rw [normalized, map_apply, hπ, exp, ← intEquivOfZPowersEqTop_symm_self
    (g := (generator' v)⁻¹ ) (by simp [Subgroup.zpowers_inv, generator'_zpowers_eq_top v])]
  simp [_root_.map_inv]

end Ring

section CommRing

variable {R : Type*} [CommRing R] (v : Valuation R Γ₀) [hv : v.IsRankOneDiscrete]

/-- A rank-one discrete valuation into `ℤᵐ⁰` attaining `exp (-1)` is its own normalization. -/
theorem normalized_eq_self {v : Valuation R ℤᵐ⁰} [v.IsRankOneDiscrete]
    (h : WithZero.exp (-1 : ℤ) ∈ Set.range v) : v.normalized = v := by
  have := generator_eq_exp_neg_one_of_mem_range h
  obtain ⟨x, hx⟩ := h
  let π : v.Uniformizer := ⟨⟨x, by simp [mem_integer_iff, hx, ← exp_zero, exp_le_exp]⟩,
    by simp [IsUniformizer, hx, this]⟩
  exact IsRankOneDiscrete.eq_of_isEquiv_of_mem_range
    v.normalized_isEquiv.symm (v.normalized_exp_neg_one_mem_range π) ⟨x, hx⟩

lemma normalized_normalized (π : v.Uniformizer) :
    v.normalized.normalized = v.normalized :=
  normalized_eq_self (v.normalized_exp_neg_one_mem_range π)

end CommRing
section Field

variable {K : Type*} [Field K] (v : Valuation K Γ₀) [hv : v.IsRankOneDiscrete]

@[simp]
theorem valuationSubring_normalized_eq_valuationSubring :
    v.normalized.valuationSubring = v.valuationSubring :=
  (isEquiv_iff_valuationSubring v.normalized v).mp v.normalized_isEquiv.symm

/-- For any `IsRankOneDiscrete` valuation `v` on a field, its normalized form
`v.normalized : K → ℤᵐ⁰` is surjective. -/
lemma normalized_surjective : Function.Surjective v.normalized := by
  intro z
  obtain ⟨y, hy⟩ := (hv.valueGroup₀_equiv_withZeroMulInt v).surjective z
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (f := (v : K →*₀ Γ₀)) y
  exact ⟨r, by simp [← hy, ← hr, normalized]; congr⟩

/-- The normalization of a rank-one discrete valuation is an invariant of its equivalence
class. -/
theorem IsEquiv.normalized_eq {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]
    {v : Valuation K Γ₀} {w : Valuation K Γ'₀} [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) : v.normalized = w.normalized := by
  obtain ⟨x, hx⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨y, hy⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial w
  exact IsRankOneDiscrete.eq_of_isEquiv_of_mem_range
    (v.normalized_isEquiv.symm.trans (h.trans w.normalized_isEquiv))
    (v.normalized_exp_neg_one_mem_range ⟨x, hx⟩) (w.normalized_exp_neg_one_mem_range ⟨y, hy⟩)

@[simp]
theorem normalized_valuation_valuationSubring_eq_normalized :
    v.valuationSubring.valuation.normalized = v.normalized :=
  v.isEquiv_valuation_valuationSubring.symm.normalized_eq

open MonoidWithZeroHom.ValueGroup₀

/-- The ordered isomorphism between the `ValueGroup₀` of `v : K →*₀ Γ₀` and
`v.normalized : K →*₀ ℤᵐ⁰`. -/
noncomputable abbrev normalizedOrderMonoidIso :
    ValueGroup₀ (v : K →*₀ Γ₀) ≃*o ValueGroup₀ (v.normalized : K →*₀ ℤᵐ⁰) :=
  v.normalized_isEquiv.orderMonoidIso

lemma normalizedOrderMonoidIso_restrict (x : K) :
    v.normalizedOrderMonoidIso (v.restrict x) = v.normalized.restrict x := by
  simp [IsEquiv.orderMonoidIso_spec]

@[simp]
lemma normalizedOrderMonoidIso_generator' :
    v.normalizedOrderMonoidIso hv.generator' = v.normalized_isRankOneDiscrete.generator' := by
  set g := (restrict₀_surjective (v : K →*₀ Γ₀) hv.generator').choose with hg_def
  have hg : (restrict₀ (v : K →*₀ Γ₀)) g = ↑(generator' v) :=
    (restrict₀_surjective (v : K →*₀ Γ₀) hv.generator').choose_spec
  rw [← hg, ← restrict_def, normalizedOrderMonoidIso_restrict,
    ← (embedding_strictMono (f := (v.normalized : K →*₀ ℤᵐ⁰))).injective.eq_iff,
    embedding_generator', embedding_restrict]
  obtain ⟨π, hπ⟩ := v.normalized.exists_isUniformizer_of_isCyclic_of_nontrivial
  rw [← (embedding_strictMono (f := (v : K →*₀ Γ₀))).injective.eq_iff,
    embedding_restrict₀, coe_toMonoidWithZeroHom] at hg
  rw [← hπ.val, normalized_inj, v.normalized_isEquiv.isUniformizer_iff.mpr hπ, hg,
    embedding_generator']

end Field

section IsEquiv

variable {K Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Field K] {v w : Valuation K Γ}
  [hv : IsRankOneDiscrete v] [hw : IsRankOneDiscrete w] {e : NNReal} (he : 1 < e)

lemma IsRankOneDiscrete.rankOne_hom_eq_normalized :
   (hv.rankOne v he).hom =
      (IsRankOneDiscrete.rankOne v.normalized he).hom.comp
        v.normalizedOrderMonoidIso.toMonoidWithZeroHom := by
  ext x
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = hv.generator' ^ k := by
    have hx := Subgroup.mem_top x
    rw [← hv.generator'_zpowers_eq_top, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hk]⟩
  simp only [rankOne_hom_eq, MonoidHom.coe_comp, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe,
    toZeroHom_coe, coe_comp, MulEquiv.coe_toMonoidWithZeroHom, OrderMonoidIso.coe_mulEquiv,
    OneHom.coe_mk, Function.comp_apply, coeMonoidHom_apply, coe_zpow, map_zpow₀,
    valueGroup₀_equiv_withZeroMulInt_apply, map'_coe, MonoidHom.coe_ofClass, NNReal.coe_zpow,
    OrderMonoidIso.toMulEquiv_eq_coe, normalizedOrderMonoidIso_generator']
  nth_rw 2 [← inv_inv (generator' v), ← inv_inv (generator' v.normalized),
     ← zpow_neg_one]
  rw [← zpow_neg_one (generator' v.normalized)⁻¹, mulintEquivOfZPowersEqTop_symm_apply_zpow,
    mulintEquivOfZPowersEqTop_symm_apply_zpow]

lemma isEquiv_iff :
    v.IsEquiv w ↔
      ∃ (n : ℤ) (d : ℤ), 0 < n ∧ 0 < d ∧ ∀ (r : K), v.normalized r ^ d = w.normalized r ^ n := by
  rw [← isEquiv_iff_of_withZeroMulInt]
  exact ⟨fun h ↦(v.normalized_isEquiv).symm.trans (h.trans w.normalized_isEquiv),
    fun h ↦ (v.normalized_isEquiv).trans (h.trans (w.normalized_isEquiv).symm)⟩

end IsEquiv

end Valuation
