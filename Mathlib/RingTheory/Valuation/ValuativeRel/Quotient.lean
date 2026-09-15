/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.Valuation.Quotient

/-! # Valuations on a quotient ring and its fraction field

Given a ring `R` with a valuative rel `vr`, `vr.supp` is defined as the support of `vr.valuation`.

If `v : Valuation R Γ₀` is any valuation compatible with `vr`, we define `v.onQuotSupp` as the
valuation that `v` induces on `R / vr.supp`.

If `L` is a fraction field of `R`, `v.onQuotSuppExtend R L` is the extension of `v.onQuotSupp`
to `L`. -/

@[expose] public section

namespace Valuation

open IsRankOneDiscrete MonoidWithZeroHom

section Ring

variable {R Γ Γ' : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ'] {v : Valuation R Γ} {w : Valuation R Γ'}
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [vr : ValuativeRel R] [hv : v.Compatible]

variable (v) in
/-- Given `vr : ValuativeRel R` and a valuation `v` on `R` compatible with `vr`, this is the
  extension of `v` to a valuation on `R / vr.supp`. -/
noncomputable def onQuotSupp : Valuation (R ⧸ vr.supp) Γ := v.onQuot (by
  intro x
  simp only [ValuativeRel.supp_eq_valuation_supp, mem_supp_iff]
  have : vr.valuation.IsEquiv v := by
    apply IsEquiv.symm
    rwa [← compatible_iff_isEquiv]
  simp [this.eq_zero])

lemma onQuotSupp_mk (r : R) : onQuotSupp v ((Ideal.Quotient.mk vr.supp) r) = v r := rfl

lemma onQuotSupp_isRankOneDiscrete [hv : IsRankOneDiscrete v] : v.onQuotSupp.IsRankOneDiscrete where
  exists_generator_lt_one' := by
    obtain ⟨γ, hγ, hg1⟩ := hv
    refine ⟨γ, ?_, hg1⟩
    rw [hγ]
    ext g
    simp only [mem_valueGroup_iff_exists_mk_of_comm, MonoidWithZeroHom.coe_ofClass]
    refine ⟨fun ⟨x, y, hx0, hy0, h⟩ ↦ by
        use Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y
        simp only [h, onQuotSupp_mk, ne_eq, hy0, not_false_eq_true, exists_true_left, hx0]
        ext
        rw [valueGroup.mk_eq_div (ofClass v) hx0 hy0,
          valueGroup.mk_eq_div (ofClass v.onQuotSupp) (by aesop) (by aesop)]
        simp [onQuotSupp_mk],
      fun ⟨x, y, hx0, hy0, h⟩ ↦ ?_⟩
    obtain ⟨r, hr⟩ :=  Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs⟩ :=  Ideal.Quotient.mk_surjective y
    refine ⟨r, s, by simpa only [← hr, ne_eq, onQuotSupp_mk] using hx0,
      by simpa only [← hs, ne_eq, onQuotSupp_mk] using hy0, ?_⟩
    ext
    have hr0 : v r ≠ 0 := by aesop
    have hs0 : v s ≠ 0 := by aesop
    simp [h, valueGroup.mk_eq_div (ofClass v) hr0 hs0,
      valueGroup.mk_eq_div (ofClass v.onQuotSupp),
      ← hr, ← hs, onQuotSupp_mk]

variable (v w) in
lemma onQuotSupp_isEquiv [w.Compatible] : (onQuotSupp v).IsEquiv (onQuotSupp w) := by
  have h : v.IsEquiv w := ValuativeRel.isEquiv v w
  rw [IsEquiv] at h
  intro x y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp [onQuotSupp_mk, h]

variable (L : Type*) [Field L] [Algebra (R ⧸ vr.supp) L] [IsFractionRing (R ⧸ vr.supp) L]

variable (R v) in
/-- Given `vr : ValuativeRel R`, a fraction ring `L` for `R ⧸ vr.supp` and a valuation `v` on `R`
  compatible with `vr`, this is the extension of `v` to a valuation on `L`. -/
noncomputable def onQuotSuppExtend : Valuation L Γ := by
  refine (onQuotSupp v).extendToLocalization (S := nonZeroDivisors (R ⧸ vr.supp)) ?_ L
  intro r hr
  have : v.supp = vr.valuation.supp := by
    apply IsEquiv.supp
    rwa [← compatible_iff_isEquiv]
  simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hr
  simp [onQuotSupp, v.supp_quot, this, ← ValuativeRel.supp_eq_valuation_supp, hr]

@[simp]
lemma onQuotSuppExtend_algebraMap [Algebra R L] [IsScalarTower R (R ⧸ vr.supp) L] (r : R) :
    v.onQuotSuppExtend R L (algebraMap R L r) = v r := by
  have : (algebraMap R L) r = (algebraMap (R ⧸ vr.supp) L) (algebraMap R (R ⧸ vr.supp) r) :=
    IsScalarTower.algebraMap_apply R (R ⧸ vr.supp) L r
  simp [onQuotSuppExtend, this, onQuotSupp_mk]

@[simp]
lemma onQuotSuppExtend_algebraMap' (r : R ⧸ vr.supp) :
    onQuotSuppExtend R v L (algebraMap (R ⧸ vr.supp) L r) = onQuotSupp v r := by
  simp [onQuotSuppExtend]

lemma onQuotSuppExtend_isRankOneDiscrete [hv : IsRankOneDiscrete v] :
    (onQuotSuppExtend R v L).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    let hv' := v.onQuotSupp_isRankOneDiscrete
    obtain ⟨γ, hγ, hg1⟩ := hv'
    refine ⟨γ, ?_, hg1⟩
    rw [hγ]
    ext g
    simp only [mem_valueGroup_iff_exists_mk_of_comm, MonoidWithZeroHom.coe_ofClass]
    refine ⟨fun ⟨x, y, hx0, hy0, h⟩ ↦
        ⟨algebraMap _ L x, algebraMap _ L y, by simp [hx0], by simp [hy0], ?_⟩,
      fun ⟨x, y, hx0, hy0, h⟩ ↦ ?_⟩
    · rw [h]
      ext
      rw [valueGroup.mk_eq_div (ofClass (onQuotSuppExtend R v L)) (by simp [hx0]) (by simp [hy0])]
      simp [valueGroup.mk_eq_div (ofClass v.onQuotSupp) hx0 hy0]
    obtain ⟨nx, dx, hdx0, hx⟩ := IsFractionRing.div_surjective (R ⧸ vr.supp) x
    obtain ⟨ny, dy, hdy0, hy⟩ := IsFractionRing.div_surjective (R ⧸ vr.supp) y
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hdx0 hdy0
    simp only [← hx, map_div₀, onQuotSuppExtend_algebraMap', ne_eq,
      div_eq_zero_iff, not_or, ← hy] at hx0 hy0
    refine ⟨nx * dy, dx * ny,by simp [hx0, hy0], by simp [hx0, hy0], ?_⟩
    ext
    rw [valueGroup.mk_eq_div (ofClass v.onQuotSupp) (by aesop) (by aesop), h,
      valueGroup.mk_eq_div ((ofClass (onQuotSuppExtend R v L))) (by aesop) (by aesop),
      ← hx, ← hy]
    simp only [map_div₀, MonoidWithZeroHom.coe_ofClass, onQuotSuppExtend_algebraMap', map_mul]
    field_simp -- This is slow

variable (v w) in
lemma onQuotSuppExtend_isEquiv [w.Compatible] :
    (onQuotSuppExtend R v L).IsEquiv (onQuotSuppExtend R w L) := by
  have h' : v.IsEquiv w := ValuativeRel.isEquiv v w
  have h : v.onQuotSupp.IsEquiv w.onQuotSupp := onQuotSupp_isEquiv v w
  rw [IsEquiv] at h
  rw [isEquiv_iff_val_le_one]
  intro x
  obtain ⟨nx, dx, hx0, rfl⟩ := IsFractionRing.div_surjective (R ⧸ vr.supp) x
  simp only [map_div₀]
  rw [div_le_one₀, div_le_one₀]
  · simp [onQuotSuppExtend, h]
  all_goals
    rw [pos_iff_ne_zero, ne_zero_iff]
    exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L (fun ⦃x⦄ a ↦ a) hx0

open WithZero in
lemma onQuotSuppExtend_mem_range {v : Valuation R ℤᵐ⁰} [v.Compatible]
    (hv : WithZero.exp (-1) ∈ Set.range v) :
    WithZero.exp (-1) ∈ Set.range (onQuotSuppExtend R v L) := by
  obtain ⟨r, hr⟩ := hv
  exact ⟨algebraMap (R ⧸ ValuativeRel.supp R) L r, by  simp [onQuotSuppExtend, onQuotSupp_mk, hr]⟩

end Ring

end Valuation
