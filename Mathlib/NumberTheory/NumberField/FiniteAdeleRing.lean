/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/

module

public import Mathlib.NumberTheory.NumberField.FinitePlaces
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The finite adele ring of a number field

This file concerns the finite adele ring of a Dedekind domain `R` and its field of
fractions under the assumption that `K` is a number field.

## Tags
adele ring, number field
-/

namespace NumberField

section norm

variable {K : Type*} [Field K] [NumberField K]

namespace FiniteAdeleRing

open RingOfIntegers.HeightOneSpectrum IsDedekindDomain HeightOneSpectrum

theorem mulSupport_finite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v ↦ ‖x.1 v‖).Finite := by
  simpa [Function.mulSupport, Valued.toNormedField.norm_eq_one_iff] using
    FiniteAdeleRing.unitsEquiv_finite_valued_eq_one x

private theorem hasProd_subset_valued_lt_one (x : FiniteAdeleRing (𝓞 K) K) :
    HasProd (fun v : {v | 1 < Valued.v (x v)} ↦ ‖x v‖)
      (∏ᶠ v : {v | 1 < Valued.v (x v)}, ‖x v‖) := by
  have : {v | 1 < Valued.v (x v)}.Finite := by
    simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using x.2
  have : Fintype _ := Set.Finite.fintype this
  rw [finprod_eq_prod_of_fintype]
  exact hasProd_fintype _

open Filter HeightOneSpectrum Valued in
private theorem hasProd_zero_subset_one_lt_valued {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬IsUnit x)
    (hx₀ : ∀ v, x v ≠ 0) : HasProd (fun v : {v | Valued.v (x v) < 1} ↦ ‖x v‖) 0 :=
  have hx := FiniteAdeleRing.infinite_valued_ne_one_of_not_isUnit (by simpa using hx₀) hx
  have hx_prop : {v | 1 < Valued.v (x v)}.Finite := by simpa [mem_adicCompletionIntegers] using x.2
  have hx_inf : {v | Valued.v (x v) < 1}.Infinite := (hx.diff hx_prop).mono (by grind)
  have : atTop.Tendsto (fun s : Finset {v | Valued.v (x v) < 1} ↦ (∏ v ∈ s, ‖x v‖)⁻¹) atTop := by
    have h_le (S : Finset {v | Valued.v (x v) < 1}) : 2 ^ S.card ≤ (∏ v ∈ S, ‖x v‖)⁻¹ := by
      have (v : _) (h : v ∈ S) : 2 ≤ ‖(x v)⁻¹‖  := by
        apply FinitePlace.two_le_norm_of_one_lt_norm
        grind [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (Valued.v.pos_iff.2 (hx₀ v))]
      simpa [Finset.prod_const] using (Finset.prod_le_prod (by grind) this).trans (by simp)
    apply tendsto_atTop_mono h_le ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp ?_)
    apply Filter.tendsto_atTop_atTop_of_monotone Finset.card_mono fun N ↦ ?_
    obtain ⟨t, ht, _⟩ := hx_inf.exists_subset_card_eq N
    exact ⟨t.subtype _, by grind [Finset.card_subtype, Finset.card_filter_eq_iff.2 ht]⟩
  (tendsto_inv_atTop_zero.comp this).congr (by simp)

theorem hasProd_zero_of_not_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬IsUnit x) :
    HasProd (fun v ↦ ‖x v‖) 0 := by
  by_cases hx₀ : ∃ v, x v = 0
  · exact hasProd_zero_of_exists_eq_zero (by simpa using hx₀)
  have hT := hasProd_zero_subset_one_lt_valued hx (by simpa using hx₀)
  have h : HasProd (fun v : {v | Valued.v (x v) = 1} ↦ ‖x.1 v‖) 1 := by
    convert hasProd_one; aesop (add simp [Valued.toNormedField.norm_eq_one_iff])
  have := HasProd.mul_disjoint (by grind) (hasProd_subset_valued_lt_one x) h (f := fun v ↦ ‖x v‖)
  simpa using this.mul_isCompl ⟨by grind, fun _ _ _ ↦ by simp_all; grind⟩ hT

theorem tprod_norm_of_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : IsUnit x) :
    ∏' v, ‖x.1 v‖ = ∏ᶠ v, ‖x.1 v‖ := by
  rw [tprod_eq_finprod]
  exact mulSupport_finite hx.unit

theorem tprod_norm_of_unit (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ∏' v, ‖x.1 v‖ = ∏ᶠ v, ‖x.1 v‖ :=
  tprod_norm_of_isUnit x.isUnit

theorem tprod_eq_zero_of_not_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬ IsUnit x) :
    ∏' v, ‖x.1 v‖ = 0 := by
  rw [HasProd.tprod_eq]
  exact hasProd_zero_of_not_isUnit hx

instance : Norm (FiniteAdeleRing (𝓞 K) K) where norm x := ∏' v, ‖x.1 v‖

theorem norm_def (x : FiniteAdeleRing (𝓞 K) K) : ‖x‖ = ∏' v, ‖x.1 v‖ := rfl

theorem norm_def_unit (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : ‖x.1‖ = ∏ᶠ v, ‖x.1 v‖ :=
  tprod_norm_of_unit x

theorem norm_eq_zero_of_not_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬IsUnit x) : ‖x‖ = 0 :=
  tprod_eq_zero_of_not_isUnit hx

theorem coe_norm_apply (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ).1‖ = ∏ᶠ v, FinitePlace.mk v x.1 := norm_def_unit _

theorem coe_norm_apply_eq_finprod_finitePlace (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ).1‖ = ∏ᶠ v : FinitePlace K, v x := by
  rw [coe_norm_apply, ← finprod_comp FinitePlace.equivHeightOneSpectrum.invFun
    FinitePlace.equivHeightOneSpectrum.symm.bijective]
  exact finprod_congr fun _ ↦ rfl

theorem coe_norm_eq_inv_abs_norm (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ).1‖ = |Algebra.norm ℚ x.1|⁻¹ := by
  rw [← FinitePlace.prod_eq_inv_abs_norm x.ne_zero, coe_norm_apply_eq_finprod_finitePlace]

end NumberField.FiniteAdeleRing
