/-
Copyright (c) 2026 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Ostrowski's Theorem for number fields

Ostrowski's Theorem for number fields:
every nontrivial absolute value on `K` is equivalent to either a `v`-adic absolute value for some
`v : HeightOneSpectrum (𝓞 K)` or to an archimedean absolute value induced by an embedding of `K`
into `ℂ`.

## Main results

- `NumberField.exists_heightOneSpectrum_eq_adicAbv`: A nontrivial non-archimedean absolute value on
  a number field is equal to a `v`-adic absolute value for a unique `v : HeightOneSpectrum (𝓞 K)`
  and a suitable base.
- `NumberField.exists_heightOneSpectrum_equiv_adicAbv`: A nontrivial non-archimedean absolute value
  on a number field is equivalent to the `v`-adic absolute value `adicAbv K v` for a unique
  `v : HeightOneSpectrum (𝓞 K)`.
- `NumberField.exists_finitePlace_equiv`: A nontrivial non-archimedean absolute value on a number
  field is equivalent to a unique finite place `w : FinitePlace K`.

## TODO

Archimedean case.

## References

* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]

## Tags

absolute value, number field, Ostrowski's Theorem
-/

@[expose] public section

section Nonarchimedean

/-!
### The non-archimedean case

Every nontrivial non-archimedean absolute value on `K` is equivalent to a `v`-adic absolute value
for some `v : HeightOneSpectrum (𝓞 K)`. -/

open Finset Polynomial in
/-- An element that is integral over a ring whose image lies in the closed unit ball of a
non-archimedean absolute value lies in the closed unit ball as well. -/
lemma IsNonarchimedean.apply_le_one_of_isIntegral {R K : Type*} [CommRing R] [CommRing K]
    [Nontrivial K] [Algebra R K] {f : AbsoluteValue K ℝ} (hf : IsNonarchimedean f)
    (hR : ∀ r, f (algebraMap R K r) ≤ 1) {x : K} (hx : IsIntegral R x) : f x ≤ 1 := by
  obtain ⟨p, hp, hpx⟩ := hx
  by_contra! h
  suffices f (∑ i ∈ range (p.natDegree + 1), (algebraMap R K) (p.coeff i) * x ^ i) =
      f ((algebraMap R K) (p.coeff p.natDegree) * x ^ p.natDegree) by
    refine (pow_pos (one_pos.trans h) p.natDegree).ne ?_
    simpa [← eval₂_eq_sum_range, hpx, hp.coeff_natDegree] using this
  refine hf.apply_sum_eq_of_lt (fun i ↦ algebraMap R K (p.coeff i) * x ^ i) (map_neg_eq_map f)
    (self_mem_range_succ p.natDegree) fun j hj hjn ↦ ?_
  simp only [map_mul, map_pow, hp.coeff_natDegree, map_one, one_mul]
  exact (mul_le_of_le_one_left (by positivity) (hR _)).trans_lt (pow_lt_pow_right₀ h (by grind))

variable {K : Type*} [Field K]
variable {f : AbsoluteValue K ℝ} (hfna : IsNonarchimedean f) (hf_nontriv : f.IsNontrivial)

include hfna in
open NumberField in
/-- Algebraic integers are contained in the closed unit ball of a non-archimedean absolute value. -/
lemma RingOfIntegers.absoluteValue_le_one (x : 𝓞 K) : f x ≤ 1 :=
  hfna.apply_le_one_of_isIntegral
    (fun _ ↦ by simpa using hfna.apply_intCast_le_one (map_zero_le f 1) (map_one f) f.map_neg)
    x.isIntegral_coe

namespace NumberField

open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NNReal

variable [NumberField K]

/-- If the `v`-adic absolute value of `α` is at most one, then `α` can be written as a quotient of
algebraic integers with denominator a `v`-adic unit. -/
lemma exists_num_denom_of_adicAbv_eq_one {α : K} {v : HeightOneSpectrum (𝓞 K)}
    {b : ℝ≥0} (hb : 1 < b) (h_abs : v.adicAbv hb α ≤ 1) :
    ∃ x y : 𝓞 K, α = x / y ∧ v.adicAbv hb (y : K) = 1 := by
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v}ᶜ
  let γ : S.integer K := ⟨α, fun _ _ ↦ by simp_all [S, (toNNReal_le_one_iff hb).mp h_abs]⟩
  obtain ⟨⟨x, y, hy_away, hy_nzd⟩, h⟩ := IsLocalization.surj (Localization.submonoid S) γ
  refine ⟨x, y, ?_, by simpa [adicAbv_coe_eq_one_iff, S] using hy_away⟩
  rw [eq_div_iff <| IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy_nzd]
  exact Subtype.ext_iff.mp h

include hfna

include hf_nontriv in
/-- The open unit ball in `𝓞 K` is a non-zero prime ideal of `𝓞 K`. -/
def heightOneSpectrumOfAbsoluteValue : HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a | f a < 1}
    add_mem' ha hb := (hfna _ _).trans_lt (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' c _ hx := by
      simpa using (mul_le_of_le_one_left (apply_nonneg f _)
        (RingOfIntegers.absoluteValue_le_one hfna c)).trans_lt hx
  }
  isPrime := by
    simp_rw [Ideal.isPrime_iff, Ideal.ne_top_iff_one, ← Submodule.mem_carrier']
    refine ⟨by simp, fun {x} {y} ↦ ?_⟩
    contrapose!
    simpa using one_le_mul_of_one_le_of_one_le
  ne_bot := by
    simp_rw [Submodule.ne_bot_iff, ← Submodule.mem_carrier', Set.mem_ofPred_eq]
    obtain ⟨a, ha, hfa⟩ := hf_nontriv
    obtain ⟨c, b, h, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    by_cases hfb : f b < 1
    · exact ⟨b, hfb, nonZeroDivisors.ne_zero h⟩
    grind [map_inv₀, RingOfIntegers.absoluteValue_le_one]

include hf_nontriv

@[simp]
lemma mem_heightOneSpectrumOfAbsoluteValue {x : 𝓞 K} :
    x ∈ (heightOneSpectrumOfAbsoluteValue hfna hf_nontriv).asIdeal ↔ f x < 1 :=
  Iff.rfl

lemma notMem_heightOneSpectrumOfAbsoluteValue {x : 𝓞 K} :
    x ∉ (heightOneSpectrumOfAbsoluteValue hfna hf_nontriv).asIdeal ↔ f x = 1 := by
  rw [mem_heightOneSpectrumOfAbsoluteValue, not_lt]
  exact ⟨(RingOfIntegers.absoluteValue_le_one hfna x).antisymm, ge_of_eq⟩

/-- A nontrivial non-archimedean absolute value `f` is `1` on the units of the `v`-adic absolute
value, where `v` is `NumberField.heightOneSpectrumOfAbsoluteValue`. -/
lemma apply_eq_one_of_adicAbv_eq_one {b : ℝ≥0} (hb : 1 < b) {x : K}
    (hx : (heightOneSpectrumOfAbsoluteValue hfna hf_nontriv).adicAbv hb x = 1) : f x = 1 := by
  obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_of_adicAbv_eq_one hb hx.le
  have hy : (heightOneSpectrumOfAbsoluteValue hfna hf_nontriv).adicAbv hb (y : K) = 1 := by
    simpa [hz] using hx
  rw [adicAbv_coe_eq_one_iff, notMem_heightOneSpectrumOfAbsoluteValue] at hy hz
  simp [hy, hz]

/-- **Ostrowski's Theorem, non-archimedean case** A nontrivial non-archimedean absolute value on a
number field is equal to a `v`-adic absolute value attached to a unique
`v : HeightOneSpectrum (𝓞 K)` and for some base `b`. -/
theorem exists_heightOneSpectrum_eq_adicAbv :
    ∃! P : HeightOneSpectrum (𝓞 K), ∃ b, ∃ hb : 1 < b, f = adicAbv P hb := by
  let P := heightOneSpectrumOfAbsoluteValue hfna hf_nontriv
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπv_ne : P.valuation K π ≠ 0 := by simp [valuation_of_algebraMap, hπ]
  have hπ_pos : 0 < f π := f.pos ((P.valuation K).ne_zero_iff.mp hπv_ne)
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    apply_mod_cast (one_lt_inv₀ hπ_pos).2
    simp [P, ← mem_heightOneSpectrumOfAbsoluteValue hfna hf_nontriv,
      ← intValuation_lt_one_iff_mem, hπ]
  refine ⟨P, ⟨b, hb, P.eq_adicAbv_of_apply_uniformizer hb
    (fun _ ↦ apply_eq_one_of_adicAbv_eq_one hfna hf_nontriv hb) hπ (inv_inv _).symm⟩, ?_⟩
  rintro Q ⟨_, hc, rfl⟩
  ext x
  exact (adicAbv_coe_lt_one_iff Q hc x).symm

/-- **Ostrowski's Theorem, non-archimedean case** A nontrivial non-archimedean absolute value on a
number field is equivalent to a `v`-adic absolute value attached to a unique
`v : HeightOneSpectrum (𝓞 K)`. -/
theorem exists_heightOneSpectrum_equiv_adicAbv :
    ∃! P : HeightOneSpectrum (𝓞 K), f ≈ adicAbv K P := by
  obtain ⟨P, ⟨_, hb, rfl⟩, -⟩ := exists_heightOneSpectrum_eq_adicAbv hfna hf_nontriv
  refine ⟨P, AbsoluteValue.isEquiv_iff_lt_one_iff.mpr fun _ ↦ ?_, fun Q hQ ↦ ?_⟩
  · exact (adicAbv_lt_one_iff P hb _).trans (adicAbv_lt_one_iff P _ _).symm
  · ext x
    exact (adicAbv_coe_lt_one_iff Q _ x).symm.trans <|
      hQ.lt_one_iff.symm.trans (adicAbv_coe_lt_one_iff P hb x)

/-- **Ostrowski's Theorem, non-archimedean case** A nontrivial non-archimedean absolute value on a
number field is equivalent to a unique finite place. -/
theorem exists_finitePlace_equiv : ∃! w : FinitePlace K, f ≈ w.val := by
  refine FinitePlace.equivHeightOneSpectrum.symm.existsUnique_congr_right.mp ?_
  convert exists_heightOneSpectrum_equiv_adicAbv hfna hf_nontriv using 4
  exact AbsoluteValue.ext (FinitePlace.norm_embedding _)

end NumberField

end Nonarchimedean
