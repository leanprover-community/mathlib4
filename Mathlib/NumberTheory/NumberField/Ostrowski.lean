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

## TODO

Archimedean case.

## References

* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]

## Tags

absolute value, number field, Ostrowski's theorem
-/

@[expose] public section

namespace NumberField

section Nonarchimedean

/-!
### The non-archimedean case

Every nontrivial non-archimedean absolute value on `K` is equivalent to a `v`-adic absolute value
for some `v : HeightOneSpectrum (𝓞 K)`. -/

open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NNReal

variable {K : Type*} [Field K] [NumberField K] {f : AbsoluteValue K ℝ}
variable (hfna : IsNonarchimedean f) (hf_nontriv : f.IsNontrivial)

/-- If the `v`-adic absolute value of `α` is at most one, then `α` can be written as a quotient of
algebraic integers with denominator a `v`-adic unit. -/
lemma exists_num_denom_adicAbv_eq_one {α : K} {v : HeightOneSpectrum (𝓞 K)}
    {b : ℝ≥0} (hb : 1 < b) (h_abs : v.adicAbv hb α ≤ 1) :
    ∃ x y : 𝓞 K, α = x / y ∧ v.adicAbv hb (y : K) = 1 := by
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v}ᶜ
  let γ : S.integer K := ⟨α, fun _ _ ↦ by simp_all [S, (toNNReal_le_one_iff hb).mp h_abs]⟩
  obtain ⟨⟨x, ⟨y, hy_away, hy_nzd⟩⟩, h⟩ := IsLocalization.surj (Localization.submonoid S) γ
  refine ⟨x, y, ?_, by simpa [adicAbv_coe_eq_one_iff, S] using hy_away⟩
  rw [eq_div_iff <| IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy_nzd]
  exact Subtype.ext_iff.mp h

include hfna

/-- Algebraic integers are contained in the closed unit ball of a non-archimedean absolute value. -/
lemma RingOfIntegers.absoluteValue_le_one (x : 𝓞 K) : f x ≤ 1 := by
  let B := basis K
  let C := ∑ i, f (B i)
  have hC (y : 𝓞 K) : f y ≤ C := by
    rw [← B.sum_repr y]
    calc
      f ↑(∑ i, (B.repr y i) • B i) ≤ ∑ i, f ((B.repr y i) • B i) := by
        push_cast
        exact f.sum_le _ _
      _ ≤ ∑ i, f (B i) := by
        gcongr
        rw [zsmul_eq_mul, map_mul]
        exact mul_le_of_le_one_left (apply_nonneg f _) <| hfna.apply_intCast_le_one
          (map_zero_le f 1) (map_one f) f.map_neg
  by_contra! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  exact (hC (x ^ n)).not_gt (by simp [hn])

include hf_nontriv in
/-- The open unit ball in `𝓞 K` is a non-zero prime ideal of `𝓞 K`. -/
def heightOneSpectrumOfAbsoluteValue : HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a | f a < 1}
    add_mem' := fun ha hb ↦ (hfna _ _).trans_lt (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' c _ hx := by
      simpa using (mul_le_of_le_one_left (apply_nonneg f _)
        (RingOfIntegers.absoluteValue_le_one hfna c)).trans_lt hx
  }
  isPrime := by
    rw [Ideal.isPrime_iff]
    constructor
    · rw [Ideal.ne_top_iff_one]
      change ¬f 1 < 1
      simp
    · change ∀ x y : 𝓞 K, f (x * y) < 1 → f x < 1 ∨ f y < 1
      intro _ _
      contrapose!
      simpa using fun h1 h2 ↦ one_le_mul_of_one_le_of_one_le h1 h2
  ne_bot := by
    rw [Submodule.ne_bot_iff]
    change ∃ x : 𝓞 K, f x < 1 ∧ x ≠ 0
    obtain ⟨a, ha, hfa⟩ := hf_nontriv
    obtain ⟨c, b, h, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    by_cases hfb : f b < 1
    · exact ⟨b, hfb, nonZeroDivisors.ne_zero h⟩
    grind [map_inv₀, RingOfIntegers.absoluteValue_le_one]

include hf_nontriv

/-- A nontrivial non-archimedean absolute value on a number field is equal to a `v`-adic absolute
value attached to a unique `v : HeightOneSpectrum (𝓞 K)` and for some base `b`. -/
theorem exists_heightOneSpectrum_eq_adicAbv :
    ∃! P : HeightOneSpectrum (𝓞 K), ∃ b, ∃ hb : 1 < b, f = adicAbv P hb := by
  let P := heightOneSpectrumOfAbsoluteValue hfna hf_nontriv
  use P
  rcases P.intValuation_exists_uniformizer with ⟨π, hπ⟩
  have hπv_ne : P.valuation K π ≠ 0 := by simp [valuation_of_algebraMap, hπ]
  have hπ_pos : 0 < f π := f.pos ((P.valuation K).ne_zero_iff.mp hπv_ne)
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    apply_mod_cast (one_lt_inv₀ hπ_pos).2
    change π ∈ P.asIdeal
    simp [← intValuation_lt_one_iff_mem, hπ]
  have f_eq_one_of_adicAbv_eq_one {x : K} (hx : P.adicAbv hb x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_adicAbv_eq_one hb (le_of_eq hx)
    have h {x : 𝓞 K} (hx : P.adicAbv hb (x : K) = 1) : f x = 1 := by
      rw [adicAbv_coe_eq_one_iff] at hx
      exact le_antisymm (RingOfIntegers.absoluteValue_le_one hfna x) (le_of_not_gt hx)
    simp [h (by simpa [hz] using hx), h hz]
  constructor
  · use b, hb
    ext x
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp
    have hxv_ne : P.valuation K x ≠ 0 := (P.valuation K).ne_zero_iff.mpr hx
    have coe_b : (b : ℝ) = (f π)⁻¹ := rfl
    simp only [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, AbsoluteValue.coe_mk,
      MulHom.coe_mk, WithZeroMulInt.toNNReal_neg_apply _ hxv_ne, coe_zpow, coe_b, inv_zpow]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_zpow₀, ← map_mul]
    apply f_eq_one_of_adicAbv_eq_one
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, coe_b, valuation_of_algebraMap,
      hπ, toNNReal_neg_apply, hxv_ne, zpow_ne_zero _ hπ_pos.ne']
  · rintro Q ⟨_, hc, rfl⟩
    ext x
    exact (adicAbv_coe_lt_one_iff Q hc x).symm

/-- A nontrivial non-archimedean absolute value on a number field is equivalent to a `v`-adic
absolute value attached to a unique `v : HeightOneSpectrum (𝓞 K)`. -/
theorem exists_heightOneSpectrum_equiv_adicAbv :
    ∃! P : HeightOneSpectrum (𝓞 K), f ≈ adicAbv K P := by
  obtain ⟨P, ⟨b, hb, hf⟩, -⟩ := exists_heightOneSpectrum_eq_adicAbv hfna hf_nontriv
  refine ⟨P, ?_, fun Q hQ ↦ ?_⟩
  · refine hf ▸ AbsoluteValue.isEquiv_iff_lt_one_iff.mpr fun _ ↦ ?_
    simpa [NumberField.HeightOneSpectrum.adicAbv, IsDedekindDomain.HeightOneSpectrum.adicAbv,
      IsDedekindDomain.HeightOneSpectrum.adicAbvDef] using
      (toNNReal_lt_one_iff hb).trans (toNNReal_lt_one_iff (one_lt_absNorm_nnreal P)).symm
  · ext x
    simpa only [NumberField.HeightOneSpectrum.adicAbv, hf,
      adicAbv_coe_lt_one_iff] using (hQ.lt_one_iff (x := (x : K))).symm

end Nonarchimedean

end NumberField
