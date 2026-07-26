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
# Ostrowski’s Theorem for number fields

Ostrowski's Theorem for number fields:
every nontrivial absolute value on `K` is equivalent to either a `v`-adic absolute value for some
`v : HeightOneSpectrum (𝓞 K)` or to some archimedean absolute value induced by an embedding of `K`
into `ℂ`.

## Main results

- `NumberField.exists_heightOneSpectrum_eq_adicAbv`: A nontrivial non-archimedean absolute value on
  a number field is equal to a `v`-adic absolute value for some `v : HeightOneSpectrum (𝓞 K)`.

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

Every bounded absolute value on `K` is equivalent to a `v`-adic absolute value for some
`v : HeightOneSpectrum (𝓞 K)`. -/

open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField NNReal

variable {K : Type*} [Field K] [NumberField K] (f : AbsoluteValue K ℝ)
variable (hf_nonarch : IsNonarchimedean f) (hf_nontriv : f.IsNontrivial)

/-- If the `v`-adic absolute value of `α` is at most one, then `α` can be written as a quotient of
algebraic integers with denominator a `v`-adic unit. -/
lemma exists_num_denom_adicAbv_eq_one {α : K} {v : HeightOneSpectrum (𝓞 K)}
    {b : ℝ≥0} (hb : 1 < b) (h_abs : v.adicAbv hb α ≤ 1) :
  ∃ x y : 𝓞 K, α = x / y ∧ v.adicAbv hb (y : K) = 1 := by
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v}ᶜ
  have mem : α ∈ S.integer K := by
    intro _ hw
    simp_all [S, (toNNReal_le_one_iff hb).mp h_abs]
  letI : Fact (IsMulTorsion (ClassGroup (𝓞 K))) := fact_iff.mpr isMulTorsion_of_finite
  let γ : S.integer K := ⟨α, mem⟩
  obtain ⟨⟨x, ⟨y, hy_away, hy_nzd⟩⟩, h⟩ := IsLocalization.surj S.submonoid γ
  refine ⟨x, y, ?_, by simpa [adicAbv_coe_eq_one_iff, S] using hy_away⟩
  rw [eq_div_iff <| IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy_nzd]
  exact Subtype.ext_iff.mp h

include hf_nonarch in
/-- Algebraic integers are contained in the closed unit ball of a non-archimedean absolute value. -/
lemma RingOfIntegers.absoluteValue_le_one (x : 𝓞 K) : f x ≤ 1 := by
  let B := basis K
  let C := ∑ i, f (B i)
  have hC (y : 𝓞 K) : f y ≤ C := by
    rw [← B.sum_repr y]
    calc
      f ↑(∑ i, (B.repr y i) • B i) ≤ ∑ i, f ((B.repr y i) • B i) := by
        rw [coe_eq_algebraMap, map_sum]
        exact f.sum_le _ _
      _ ≤ ∑ i, f (B i) := by
        apply Finset.sum_le_sum
        intro _ _
        rw [zsmul_eq_mul, map_mul]
        exact mul_le_of_le_one_left (apply_nonneg f _) <|
          IsNonarchimedean.apply_intCast_le_one hf_nonarch
  have hx_root {k : ℕ} (hk : k ≠ 0) : f x ≤ C ^ (1 / (k : ℝ)) := by
    rw [one_div, ← Real.pow_rpow_inv_natCast (apply_nonneg f (x : K)) hk, ← map_pow]
    exact Real.rpow_le_rpow (apply_nonneg f _) (hC (x ^ k)) (by positivity)
  have ht : Filter.atTop.Tendsto (fun k : ℕ ↦ C ^ (1 / (k : ℝ))) (nhds 1) := by
    simpa using tendsto_const_nhds.rpow (tendsto_one_div_atTop_nhds_zero_nat)
      (Or.inl <| ne_of_gt <| lt_of_lt_of_le zero_lt_one (by simpa using hC 1))
  exact ge_of_tendsto ht <| Filter.eventually_atTop.2 ⟨1, fun k hk ↦ hx_root (ne_of_gt hk)⟩

include hf_nonarch hf_nontriv in
/-- The open unit ball in `𝓞 K` is a non-zero prime ideal of `𝓞 K`. -/
def maximalIdeal : HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a | f a < 1}
    add_mem' := fun ha hb ↦ lt_of_le_of_lt (hf_nonarch _ _) (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := by
      simpa [Set.mem_ofPred_eq] using
        (fun (c x : 𝓞 K) hx ↦ mul_lt_one_of_nonneg_of_lt_one_right
            (RingOfIntegers.absoluteValue_le_one f hf_nonarch c) (apply_nonneg f ↑x) hx)
  }
  isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      · rw [Ideal.ne_top_iff_one]
        change ¬f 1 < 1
        simp
      · change ∀ x y : 𝓞 K, f (x * y) < 1 → f x < 1 ∨ f y < 1
        intro x y hxy
        rw [map_mul] at hxy
        by_contra! h
        linarith [one_le_mul_of_one_le_of_one_le h.1 h.2]
  ne_bot := by
    rw [Submodule.ne_bot_iff]
    change ∃ x : 𝓞 K, f x < 1 ∧ x ≠ 0
    obtain ⟨a, ha, hfa⟩ := hf_nontriv
    obtain ⟨c, b, h, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    by_cases hfb : f b < 1
    · exact ⟨b, hfb, nonZeroDivisors.ne_zero h⟩
    rw [map_div₀,
      le_antisymm (RingOfIntegers.absoluteValue_le_one f hf_nonarch b) (le_of_not_gt hfb)] at hfa
    grind [RingOfIntegers.absoluteValue_le_one]

include hf_nonarch in
/-- A nontrivial non-archimedean absolute value on a number field is equal to a `v`-adic absolute
value attached for some `v : HeightOneSpectrum (𝓞 K)`. -/
theorem exists_heightOneSpectrum_eq_adicAbv (hf_nontriv : f.IsNontrivial) :
    ∃! P : HeightOneSpectrum (𝓞 K), ∃ b, ∃ hb : 1 < b, f = adicAbv P hb := by
  let P := maximalIdeal f hf_nonarch hf_nontriv
  use P
  rcases intValuation_exists_uniformizer P with ⟨π, hπ⟩
  have hπv_ne : P.valuation K (π : K) ≠ 0 := by simp [valuation_of_algebraMap, hπ]
  have hπ_pos : 0 < f π := by grind [AbsoluteValue.pos_iff]
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    apply_mod_cast (one_lt_inv₀ hπ_pos).2
    change π ∈ P.asIdeal
    simp [← intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, -WithZero.exp_neg]
  have f_eq_one_of_adicAbv_eq_one {x : K} (hx : P.adicAbv hb x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_adicAbv_eq_one hb (le_of_eq hx)
    have int {x : 𝓞 K} (hx : P.adicAbv hb (x : K) = 1) : f x = 1 := by
      rw [adicAbv_coe_eq_one_iff] at hx
      exact le_antisymm (RingOfIntegers.absoluteValue_le_one f hf_nonarch x) (le_of_not_gt hx)
    have hy : P.adicAbv hb (y : K) = 1 := by simpa [map_div₀, hz] using hx
    simp [map_div₀, int hy, int hz]
  constructor
  · use b, hb
    ext x
    by_cases hx : x = 0
    · simp [hx]
    have hxv_ne : P.valuation K x ≠ 0 := (P.valuation K).ne_zero_iff.mpr hx
    have coe_b : (b : ℝ) = (f π)⁻¹ := rfl
    simp only [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, AbsoluteValue.coe_mk,
      MulHom.coe_mk, WithZeroMulInt.toNNReal_neg_apply _ hxv_ne, coe_zpow, coe_b, inv_zpow]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_zpow₀, ← map_mul]
    apply f_eq_one_of_adicAbv_eq_one
    have : (WithZero.unzero hπv_ne).toAdd = -1 := by
      simp [valuation_of_algebraMap, hπ, WithZero.toAdd_unzero]
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, coe_b,
      WithZeroMulInt.toNNReal_neg_apply _ hπv_ne, WithZeroMulInt.toNNReal_neg_apply _ hxv_ne, this,
      zpow_ne_zero _ hπ_pos.ne']
  · simp only [forall_exists_index]
    rintro Q _ hc rfl
    ext x
    exact (adicAbv_coe_lt_one_iff Q hc x).symm

end Nonarchimedean

end NumberField
