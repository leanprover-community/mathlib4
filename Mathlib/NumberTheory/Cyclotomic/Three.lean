/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Pietro Monticone
-/

import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Third Cyclotomic Field
We gather various results about the third cyclotomic field. The following notations are used in this
file: `K` is a number field such that `IsCyclotomicExtension {3} ℚ K`, `ζ` is any primitive `3`-rd
root of unity in `K`, `η` is the element in the units of the ring of integers corresponding to `ζ`
and `λ = η - 1`.

## Main results
* `IsCyclotomicExtension.Rat.Three.Units.mem`: Given a unit `u : (𝓞 K)ˣ`, we have that
`u ∈ {1, -1, η, -η, η^2, -η^2}`.

* `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`: Given a unit
`u : (𝓞 K)ˣ`, if `u` is congruent to an integer modulo `3`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma* (see for example [washington_cyclotomic],
Theorem 5.36
-/

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)
local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => (η : 𝓞 K) - 1

open scoped Classical

/-- Let `u` be a unit in `(𝓞 K)ˣ`, then `u ∈ {1, -1, η, -η, η^2, -η^2}`. -/
theorem Units.mem : u ∈ ({1, -1, η, -η, η ^ 2, -η ^ 2} : Finset (𝓞 K)ˣ) := by
  have hrank : rank K = 0 := by
    dsimp only [rank]
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero (n := 3) K (by decide),
      zero_add, nrComplexPlaces_eq_totient_div_two (n := 3)]
    rfl
  obtain ⟨⟨x, e⟩, hxu, -⟩ := exist_unique_eq_mul_prod _ u
  replace hxu : u = x := by
    rw [← mul_one x.1, hxu]
    apply congr_arg
    rw [← Finset.prod_empty]
    congr
    rw [Finset.univ_eq_empty_iff, hrank]
    infer_instance
  obtain ⟨n, hnpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.1 <| (CommGroup.mem_torsion _ _).1 x.2
  replace hn : (↑u : K) ^ ((⟨n, hnpos⟩ : ℕ+) : ℕ) = 1 := by
    rw [← map_pow]
    convert map_one (algebraMap (𝓞 K) K)
    rw_mod_cast [hxu, hn]
    simp
  obtain ⟨r, hr3, hru⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide)
    (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hn⟩)
  replace hr : r ∈ Finset.Ico 0 3 := Finset.mem_Ico.2 ⟨by simp, hr3⟩
  replace hru : ↑u = η ^ r ∨ ↑u = -η ^ r := by
    rcases hru with (h | h)
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr
  all_goals{
    rcases hru with (h | h)
    · simp [h]
    · simp [h]}

/-- We have that `λ ^ 2 = -3 * η`. -/
lemma lambda_sq : λ ^ 2 = -3 * η := by
  ext
  calc (λ ^ 2 : K) = η ^ 2 + η + 1 - 3 * η := by ring
  _ = 0 - 3 * η := by simpa using hζ.isRoot_cyclotomic (by decide)
  _ = -3 * η := by ring

lemma eta_sq : (η ^ 2 : 𝓞 K) = - η - 1 := by
  rw [← neg_add', ← add_eq_zero_iff_eq_neg, ← add_assoc]
  ext; simpa using hζ.isRoot_cyclotomic (by decide)

/-- If a unit `u` is congruent to an integer modulo `λ ^ 2`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma*. -/
theorem eq_one_or_neg_one_of_unit_of_congruent (hcong : ∃ n : ℤ, λ ^ 2 ∣ (u - n : 𝓞 K)) :
    u = 1 ∨ u = -1 := by
  replace hcong : ∃ n : ℤ, (3 : 𝓞 K) ∣ (↑u - n : 𝓞 K) := by
    obtain ⟨n, x, hx⟩ := hcong
    exact ⟨n, -η * x, by rw [← mul_assoc, mul_neg, ← neg_mul, ← lambda_sq, hx]⟩
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have := Units.mem hζ u
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  have h2 : (hζ.pow_of_coprime 2 (by decide)).toInteger = hζ.toInteger ^ 2 := by ext; simp
  rcases this with (rfl | h | h | h | h | h)
  · left; rfl
  · right; ext; simp [h]
  · exfalso
    apply hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide)
    convert hcong
    simp [h]
  · exfalso
    apply hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add, h] at hx
    refine ⟨-n, -x, sub_eq_iff_eq_add.2 ?_⟩
    simp [mul_neg, ← neg_add, ← hx]
  · exfalso
    apply (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide)
    convert hcong
    simp [h2, h]
  · apply (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, sub_eq_iff_eq_add.2 ?_⟩
    simp only [h2, PNat.val_ofNat, Nat.cast_ofNat, mul_neg, Int.cast_neg, ← neg_add,
      ← sub_eq_iff_eq_add.1 hx, Units.val_neg, val_pow_eq_pow_val, IsUnit.unit_spec, neg_neg]
