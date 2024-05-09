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
root of unity in `K`, `η` is the element in the ring of integers corresponding to `ζ` and
`λ = η - 1`.

## Main results
* `IsCyclotomicExtension.Rat.Three.Units.mem`: Given a unit `u : (𝓞 K)ˣ`, we have that
`u ∈ ({1, -1, η, -η, η^2, -η^2}`.

* `IsCyclotomicExtension.Rat.Three.Units.mem.eq_one_or_neg_one_of_unit_of_congruent`: Given a unit
`u : (𝓞 K)ˣ`, if `u` is congruent to an integer modulo `3`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma*.
-/

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)
local notation3 "η" => hζ.toInteger
local notation3 "λ" => hζ.toInteger - 1

/-- Let `u` be a unit in `(𝓞 K)ˣ`, then `u ∈ {1, -1, η, -η, η^2, -η^2}`. -/
theorem Units.mem : ↑u ∈({1, -1, η, -η, η ^ 2, -η ^ 2} : Set (𝓞 K)) := by
  have hrank : rank K = 0 := by
    dsimp [rank]
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
  have hodd : Odd ((3 : ℕ+) : ℕ) := by decide
  obtain ⟨r, hr3, hru⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hodd
    (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hn⟩)
  replace hr : r ∈ Finset.Ico 0 3 := Finset.mem_Ico.2 ⟨by simp, hr3⟩
  replace hru : ↑u = η ^ r ∨ ↑u = -η ^ r := by
    rcases hru with (h | h)
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr
  · rcases hru with (h | h)
    · simp only [h, pow_zero, Set.mem_insert_iff, eq_neg_self_iff, one_ne_zero,
        Set.mem_singleton_iff, false_or, true_or]
    · simp only [h, pow_zero, Set.mem_insert_iff, neg_eq_self_iff, one_ne_zero, neg_inj,
        Set.mem_singleton_iff, true_or, or_true]
  · rcases hru with (h | h)
    · simp only [h, zero_add, pow_one, Set.mem_insert_iff, eq_neg_self_iff, Set.mem_singleton_iff,
      true_or, or_true]
    · simp only [h, zero_add, pow_one, Set.mem_insert_iff, neg_inj, neg_eq_self_iff,
      Set.mem_singleton_iff, true_or, or_true]
  · rcases hru with (h | h)
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]

/-- Let `K` be a number field such that `IsCyclotomicExtension {3} ℚ K`.
Let `ζ` be any primitive `3`-rd root of unity in `K`.
Let `η` be the element in the ring of integers corresponding to `ζ`.
Let `λ` be the element in the ring of integers corresponding to `ζ - 1`.

Then `λ ^ 2 = -3 * η`. -/
lemma lambda_sq : λ ^ 2 = -3 * η :=
  calc λ ^ 2 = η ^ 2 + η + 1 - 3 * η := by ring
  _ = 0 - 3 * η := by ext; simpa using hζ.isRoot_cyclotomic (by decide)
  _ = -3 * η := by ring

/-- Let `K` be a number field such that `IsCyclotomicExtension {3} ℚ K`.
Let `ζ` be any primitive `3`-rd root of unity in `K`.
Let `η` be the element in the ring of integers corresponding to `ζ`.
Let `λ` be the element in the ring of integers corresponding to `ζ - 1`.
Let `u` be a unit in `(𝓞 K)ˣ`.

If `u` is congruent to an integer modulo `λ ^ 2`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma*. -/
theorem eq_one_or_neg_one_of_unit_of_congruent (hcong : ∃ n : ℤ, λ ^ 2 ∣ (u - n : 𝓞 K)) :
    u = 1 ∨ u = -1 := by
  replace hcong : ∃ n : ℤ, (3 : 𝓞 K) ∣ (↑u - n : 𝓞 K) := by
    obtain ⟨n, x, hx⟩ := hcong
    exact ⟨n, -η * x, by rw [← mul_assoc, mul_neg, ← neg_mul, ← lambda_sq, hx]⟩
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have := Units.mem hζ u
  have h2 : (hζ.pow_of_coprime 2 (by decide)).toInteger = hζ.toInteger ^ 2 := by ext; simp
  simp only [Set.mem_insert_iff, val_eq_one, Set.mem_singleton_iff] at this
  rcases this with (rfl | h | h | h | h | h)
  · left; rfl
  · right; ext; simp [h]
  · exfalso
    apply hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide)
    rw [← h]
    exact hcong
  · exfalso
    apply hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add] at hx
    refine ⟨-n, -x, ?_⟩
    rw [← neg_eq_iff_eq_neg.2 h, hx]
    simp
  · exfalso
    apply (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide)
    rw [h2, ← h]
    exact hcong
  · exfalso
    apply (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, ?_⟩
    simp only [Int.cast_neg, sub_neg_eq_add, PNat.val_ofNat, Nat.cast_ofNat]
    rw [h2, mul_neg, ← hx, ← neg_eq_iff_eq_neg.2 h]
    simp only [Int.cast_neg, sub_neg_eq_add, neg_sub]
    ring
