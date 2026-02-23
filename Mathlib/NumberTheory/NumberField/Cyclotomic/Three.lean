/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Pietro Monticone
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Fintype

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
Theorem 5.36).
-/

public section

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ)
local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

lemma coe_eta : (η : 𝓞 K) = hζ.toInteger := rfl

lemma _root_.IsPrimitiveRoot.toInteger_cube_eq_one : hζ.toInteger ^ 3 = 1 :=
  hζ.toInteger_isPrimitiveRoot.pow_eq_one

/-- Let `u` be a unit in `(𝓞 K)ˣ`, then `u ∈ [1, -1, η, -η, η^2, -η^2]`. -/
-- Here `List` is more convenient than `Finset`, even if further from the informal statement.
-- For example, `fin_cases` below does not work with a `Finset`.
theorem Units.mem [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] := by
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
    rcases hru with h | h
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr <;> rcases hru with h | h <;> simp [h]

/-- We have that `λ ^ 2 = -3 * η`. -/
private lemma lambda_sq : λ ^ 2 = -3 * η := by
  ext
  calc (λ ^ 2 : K) = η ^ 2 + η + 1 - 3 * η := by
        simp only [RingOfIntegers.map_mk, IsUnit.unit_spec]; ring
  _ = 0 - 3 * η := by simpa using hζ.isRoot_cyclotomic (by decide)
  _ = -3 * η := by ring

/-- We have that `η ^ 2 = -η - 1`. -/
lemma eta_sq : (η ^ 2 : 𝓞 K) = -η - 1 := by
  rw [← neg_add', ← add_eq_zero_iff_eq_neg, ← add_assoc]
  ext; simpa using hζ.isRoot_cyclotomic (by decide)

/-- If a unit `u` is congruent to an integer modulo `λ ^ 2`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma*. -/
theorem eq_one_or_neg_one_of_unit_of_congruent
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] (hcong : ∃ n : ℤ, λ ^ 2 ∣ (u - n : 𝓞 K)) :
    u = 1 ∨ u = -1 := by
  replace hcong : ∃ n : ℤ, (3 : 𝓞 K) ∣ (↑u - n : 𝓞 K) := by
    obtain ⟨n, x, hx⟩ := hcong
    exact ⟨n, -η * x, by rw [← mul_assoc, mul_neg, ← neg_mul, ← lambda_sq, hx]⟩
  have := Units.mem hζ u
  fin_cases this
  · left; rfl
  · right; rfl
  all_goals exfalso
  · exact hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide) hcong
  · apply hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add] at hx
    refine ⟨-n, -x, sub_eq_iff_eq_add.2 ?_⟩
    simp only [Nat.cast_ofNat, mul_neg, Int.cast_neg, ← neg_add, ← hx, Units.val_neg,
      IsUnit.unit_spec, RingOfIntegers.neg_mk, neg_neg]
  · exact (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide) hcong
  · apply (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, sub_eq_iff_eq_add.2 ?_⟩
    have : (hζ.pow_of_coprime 2 (by decide)).toInteger = hζ.toInteger ^ 2 := by ext; simp
    simp only [this, Nat.cast_ofNat, mul_neg, Int.cast_neg, ← neg_add, ← sub_eq_iff_eq_add.1 hx,
      Units.val_neg, val_pow_eq_pow_val, IsUnit.unit_spec, neg_neg]

variable (x : 𝓞 K)

set_option backward.isDefEq.respectTransparency false in
/-- Let `(x : 𝓞 K)`. Then we have that `λ` divides one amongst `x`, `x - 1` and `x + 1`. -/
lemma lambda_dvd_or_dvd_sub_one_or_dvd_add_one [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    λ ∣ x ∨ λ ∣ x - 1 ∨ λ ∣ x + 1 := by
  classical
  have := hζ.finite_quotient_toInteger_sub_one (by decide)
  let _ := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {λ})
  let _ : Ring (𝓞 K ⧸ Ideal.span {λ}) := CommRing.toRing -- to speed up instance synthesis
  let _ : AddGroup (𝓞 K ⧸ Ideal.span {λ}) := AddGroupWithOne.toAddGroup -- ditto
  have := Finset.mem_univ (Ideal.Quotient.mk (Ideal.span {λ}) x)
  have h3 : Fintype.card (𝓞 K ⧸ Ideal.span {λ}) = 3 := by
    rw [← Nat.card_eq_fintype_card, hζ.card_quotient_toInteger_sub_one,
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]
    simp only [Nat.cast_ofNat, Int.reduceAbs]
  rw [Finset.univ_of_card_le_three h3.le] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h
  · left
    exact Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 h
  · right; left
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_sub, h, RingHom.map_one, sub_self]
  · right; right
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_add, h, RingHom.map_one, neg_add_cancel]

/-- We have that `η ^ 2 + η + 1 = 0`. -/
lemma eta_sq_add_eta_add_one : (η : 𝓞 K) ^ 2 + η + 1 = 0 := by
  rw [eta_sq]
  ring

/-- We have that `x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)`. -/
lemma cube_sub_one_eq_mul : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) := by
  symm
  calc _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + η ^ 3) - η ^ 3 := by ring
  _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + 1) - 1 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = x ^ 3 - 1 := by rw [eta_sq_add_eta_add_one hζ]; ring

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- We have that `λ` divides `x * (x - 1) * (x - (η + 1))`. -/
lemma lambda_dvd_mul_sub_one_mul_sub_eta_add_one : λ ∣ x * (x - 1) * (x - (η + 1)) := by
  rcases lambda_dvd_or_dvd_sub_one_or_dvd_add_one hζ x with h | h | h
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · refine dvd_mul_of_dvd_right ?_ _
    rw [show x - (η + 1) = x + 1 - (η - 1 + 3) by ring]
    exact dvd_sub h <| dvd_add dvd_rfl hζ.toInteger_sub_one_dvd_prime'

/-- If `λ` divides `x - 1`, then `λ ^ 4` divides `x ^ 3 - 1`. -/
lemma lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : λ ∣ x - 1) :
    λ ^ 4 ∣ x ^ 3 - 1 := by
  obtain ⟨y, hy⟩ := h
  have : x ^ 3 - 1 = λ ^ 3 * (y * (y - 1) * (y - (η + 1))) := by
    calc _ = (x - 1) * (x - 1 - λ) * (x - 1 - λ * (η + 1)) := by
          simp only [coe_eta, cube_sub_one_eq_mul hζ x]; ring
    _ = _ := by rw [hy]; ring
  rw [this, pow_succ]
  exact mul_dvd_mul_left _ (lambda_dvd_mul_sub_one_mul_sub_eta_add_one hζ y)

/-- If `λ` divides `x + 1`, then `λ ^ 4` divides `x ^ 3 + 1`. -/
lemma lambda_pow_four_dvd_cube_add_one_of_dvd_add_one {x : 𝓞 K} (h : λ ∣ x + 1) :
    λ ^ 4 ∣ x ^ 3 + 1 := by
  replace h : λ ∣ -x - 1 := by
    convert h.neg_right using 1
    exact (neg_add' x 1).symm
  convert (lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ h).neg_right using 1
  ring

/-- If `λ` does not divide `x`, then `λ ^ 4` divides `x ^ 3 - 1` or `x ^ 3 + 1`. -/
lemma lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd {x : 𝓞 K} (h : ¬ λ ∣ x) :
    λ ^ 4 ∣ x ^ 3 - 1 ∨ λ ^ 4 ∣ x ^ 3 + 1 := by
  rcases lambda_dvd_or_dvd_sub_one_or_dvd_add_one hζ x with H | H | H
  · contradiction
  · left
    exact lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ H
  · right
    exact lambda_pow_four_dvd_cube_add_one_of_dvd_add_one hζ H

end Three

end Rat

end IsCyclotomicExtension
