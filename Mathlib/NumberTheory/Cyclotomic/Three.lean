/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.NumberField.Units

/-!
# Third cyclotomic field.
We gather various results about the third cyclotomic field.

## Main results
* `IsCyclotomicExtension.Rat.Three.Units.mem`: Given a unit `u : (𝓞 K)ˣ`, where `K` is a number
field such that `IsCyclotomicExtension {3} ℚ K`, then `u ∈ ({1, -1, ζ, -ζ, ζ^2, -ζ^2}`, where `ζ`
is any primitive `3`-rd root of unity in `K`.

* `IsCyclotomicExtension.Rat.Three.Units.mem.eq_one_or_neg_one_of_unit_of_congruent`: Given a unit
`u : (𝓞 K)ˣ`, where `K` is a number field such that `IsCyclotomicExtension {3} ℚ K`, if `u` is
congruent to an integer modulo `3`, then `u = 1` or `u = -1`. This is a special case of the
so-called *Kummer's lemma*.

-/

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)

local notation3 "η" => hζ.toInteger

local notation3 "λ" => hζ.toInteger - 1

local notation3 "f" => algebraMap (𝓞 K) (𝓞 K ⧸ Ideal.span {λ})

/-- Given a unit `u : (𝓞 K)ˣ`, where `K` is a number field such that
`IsCyclotomicExtension {3} ℚ K`, then `u ∈ ({1, -1, ζ, -ζ, ζ^2, -ζ^2}`, where `ζ` is any
primitive `3`-rd root of unity in `K`. -/
theorem Units.mem : ↑u ∈({1, -1, η, -η, η ^ 2, -η ^ 2} : Set (𝓞 K)) := by
  have hrank : rank K = 0 := by
    dsimp [rank]
    rw [card_eq_NrRealPlaces_add_NrComplexPlaces, nrRealPlaces_eq_zero (n := 3) K (by decide),
      zero_add, nrComplexPlaces_eq_totient_div_two (n := 3)]
    rfl
  obtain ⟨x, ⟨_, hxu, -⟩, -⟩ := exist_unique_eq_mul_prod _ u
  replace hxu : u = x := by
    rw [← mul_one x.1]
    convert hxu
    convert Finset.prod_empty.symm
    rw [Finset.univ_eq_empty_iff, hrank]
    infer_instance
  obtain ⟨n, hnpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.1 <| (CommGroup.mem_torsion _ _).1 x.2
  replace hn : (↑u : K) ^ ((⟨n, hnpos⟩ : ℕ+) : ℕ) = 1 := by
    norm_cast
    simp [hxu, hn]
  have hodd : Odd ((3 : ℕ+) : ℕ) := by decide
  obtain ⟨r, hr3, hru⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hodd
    (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hn⟩)
  replace hr : r ∈ Finset.Ico 0 3 := Finset.mem_Ico.2 ⟨by simp, hr3⟩
  replace hru : ↑u = η ^ r ∨ ↑u = -η ^ r := by
    rcases hru with (h | h)
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr
  · rcases hru with (h | h) <;> simp [h]
  · rcases hru with (h | h) <;> simp [h]
  · rcases hru with (h | h)
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]

theorem Units.not_exists_int_three_dvd_sub : ¬(∃ n : ℤ, (3 : 𝓞 K) ∣ (η - n : 𝓞 K)) := by
  intro ⟨n, x, h⟩
  let pB := hζ.integralPowerBasis'
  have hdim : pB.dim = 2 := by
    simp only [IsPrimitiveRoot.power_basis_int'_dim, PNat.val_ofNat, Nat.reduceSucc, pB]
    rfl
  replace hdim : 1 < pB.dim := by simp [hdim]
  rw [sub_eq_iff_eq_add] at h
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasis'_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this, show pB.gen = pB.gen ^ (⟨1, hdim⟩: Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (3 : 𝓞 K) * x = (3 : ℤ) • x by simp, ← pB.basis.coord_apply,
    LinearMap.map_smul, ← zsmul_one, ← pB.basis.coord_apply, LinearMap.map_smul,
    show 1 = pB.gen ^ (⟨0, by linarith⟩: Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.coord_apply, pB.basis.coord_apply, pB.basis.repr_self_apply] at h
  simp only [smul_eq_mul, Fin.mk.injEq, zero_ne_one, ↓reduceIte, mul_zero, add_zero] at h
  have hdvd : ¬ ((3 : ℤ) ∣ 1) := by norm_num
  apply hdvd
  exact ⟨_, h⟩

lemma lambda_sq : λ ^ 2 = -3 * η :=
  calc λ ^ 2 = η ^ 2 + η + 1 - 3 * η := by ring
  _ = 0 - 3 * η := by ext; simpa using hζ.isRoot_cyclotomic (by decide)
  _ = -3 * η := by ring

/-- Given a unit `u : (𝓞 K)ˣ`, where `K` is a number field such that
`IsCyclotomicExtension {3} ℚ K`, if `u` is congruent to an integer modulo `λ ^ 2`, then `u = 1` or
`u = -1`.

This is a special case of the so-called *Kummer's lemma*. -/
theorem eq_one_or_neg_one_of_unit_of_congruent (hcong : ∃ n : ℤ, λ ^ 2 ∣ (↑u - n : 𝓞 K)) :
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
    apply Units.not_exists_int_three_dvd_sub hζ
    rw [← h]
    exact hcong
  · exfalso
    apply Units.not_exists_int_three_dvd_sub hζ
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add] at hx
    refine ⟨-n, -x, ?_⟩
    rw [← neg_eq_iff_eq_neg.2 h, hx]
    simp
  · exfalso
    apply Units.not_exists_int_three_dvd_sub <| hζ.pow_of_coprime 2 (by decide)
    rw [h2, ← h]
    exact hcong
  · exfalso
    apply Units.not_exists_int_three_dvd_sub <| hζ.pow_of_coprime 2 (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, ?_⟩
    rw [h2, mul_neg, ← hx, ← neg_eq_iff_eq_neg.2 h]
    simp only [Int.cast_neg, sub_neg_eq_add, neg_sub]
    ring

noncomputable
instance : Fintype (𝓞 K ⧸ Ideal.span {λ}) := by
  refine Ideal.fintypeQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero, ← Subtype.coe_inj] at h
  exact hζ.ne_one (by decide) h

lemma norm_lambda : Algebra.norm ℤ λ = 3 := by
  apply (algebraMap ℤ ℚ).injective_int
  have : algebraMap (𝓞 K) K λ = ζ - 1 := by
    simp only [map_sub, map_one, sub_left_inj]
    exact rfl
  rw [← Algebra.norm_localization (Sₘ := K) ℤ ℤ⁰, this, hζ.sub_one_norm_prime
    (cyclotomic.irreducible_rat (n := 3) (by decide)) (by decide)]
  simp

lemma norm_lambda_prime : Prime (Algebra.norm ℤ λ) := by
  rw [norm_lambda]
  exact Int.prime_three

lemma lambda_dvd_three : λ ∣ 3 := by
  suffices λ ∣ (3 : ℤ) by simpa
  rw [← Ideal.norm_dvd_iff, norm_lambda hζ]
  rw [norm_lambda hζ]
  exact Int.prime_three

lemma lambda_not_unit : ¬ IsUnit λ := by
  intro h
  rw [isUnit_iff_dvd_one, show (1 : 𝓞 K) = ((1 : ℤ) : 𝓞 K) by simp, show η - ((1 : ℤ) : 𝓞 K) = λ
    by simp, ← Ideal.norm_dvd_iff (norm_lambda_prime hζ), norm_lambda hζ] at h
  have h3 : ¬((3 : ℤ) ∣ 1) := by decide
  exact h3 h

lemma card_quot : Fintype.card (𝓞 K ⧸ Ideal.span {λ}) = 3 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  simp [norm_lambda hζ]

lemma two_ne_zero : (2 : 𝓞 K ⧸ Ideal.span {λ}) ≠ 0 := by
  suffices 2 ∉ Ideal.span {λ} by
    intro h
    refine this (Ideal.Quotient.eq_zero_iff_mem.1 <| by simp [h])
  intro h
  rw [Ideal.mem_span_singleton] at h
  replace h : λ ∣ ↑(2 : ℤ) := by simp [h]
  rw [← Ideal.norm_dvd_iff, norm_lambda hζ] at h
  · norm_num at h
  · rw [norm_lambda hζ]
    exact Int.prime_three

lemma lambda_not_dvd_two : ¬ λ ∣ 2 := by
  intro h
  exact two_ne_zero hζ (Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 h)

instance : Nontrivial (𝓞 K ⧸ Ideal.span {λ}) := nontrivial_of_ne 2 0 <| two_ne_zero hζ

open Classical Finset in
lemma univ_quot : (univ : Finset ((𝓞 K ⧸ Ideal.span {λ}))) = {0, 1, -1} := by
  refine (eq_of_subset_of_card_le (fun _ _ ↦ mem_univ _) ?_).symm
  rw [card_univ, card_quot hζ, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
  · rw [mem_singleton]
    intro h
    rw [← add_eq_zero_iff_eq_neg, one_add_one_eq_two] at h
    exact two_ne_zero hζ h
  · intro h
    simp only [mem_insert, mem_singleton, zero_eq_neg] at h
    rcases h with (h | h)
    · exact zero_ne_one h
    · exact zero_ne_one h.symm

lemma dvd_or_dvd_sub_one_or_dvd_add_one (x : 𝓞 K) : λ ∣ x ∨ λ ∣ x - 1 ∨ λ ∣ x + 1 := by
  have := Finset.mem_univ (Ideal.Quotient.mk (Ideal.span {λ}) x)
  rw [univ_quot hζ] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with (h | h | h)
  · left
    exact Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 h
  · right; left
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_sub, h, RingHom.map_one, sub_self]
  · right; right
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_add, h, RingHom.map_one, add_left_neg]

lemma _root_.IsPrimitiveRoot.toInteger_coe : hζ.toInteger.1 = ζ := rfl

lemma _root_.IsPrimitiveRoot.toInteger_cube_eq_one : η ^ 3 = 1 := by
  ext
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact hζ.pow_eq_one

lemma _root_.IsPrimitiveRoot.eta_isUnit : IsUnit η :=
  isUnit_of_mul_eq_one _ (η ^ 2) (by simp [← pow_succ, hζ.toInteger_cube_eq_one])

lemma _root_.IsPrimitiveRoot.toInteger_eval_cyclo : η ^ 2 + η + 1 = 0 := by
  ext; simpa using hζ.isRoot_cyclotomic (by decide)

lemma cube_sub_one (x : 𝓞 K) : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) := by
  symm
  calc _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + η ^ 3) - η ^ 3 := by ring
  _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + 1) - 1 := by rw [hζ.toInteger_cube_eq_one]
  _ = x ^ 3 - 1 := by rw [hζ.toInteger_eval_cyclo]; ring

lemma lambda_dvd_mul_sub_one_mul_sub_eta_add_one (x : 𝓞 K) :
    λ ∣ x * (x - 1) * (x - (η + 1)) := by
  rcases dvd_or_dvd_sub_one_or_dvd_add_one hζ x with (h | h | h)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · refine dvd_mul_of_dvd_right ?_ _
    rw [show x - (η + 1) = x + 1 - (η - 1 + 3) by ring]
    exact dvd_sub h (dvd_add dvd_rfl <| lambda_dvd_three hζ)

lemma lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : λ ∣ x - 1) :
    λ ^ 4 ∣ x ^ 3 - 1 := by
  obtain ⟨y, hy⟩ := h
  have : x ^ 3 - 1 = λ ^ 3 * (y * (y - 1) * (y - (η + 1))) := by
    calc _ =  (x - 1) * (x - 1 - λ) * (x - 1 - λ * (η + 1)) := by rw [cube_sub_one hζ x]; ring
    _ = _ := by rw [hy]; ring
  rw [this, show λ ^ 4 = λ ^ 3 * λ by ring]
  exact mul_dvd_mul dvd_rfl (lambda_dvd_mul_sub_one_mul_sub_eta_add_one hζ y)

lemma lambda_pow_four_dvd_cube_add_one_of_dvd_add_one {x : 𝓞 K} (h : λ ∣ x + 1) :
    λ ^ 4 ∣ x ^ 3 + 1 := by
  replace h : λ ∣ -x - 1 := by
    obtain ⟨y, hy⟩ := h
    refine ⟨-y, ?_⟩
    rw [mul_neg, ← hy]
    ring
  obtain ⟨y, hy⟩ := lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ h
  refine ⟨-y, ?_⟩
  rw [mul_neg, ← hy]
  ring

lemma lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd {x : 𝓞 K} (h : ¬ λ ∣ x) :
    λ ^ 4 ∣ x ^ 3 - 1 ∨ λ ^ 4 ∣ x ^ 3 + 1 := by
  rcases dvd_or_dvd_sub_one_or_dvd_add_one hζ x with (H | H | H)
  · contradiction
  · left
    exact lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ H
  · right
    exact lambda_pow_four_dvd_cube_add_one_of_dvd_add_one hζ H

end IsCyclotomicExtension.Rat.Three
