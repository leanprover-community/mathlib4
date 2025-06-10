/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `Polynomial.degree_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i`
  divides `n`.
* `Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `R[X]`.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `unique_int_coeff_of_cycl`, with `R = ℂ`,
to get a polynomial with integer coefficients and then we map it to `R[X]`, for any ring `R`.
-/


open scoped Polynomial

noncomputable section

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : R[X] :=
  ∏ μ ∈ primitiveRoots n R, (X - C μ)

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic'_zero (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 0 R = 1 := by
  simp only [cyclotomic', Finset.prod_empty, primitiveRoots_zero]

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic'_one (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 1 R = X - 1 := by
  simp only [cyclotomic', Finset.prod_singleton, RingHom.map_one,
    IsPrimitiveRoot.primitiveRoots_one]

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
-- Cannot be @[simp] because `p` can not be inferred by `simp`.
theorem cyclotomic'_two (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [CharP R p] (hp : p ≠ 2) :
    cyclotomic' 2 R = X + 1 := by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one p hp, fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  simp only [prim_root_two, Finset.prod_singleton, RingHom.map_neg, RingHom.map_one, sub_neg_eq_add]

/-- `cyclotomic' n R` is monic. -/
theorem cyclotomic'.monic (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
theorem cyclotomic'_ne_zero (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' n R ≠ 0 :=
  (cyclotomic'.monic n R).ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
theorem natDegree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).natDegree = Nat.totient n := by
  rw [cyclotomic']
  rw [natDegree_prod (primitiveRoots n R) fun z : R => X - C z]
  · simp only [IsPrimitiveRoot.card_primitiveRoots h, mul_one, natDegree_X_sub_C, Nat.cast_id,
      Finset.sum_const, nsmul_eq_mul]
  intro z _
  exact X_sub_C_ne_zero z

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
theorem degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).degree = Nat.totient n := by
  simp only [degree_eq_natDegree (cyclotomic'_ne_zero n R), natDegree_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
theorem roots_of_cyclotomic (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).roots = (primitiveRoots n R).val := by
  rw [cyclotomic']; exact roots_prod_X_sub_C (primitiveRoots n R)

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
theorem X_pow_sub_one_eq_prod {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    X ^ n - 1 = ∏ ζ ∈ nthRootsFinset n (1 : R), (X - C ζ) := by
  classical
  rw [nthRootsFinset, ← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  simp only [Finset.prod_mk, RingHom.map_one]
  rw [nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@natDegree_X_pow_sub_C R _ _ n 1, ← nthRoots]
  exact IsPrimitiveRoot.card_nthRoots_one h

end IsDomain

section Field

variable {K : Type*} [Field K]

/-- `cyclotomic' n K` splits. -/
theorem cyclotomic'_splits (n : ℕ) : Splits (RingHom.id K) (cyclotomic' n K) := by
  apply splits_prod (RingHom.id K)
  intro z _
  simp only [splits_X_sub_C (RingHom.id K)]

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1` splits. -/
theorem X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    Splits (RingHom.id K) (X ^ n - C (1 : K)) := by
  rw [splits_iff_card_roots, ← nthRoots, IsPrimitiveRoot.card_nthRoots_one h, natDegree_X_pow_sub_C]

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i ∈ Nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
theorem prod_cyclotomic'_eq_X_pow_sub_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    ∏ i ∈ Nat.divisors n, cyclotomic' i K = X ^ n - 1 := by
  classical
  have hd : (n.divisors : Set ℕ).PairwiseDisjoint fun k => primitiveRoots k K :=
    fun x _ y _ hne => IsPrimitiveRoot.disjoint hne
  simp only [X_pow_sub_one_eq_prod hpos h, cyclotomic', ← Finset.prod_biUnion hd,
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i ∈ Nat.properDivisors k, cyclotomic' i K)`. -/
theorem cyclotomic'_eq_X_pow_sub_one_div {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    cyclotomic' n K = (X ^ n - 1) /ₘ ∏ i ∈ Nat.properDivisors n, cyclotomic' i K := by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons]
  have prod_monic : (∏ i ∈ Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  rw [(div_modByMonic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  refine ⟨by rw [mul_comm], ?_⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
theorem int_coeff_of_cyclotomic' {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (h : IsPrimitiveRoot ζ n) : ∃ P : ℤ[X], map (Int.castRingHom K) P =
      cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.Monic := by
  refine lifts_and_degree_eq_and_monic ?_ (cyclotomic'.monic n K)
  induction' n using Nat.strong_induction_on with k ihk generalizing ζ
  rcases k.eq_zero_or_pos with (rfl | hpos)
  · use 1
    simp only [cyclotomic'_zero, coe_mapRingHom, Polynomial.map_one]
  let B : K[X] := ∏ i ∈ Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  have Bint : B ∈ lifts (Int.castRingHom K) := by
    refine Subsemiring.prod_mem (lifts (Int.castRingHom K)) ?_
    intro x hx
    have xsmall := (Nat.mem_properDivisors.1 hx).2
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hx).1
    rw [mul_comm] at hd
    exact ihk x xsmall (h.pow hpos hd)
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo
  obtain ⟨B₁, hB₁, _, hB₁mo⟩ := Bint
  let Q₁ : ℤ[X] := (X ^ k - 1) /ₘ B₁
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree := by
    constructor
    · rw [zero_add, mul_comm, ← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ←
        Nat.cons_self_properDivisors hpos.ne', Finset.prod_cons]
    · simpa only [degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot] using Bmo.ne_zero
  replace huniq := div_modByMonic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [lifts, RingHom.mem_rangeS]
  use Q₁
  rw [coe_mapRingHom, map_divByMonic (Int.castRingHom K) hB₁mo, hB₁, ← huniq.1]
  simp

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
theorem unique_int_coeff_of_cycl {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ζ : K}
    {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    ∃! P : ℤ[X], map (Int.castRingHom K) P = cyclotomic' n K := by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine ⟨P, hP.1, fun Q hQ => ?_⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1, hQ]

end Field

end Cyclotomic'

section Cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose

theorem int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
    cyclotomic n ℤ = (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose := by
  simp only [cyclotomic, h, dif_neg, not_false_iff]
  ext i
  simp only [coeff_map, Int.cast_id, eq_intCast]

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
theorem map_cyclotomic_int (n : ℕ) (R : Type*) [Ring R] :
    map (Int.castRingHom R) (cyclotomic n ℤ) = cyclotomic n R := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, dif_pos, Polynomial.map_one]
  simp [cyclotomic, hzero]

theorem int_cyclotomic_spec (n : ℕ) :
    map (Int.castRingHom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
      (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).Monic := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
      eq_self_iff_true, Polynomial.map_one, and_self_iff]
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n hzero)).choose_spec

theorem int_cyclotomic_unique {n : ℕ} {P : ℤ[X]} (h : map (Int.castRingHom ℂ) P = cyclotomic' n ℂ) :
    P = cyclotomic n ℤ := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [h, (int_cyclotomic_spec n).1]

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp]
theorem map_cyclotomic (n : ℕ) {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    map f (cyclotomic n R) = cyclotomic n S := by
  rw [← map_cyclotomic_int n R, ← map_cyclotomic_int n S, map_map]
  have : Subsingleton (ℤ →+* S) := inferInstance
  congr!

theorem cyclotomic.eval_apply {R S : Type*} (q : R) (n : ℕ) [Ring R] [Ring S] (f : R →+* S) :
    eval (f q) (cyclotomic n S) = f (eval q (cyclotomic n R)) := by
  rw [← map_cyclotomic n f, eval_map, eval₂_at_apply]

@[simp] theorem cyclotomic.eval_apply_ofReal (q : ℝ) (n : ℕ) :
    eval (q : ℂ) (cyclotomic n ℂ) = (eval q (cyclotomic n ℝ)) :=
  cyclotomic.eval_apply q n (algebraMap ℝ ℂ)

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic_zero (R : Type*) [Ring R] : cyclotomic 0 R = 1 := by
  simp only [cyclotomic, dif_pos]

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic_one (R : Type*) [Ring R] : cyclotomic 1 R = X - 1 := by
  have hspec : map (Int.castRingHom ℂ) (X - 1) = cyclotomic' 1 ℂ := by
    simp only [cyclotomic'_one, PNat.one_coe, map_X, Polynomial.map_one, Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int, ← int_cyclotomic_unique hspec]
  simp only [map_X, Polynomial.map_one, Polynomial.map_sub]

/-- `cyclotomic n` is monic. -/
theorem cyclotomic.monic (n : ℕ) (R : Type*) [Ring R] : (cyclotomic n R).Monic := by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _

/-- `cyclotomic n` is primitive. -/
theorem cyclotomic.isPrimitive (n : ℕ) (R : Type*) [CommRing R] : (cyclotomic n R).IsPrimitive :=
  (cyclotomic.monic n R).isPrimitive

/-- `cyclotomic n R` is different from `0`. -/
theorem cyclotomic_ne_zero (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] : cyclotomic n R ≠ 0 :=
  (cyclotomic.monic n R).ne_zero

/-- The degree of `cyclotomic n` is `totient n`. -/
theorem degree_cyclotomic (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).degree = Nat.totient n := by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom R) _]
  · rcases n with - | k
    · simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, CharP.cast_eq_zero]
    rw [← degree_cyclotomic' (Complex.isPrimitiveRoot_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
  simp only [(int_cyclotomic_spec n).right.right, eq_intCast, Monic.leadingCoeff, Int.cast_one,
    Ne, not_false_iff, one_ne_zero]

/-- The natural degree of `cyclotomic n` is `totient n`. -/
theorem natDegree_cyclotomic (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).natDegree = Nat.totient n := by
  rw [natDegree, degree_cyclotomic]; norm_cast

/-- The degree of `cyclotomic n R` is positive. -/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type*) (hpos : 0 < n) [Ring R] [Nontrivial R] :
    0 < (cyclotomic n R).degree := by
  rwa [degree_cyclotomic n R, Nat.cast_pos, Nat.totient_pos]

open Finset

/-- `∏ i ∈ Nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type*) [CommRing R] :
    ∏ i ∈ Nat.divisors n, cyclotomic i R = X ^ n - 1 := by
  have integer : ∏ i ∈ Nat.divisors n, cyclotomic i ℤ = X ^ n - 1 := by
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective
    simp only [Polynomial.map_prod, int_cyclotomic_spec, Polynomial.map_pow, map_X,
      Polynomial.map_one, Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.isPrimitiveRoot_exp n hpos.ne')
  simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) integer

theorem cyclotomic.dvd_X_pow_sub_one (n : ℕ) (R : Type*) [Ring R] :
    cyclotomic n R ∣ X ^ n - 1 := by
  suffices cyclotomic n ℤ ∣ X ^ n - 1 by
    simpa only [map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X] using Polynomial.map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn]
  exact Finset.dvd_prod_of_mem _ (n.mem_divisors_self hn.ne')

theorem prod_cyclotomic_eq_geom_sum {n : ℕ} (h : 0 < n) (R) [CommRing R] :
    ∏ i ∈ n.divisors.erase 1, cyclotomic i R = ∑ i ∈ Finset.range n, X ^ i := by
  suffices (∏ i ∈ n.divisors.erase 1, cyclotomic i ℤ) = ∑ i ∈ Finset.range n, X ^ i by
    simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) this
  rw [← mul_left_inj' (cyclotomic_ne_zero 1 ℤ), prod_erase_mul _ _ (Nat.one_mem_divisors.2 h.ne'),
    cyclotomic_one, geom_sum_mul, prod_cyclotomic_eq_X_pow_sub_one h]

/-- If `p` is prime, then `cyclotomic p R = ∑ i ∈ range p, X ^ i`. -/
theorem cyclotomic_prime (R : Type*) [Ring R] (p : ℕ) [hp : Fact p.Prime] :
    cyclotomic p R = ∑ i ∈ Finset.range p, X ^ i := by
  suffices cyclotomic p ℤ = ∑ i ∈ range p, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      congr_arg (map (Int.castRingHom R)) this
  rw [← prod_cyclotomic_eq_geom_sum hp.out.pos, hp.out.divisors,
    erase_insert (mem_singleton.not.2 hp.out.ne_one.symm), prod_singleton]

theorem cyclotomic_prime_mul_X_sub_one (R : Type*) [Ring R] (p : ℕ) [hn : Fact (Nat.Prime p)] :
    cyclotomic p R * (X - 1) = X ^ p - 1 := by rw [cyclotomic_prime, geom_sum_mul]

@[simp]
theorem cyclotomic_two (R : Type*) [Ring R] : cyclotomic 2 R = X + 1 := by simp [cyclotomic_prime]

@[simp]
theorem cyclotomic_three (R : Type*) [Ring R] : cyclotomic 3 R = X ^ 2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ']

theorem cyclotomic_dvd_geom_sum_of_dvd (R) [Ring R] {d n : ℕ} (hdn : d ∣ n) (hd : d ≠ 1) :
    cyclotomic d R ∣ ∑ i ∈ Finset.range n, X ^ i := by
  suffices cyclotomic d ℤ ∣ ∑ i ∈ Finset.range n, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [hd, hdn, hn.ne']

theorem X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : ℕ}
    (h : d ∈ n.properDivisors) :
    ((X ^ d - 1) * ∏ x ∈ n.divisors \ d.divisors, cyclotomic x R) = X ^ n - 1 := by
  obtain ⟨hd, hdn⟩ := Nat.mem_properDivisors.mp h
  have h0n : 0 < n := pos_of_gt hdn
  have h0d : 0 < d := Nat.pos_of_dvd_of_pos hd h0n
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d, ← prod_cyclotomic_eq_X_pow_sub_one h0n, mul_comm,
    Finset.prod_sdiff (Nat.divisors_subset_of_dvd h0n.ne' hd)]

theorem X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : ℕ}
    (h : d ∈ n.properDivisors) : (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1 := by
  have hdn := (Nat.mem_properDivisors.mp h).2
  use ∏ x ∈ n.properDivisors \ d.divisors, cyclotomic x R
  symm
  convert X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h using 1
  rw [mul_assoc]
  congr 1
  rw [← Nat.insert_self_properDivisors hdn.ne_bot, insert_sdiff_of_notMem, prod_insert]
  · exact Finset.notMem_sdiff_of_notMem_left Nat.self_notMem_properDivisors
  · exact fun hk => hdn.not_ge <| Nat.divisor_le hk

section ArithmeticFunction

open ArithmeticFunction

open scoped ArithmeticFunction

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `R[X]`
  using Möbius inversion. -/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (R : Type*) [CommRing R]
    [IsDomain R] : algebraMap _ (RatFunc R) (cyclotomic n R) =
      ∏ i ∈ n.divisorsAntidiagonal, algebraMap R[X] _ (X ^ i.snd - 1) ^ μ i.fst := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  have h : ∀ n : ℕ, 0 < n → (∏ i ∈ Nat.divisors n, algebraMap _ (RatFunc R) (cyclotomic i R)) =
      algebraMap _ _ (X ^ n - 1 : R[X]) := by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R, map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    simp_rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  · simp [cyclotomic_ne_zero]
  · intro n hn
    apply Monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gt hn)

end ArithmeticFunction

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i ∈ Nat.properDivisors k, cyclotomic i K)`. -/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) :
    cyclotomic n R = (X ^ n - 1) /ₘ ∏ i ∈ Nat.properDivisors n, cyclotomic i R := by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos, ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons]
  have prod_monic : (∏ i ∈ Nat.properDivisors n, cyclotomic i R).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic.monic i R
  rw [(div_modByMonic_unique (cyclotomic n R) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  constructor
  · rw [mul_comm]
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i ∈ Nat.properDivisors n, cyclotomic i R`. -/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [CommRing R] {n m : ℕ} (hpos : 0 < n)
    (hm : m ∣ n) (hdiff : m ≠ n) : X ^ m - 1 ∣ ∏ i ∈ Nat.properDivisors n, cyclotomic i R := by
  replace hm := Nat.mem_properDivisors.2
    ⟨hm, lt_of_le_of_ne (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, hpos.ne'⟩)) hdiff⟩
  rw [← Finset.sdiff_union_of_subset (Nat.divisors_subset_properDivisors (ne_of_lt hpos).symm
    (Nat.mem_properDivisors.1 hm).1 (ne_of_lt (Nat.mem_properDivisors.1 hm).2)),
    Finset.prod_union Finset.sdiff_disjoint,
    prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_properDivisors hm)]
  exact ⟨∏ x ∈ n.properDivisors \ m.divisors, cyclotomic x R, by rw [mul_comm]⟩

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ ∈ primitiveRoots n K, (X - C μ)`. ∈ particular,
`cyclotomic n K = cyclotomic' n K` -/
theorem cyclotomic_eq_prod_X_sub_primitiveRoots {K : Type*} [CommRing K] [IsDomain K] {ζ : K}
    {n : ℕ} (hz : IsPrimitiveRoot ζ n) : cyclotomic n K = ∏ μ ∈ primitiveRoots n K, (X - C μ) := by
  rw [← cyclotomic']
  induction' n using Nat.strong_induction_on with k hk generalizing ζ
  obtain hzero | hpos := k.eq_zero_or_pos
  · simp only [hzero, cyclotomic'_zero, cyclotomic_zero]
  have h : ∀ i ∈ k.properDivisors, cyclotomic i K = cyclotomic' i K := by
    intro i hi
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hi).1
    rw [mul_comm] at hd
    exact hk i (Nat.mem_properDivisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos, cyclotomic'_eq_X_pow_sub_one_div hpos hz,
    Finset.prod_congr (refl k.properDivisors) h]

theorem eq_cyclotomic_iff {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) (P : R[X]) :
    P = cyclotomic n R ↔
    (P * ∏ i ∈ Nat.properDivisors n, Polynomial.cyclotomic i R) = X ^ n - 1 := by
  nontriviality R
  refine ⟨fun hcycl => ?_, fun hP => ?_⟩
  · rw [hcycl, ← prod_cyclotomic_eq_X_pow_sub_one hpos R, ← Nat.cons_self_properDivisors hpos.ne',
      Finset.prod_cons]
  · have prod_monic : (∏ i ∈ Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i _
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos, (div_modByMonic_unique P 0 prod_monic _).1]
    refine ⟨by rwa [zero_add, mul_comm], ?_⟩
    rw [degree_zero, bot_lt_iff_ne_bot]
    intro h
    exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `p ^ k` is a prime power, then
`cyclotomic (p ^ (n + 1)) R = ∑ i ∈ range p, (X ^ (p ^ n)) ^ i`. -/
theorem cyclotomic_prime_pow_eq_geom_sum {R : Type*} [CommRing R] {p n : ℕ} (hp : p.Prime) :
    cyclotomic (p ^ (n + 1)) R = ∑ i ∈ Finset.range p, (X ^ p ^ n) ^ i := by
  have : ∀ m, (cyclotomic (p ^ (m + 1)) R = ∑ i ∈ Finset.range p, (X ^ p ^ m) ^ i) ↔
      ((∑ i ∈ Finset.range p, (X ^ p ^ m) ^ i) *
        ∏ x ∈ Finset.range (m + 1), cyclotomic (p ^ x) R) = X ^ p ^ (m + 1) - 1 := by
    intro m
    have := eq_cyclotomic_iff (R := R) (P := ∑ i ∈ range p, (X ^ p ^ m) ^ i)
      (pow_pos hp.pos (m + 1))
    rw [eq_comm] at this
    rw [this, Nat.prod_properDivisors_prime_pow hp]
  induction' n with n_n n_ih
  · haveI := Fact.mk hp; simp [cyclotomic_prime]
  rw [((eq_cyclotomic_iff (pow_pos hp.pos (n_n + 1 + 1)) _).mpr _).symm]
  rw [Nat.prod_properDivisors_prime_pow hp, Finset.prod_range_succ, n_ih]
  rw [this] at n_ih
  rw [mul_comm _ (∑ i ∈ _, _), n_ih, geom_sum_mul, sub_left_inj, ← pow_mul]
  simp only [pow_add, pow_one]

theorem cyclotomic_prime_pow_mul_X_pow_sub_one (R : Type*) [CommRing R] (p k : ℕ)
    [hn : Fact (Nat.Prime p)] :
    cyclotomic (p ^ (k + 1)) R * (X ^ p ^ k - 1) = X ^ p ^ (k + 1) - 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_mul, ← pow_mul, pow_succ, mul_comm]

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
theorem cyclotomic_coeff_zero (R : Type*) [CommRing R] {n : ℕ} (hn : 1 < n) :
    (cyclotomic n R).coeff 0 = 1 := by
  induction' n using Nat.strong_induction_on with n hi
  have hprod : (∏ i ∈ Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_properDivisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn)), Finset.prod_insert (Finset.notMem_erase 1 _),
      cyclotomic_one R]
    have hleq : ∀ j ∈ n.properDivisors.erase 1, 2 ≤ j := by
      intro j hj
      apply Nat.succ_le_of_lt
      exact (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
        (Nat.succ_le_of_lt (Nat.pos_of_mem_properDivisors (Finset.mem_erase.1 hj).2))
    have hcongr : ∀ j ∈ n.properDivisors.erase 1, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_properDivisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x ∈ n.properDivisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
      rw [Finset.prod_congr (refl (n.properDivisors.erase 1)) hcongr]
      simp only [Finset.prod_const_one]
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub]
  have heq : (X ^ n - 1 : R[X]).coeff 0 = -(cyclotomic n R).coeff 0 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (zero_le_one.trans_lt hn), ←
      Nat.cons_self_properDivisors hn.ne_bot, Finset.prod_cons, mul_coeff_zero, coeff_zero_prod,
      hprod, mul_neg, mul_one]
  have hzero : (X ^ n - 1 : R[X]).coeff 0 = (-1 : R) := by
    rw [coeff_zero_eq_eval_zero _]
    simp only [zero_pow (by positivity : n ≠ 0), eval_X, eval_one, zero_sub, eval_pow, eval_sub]
  rw [hzero] at heq
  exact neg_inj.mp (Eq.symm heq)

/-- If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
theorem coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) : a.Coprime p := by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (ZMod.natCast_zmod_eq_zero_iff_dvd a p).2 h
  rw [IsRoot.def, eq_natCast, h, ← coeff_zero_eq_eval_zero] at hroot
  by_cases hone : n = 1
  · simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
      one_ne_zero, coeff_sub] at hroot
  rw [cyclotomic_coeff_zero (ZMod p) (Nat.succ_le_of_lt
    (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hone)))] at hroot
  exact one_ne_zero hroot

end Cyclotomic

section Order

/-- If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
theorem orderOf_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) :
    orderOf (ZMod.unitOfCoprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n := by
  apply orderOf_dvd_of_pow_eq_one
  suffices hpow : eval (Nat.castRingHom (ZMod p) a) (X ^ n - 1 : (ZMod p)[X]) = 0 by
    simp only [eval_X, eval_one, eval_pow, eval_sub, eq_natCast] at hpow
    apply Units.val_eq_one.1
    simp only [sub_eq_zero.mp hpow, ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
  rw [IsRoot.def] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (ZMod p), ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons, eval_mul, hroot, zero_mul]

end Order

section miscellaneous

open Finset

variable {R : Type*} [CommRing R] {ζ : R} {n : ℕ} (x y : R)

lemma dvd_C_mul_X_sub_one_pow_add_one {p : ℕ} (hpri : p.Prime)
    (hp : p ≠ 2) (a r : R) (h₁ : r ∣ a ^ p) (h₂ : r ∣ p * a) : C r ∣ (C a * X - 1) ^ p + 1 := by
  have := hpri.dvd_add_pow_sub_pow_of_dvd (C a * X) (-1) (r := C r) ?_ ?_
  · rwa [← sub_eq_add_neg, (hpri.odd_of_ne_two hp).neg_pow, one_pow, sub_neg_eq_add] at this
  · simp only [mul_pow, ← map_pow, dvd_mul_right, (_root_.map_dvd C h₁).trans]
  simp only [map_mul, map_natCast, ← mul_assoc, dvd_mul_right, (_root_.map_dvd C h₂).trans]

private theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field {K : Type*}
    [Field K] {ζ : K} (x y : K) (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    x ^ n - y ^ n = ∏ ζ ∈ nthRootsFinset n (1 : K), (x - ζ * y) := by
  by_cases hy : y = 0
  · simp only [hy, zero_pow (Nat.ne_zero_of_lt hpos), sub_zero, mul_zero, prod_const]
    congr
    rw [h.card_nthRootsFinset]
  convert congr_arg (eval (x/y) · * y ^ card (nthRootsFinset n (1 : K)))
    <| X_pow_sub_one_eq_prod hpos h
    using 1
  · simp [sub_mul, div_pow, hy, h.card_nthRootsFinset]
  · simp [eval_prod, prod_mul_pow_card, sub_mul, hy]

variable [IsDomain R]

/-- If there is a primitive `n`th root of unity in `R`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (hpos : 0 < n)
    (h : IsPrimitiveRoot ζ n) : x ^ n - y ^ n = ∏ ζ ∈ nthRootsFinset n (1 : R), (x - ζ * y) := by
  let K := FractionRing R
  apply FaithfulSMul.algebraMap_injective R K
  rw [map_sub, map_pow, map_pow, map_prod]
  simp_rw [map_sub, map_mul]
  have h' : IsPrimitiveRoot (algebraMap R K ζ) n :=
    h.map_of_injective <| FaithfulSMul.algebraMap_injective R K
  rw [h'.pow_sub_pow_eq_prod_sub_mul_field _ _ hpos]
  refine (prod_nbij (algebraMap R K) (fun a ha ↦ map_mem_nthRootsFinset_one ha _)
    (fun a _ b _ H ↦ FaithfulSMul.algebraMap_injective R K H) (fun a ha ↦ ?_) (fun _ _ ↦ rfl)).symm
  have := Set.surj_on_of_inj_on_of_ncard_le (s := nthRootsFinset n (1 : R))
    (t := nthRootsFinset n (1: K)) _ (fun _ hr ↦ map_mem_nthRootsFinset_one hr _)
    (fun a _ b _ H ↦ FaithfulSMul.algebraMap_injective R K H)
    (by simp [h.card_nthRootsFinset, h'.card_nthRootsFinset])
  obtain ⟨x, hx, hx1⟩ := this _ ha
  exact ⟨x, hx, hx1.symm⟩

/-- If there is a primitive `n`th root of unity in `R` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity. -/
theorem _root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul (hodd : Odd n)
    (h : IsPrimitiveRoot ζ n) : x ^ n + y ^ n = ∏ ζ ∈ nthRootsFinset n (1 : R), (x + ζ * y) := by
  simpa [hodd.neg_pow] using h.pow_sub_pow_eq_prod_sub_mul x (-y) hodd.pos

end miscellaneous

end Polynomial
