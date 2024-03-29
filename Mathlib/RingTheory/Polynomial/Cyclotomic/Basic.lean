/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Polynomial.Lifts
import Mathlib.Data.Polynomial.Splits
import Mathlib.FieldTheory.RatFunc
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.RingTheory.RootsOfUnity.Basic

#align_import ring_theory.polynomial.cyclotomic.basic from "leanprover-community/mathlib"@"7fdeecc0d03cd40f7a165e6cf00a4d2286db599f"

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


open scoped BigOperators Polynomial

noncomputable section

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : R[X] :=
  ∏ μ in primitiveRoots n R, (X - C μ)
#align polynomial.cyclotomic' Polynomial.cyclotomic'

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic'_zero (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 0 R = 1 := by
  simp only [cyclotomic', Finset.prod_empty, primitiveRoots_zero]
#align polynomial.cyclotomic'_zero Polynomial.cyclotomic'_zero

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic'_one (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 1 R = X - 1 := by
  simp only [cyclotomic', Finset.prod_singleton, RingHom.map_one,
    IsPrimitiveRoot.primitiveRoots_one]
#align polynomial.cyclotomic'_one Polynomial.cyclotomic'_one

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp]
theorem cyclotomic'_two (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [CharP R p] (hp : p ≠ 2) :
    cyclotomic' 2 R = X + 1 := by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one p hp, fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  simp only [prim_root_two, Finset.prod_singleton, RingHom.map_neg, RingHom.map_one, sub_neg_eq_add]
#align polynomial.cyclotomic'_two Polynomial.cyclotomic'_two

/-- `cyclotomic' n R` is monic. -/
theorem cyclotomic'.monic (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
#align polynomial.cyclotomic'.monic Polynomial.cyclotomic'.monic

/-- `cyclotomic' n R` is different from `0`. -/
theorem cyclotomic'_ne_zero (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' n R ≠ 0 :=
  (cyclotomic'.monic n R).ne_zero
#align polynomial.cyclotomic'_ne_zero Polynomial.cyclotomic'_ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
theorem natDegree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).natDegree = Nat.totient n := by
  rw [cyclotomic']
  rw [natDegree_prod (primitiveRoots n R) fun z : R => X - C z]
  simp only [IsPrimitiveRoot.card_primitiveRoots h, mul_one, natDegree_X_sub_C, Nat.cast_id,
    Finset.sum_const, nsmul_eq_mul]
  intro z _
  exact X_sub_C_ne_zero z
#align polynomial.nat_degree_cyclotomic' Polynomial.natDegree_cyclotomic'

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
theorem degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).degree = Nat.totient n := by
  simp only [degree_eq_natDegree (cyclotomic'_ne_zero n R), natDegree_cyclotomic' h]
#align polynomial.degree_cyclotomic' Polynomial.degree_cyclotomic'

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
theorem roots_of_cyclotomic (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).roots = (primitiveRoots n R).val := by
  rw [cyclotomic']; exact roots_prod_X_sub_C (primitiveRoots n R)
#align polynomial.roots_of_cyclotomic Polynomial.roots_of_cyclotomic

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
theorem X_pow_sub_one_eq_prod {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    X ^ n - 1 = ∏ ζ in nthRootsFinset n R, (X - C ζ) := by
  classical
  rw [nthRootsFinset, ← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  simp only [Finset.prod_mk, RingHom.map_one]
  rw [nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@natDegree_X_pow_sub_C R _ _ n 1, ← nthRoots]
  exact IsPrimitiveRoot.card_nthRoots_one h
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_one_eq_prod Polynomial.X_pow_sub_one_eq_prod

end IsDomain

section Field

variable {K : Type*} [Field K]

/-- `cyclotomic' n K` splits. -/
theorem cyclotomic'_splits (n : ℕ) : Splits (RingHom.id K) (cyclotomic' n K) := by
  apply splits_prod (RingHom.id K)
  intro z _
  simp only [splits_X_sub_C (RingHom.id K)]
#align polynomial.cyclotomic'_splits Polynomial.cyclotomic'_splits

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1` splits. -/
theorem X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    Splits (RingHom.id K) (X ^ n - C (1 : K)) := by
  rw [splits_iff_card_roots, ← nthRoots, IsPrimitiveRoot.card_nthRoots_one h, natDegree_X_pow_sub_C]
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_one_splits Polynomial.X_pow_sub_one_splits

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in Nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
theorem prod_cyclotomic'_eq_X_pow_sub_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    ∏ i in Nat.divisors n, cyclotomic' i K = X ^ n - 1 := by
  classical
  have hd : (n.divisors : Set ℕ).PairwiseDisjoint fun k => primitiveRoots k K :=
    fun x _ y _ hne => IsPrimitiveRoot.disjoint hne
  simp only [X_pow_sub_one_eq_prod hpos h, cyclotomic', ← Finset.prod_biUnion hd,
    h.nthRoots_one_eq_biUnion_primitiveRoots]
set_option linter.uppercaseLean3 false in
#align polynomial.prod_cyclotomic'_eq_X_pow_sub_one Polynomial.prod_cyclotomic'_eq_X_pow_sub_one

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in Nat.properDivisors k, cyclotomic' i K)`. -/
theorem cyclotomic'_eq_X_pow_sub_one_div {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    cyclotomic' n K = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomic' i K := by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  rw [(div_modByMonic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  refine' ⟨by rw [mul_comm], _⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic'_eq_X_pow_sub_one_div Polynomial.cyclotomic'_eq_X_pow_sub_one_div

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
theorem int_coeff_of_cyclotomic' {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (h : IsPrimitiveRoot ζ n) : ∃ P : ℤ[X], map (Int.castRingHom K) P =
      cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.Monic := by
  refine' lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K)
  induction' n using Nat.strong_induction_on with k ihk generalizing ζ
  rcases k.eq_zero_or_pos with (rfl | hpos)
  · use 1
    simp only [cyclotomic'_zero, coe_mapRingHom, Polynomial.map_one]
  let B : K[X] := ∏ i in Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  have Bint : B ∈ lifts (Int.castRingHom K) := by
    refine' Subsemiring.prod_mem (lifts (Int.castRingHom K)) _
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
    · simpa only [degree_zero, bot_lt_iff_ne_bot, Ne.def, degree_eq_bot] using Bmo.ne_zero
  replace huniq := div_modByMonic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [lifts, RingHom.mem_rangeS]
  use Q₁
  rw [coe_mapRingHom, map_divByMonic (Int.castRingHom K) hB₁mo, hB₁, ← huniq.1]
  simp
#align polynomial.int_coeff_of_cyclotomic' Polynomial.int_coeff_of_cyclotomic'

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
theorem unique_int_coeff_of_cycl {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ζ : K}
    {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    ∃! P : ℤ[X], map (Int.castRingHom K) P = cyclotomic' n K := by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine' ⟨P, hP.1, fun Q hQ => _⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1, hQ]
#align polynomial.unique_int_coeff_of_cycl Polynomial.unique_int_coeff_of_cycl

end Field

end Cyclotomic'

section Cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose
#align polynomial.cyclotomic Polynomial.cyclotomic

theorem int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
    cyclotomic n ℤ = (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose := by
  simp only [cyclotomic, h, dif_neg, not_false_iff]
  ext i
  simp only [coeff_map, Int.cast_id, eq_intCast]
#align polynomial.int_cyclotomic_rw Polynomial.int_cyclotomic_rw

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
theorem map_cyclotomic_int (n : ℕ) (R : Type*) [Ring R] :
    map (Int.castRingHom R) (cyclotomic n ℤ) = cyclotomic n R := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, dif_pos, Polynomial.map_one]
  simp [cyclotomic, hzero]
#align polynomial.map_cyclotomic_int Polynomial.map_cyclotomic_int

theorem int_cyclotomic_spec (n : ℕ) :
    map (Int.castRingHom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
      (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).Monic := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
      eq_self_iff_true, Polynomial.map_one, and_self_iff]
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n hzero)).choose_spec
#align polynomial.int_cyclotomic_spec Polynomial.int_cyclotomic_spec

theorem int_cyclotomic_unique {n : ℕ} {P : ℤ[X]} (h : map (Int.castRingHom ℂ) P = cyclotomic' n ℂ) :
    P = cyclotomic n ℤ := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [h, (int_cyclotomic_spec n).1]
#align polynomial.int_cyclotomic_unique Polynomial.int_cyclotomic_unique

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp]
theorem map_cyclotomic (n : ℕ) {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    map f (cyclotomic n R) = cyclotomic n S := by
  rw [← map_cyclotomic_int n R, ← map_cyclotomic_int n S, map_map]
  congr!
#align polynomial.map_cyclotomic Polynomial.map_cyclotomic

theorem cyclotomic.eval_apply {R S : Type*} (q : R) (n : ℕ) [Ring R] [Ring S] (f : R →+* S) :
    eval (f q) (cyclotomic n S) = f (eval q (cyclotomic n R)) := by
  rw [← map_cyclotomic n f, eval_map, eval₂_at_apply]
#align polynomial.cyclotomic.eval_apply Polynomial.cyclotomic.eval_apply

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic_zero (R : Type*) [Ring R] : cyclotomic 0 R = 1 := by
  simp only [cyclotomic, dif_pos]
#align polynomial.cyclotomic_zero Polynomial.cyclotomic_zero

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic_one (R : Type*) [Ring R] : cyclotomic 1 R = X - 1 := by
  have hspec : map (Int.castRingHom ℂ) (X - 1) = cyclotomic' 1 ℂ := by
    simp only [cyclotomic'_one, PNat.one_coe, map_X, Polynomial.map_one, Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int, ← int_cyclotomic_unique hspec]
  simp only [map_X, Polynomial.map_one, Polynomial.map_sub]
#align polynomial.cyclotomic_one Polynomial.cyclotomic_one

/-- `cyclotomic n` is monic. -/
theorem cyclotomic.monic (n : ℕ) (R : Type*) [Ring R] : (cyclotomic n R).Monic := by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _
#align polynomial.cyclotomic.monic Polynomial.cyclotomic.monic

/-- `cyclotomic n` is primitive. -/
theorem cyclotomic.isPrimitive (n : ℕ) (R : Type*) [CommRing R] : (cyclotomic n R).IsPrimitive :=
  (cyclotomic.monic n R).isPrimitive
#align polynomial.cyclotomic.is_primitive Polynomial.cyclotomic.isPrimitive

/-- `cyclotomic n R` is different from `0`. -/
theorem cyclotomic_ne_zero (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] : cyclotomic n R ≠ 0 :=
  (cyclotomic.monic n R).ne_zero
#align polynomial.cyclotomic_ne_zero Polynomial.cyclotomic_ne_zero

/-- The degree of `cyclotomic n` is `totient n`. -/
theorem degree_cyclotomic (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).degree = Nat.totient n := by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom R) _]
  · cases' n with k
    · simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, CharP.cast_eq_zero]
    rw [← degree_cyclotomic' (Complex.isPrimitiveRoot_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
  simp only [(int_cyclotomic_spec n).right.right, eq_intCast, Monic.leadingCoeff, Int.cast_one,
    Ne.def, not_false_iff, one_ne_zero]
#align polynomial.degree_cyclotomic Polynomial.degree_cyclotomic

/-- The natural degree of `cyclotomic n` is `totient n`. -/
theorem natDegree_cyclotomic (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).natDegree = Nat.totient n := by
  rw [natDegree, degree_cyclotomic]; norm_cast
#align polynomial.nat_degree_cyclotomic Polynomial.natDegree_cyclotomic

/-- The degree of `cyclotomic n R` is positive. -/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type*) (hpos : 0 < n) [Ring R] [Nontrivial R] :
    0 < (cyclotomic n R).degree := by
  rw [degree_cyclotomic n R, Nat.cast_pos]; exact Nat.totient_pos hpos
#align polynomial.degree_cyclotomic_pos Polynomial.degree_cyclotomic_pos

open Finset

/-- `∏ i in Nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type*) [CommRing R] :
    ∏ i in Nat.divisors n, cyclotomic i R = X ^ n - 1 := by
  have integer : ∏ i in Nat.divisors n, cyclotomic i ℤ = X ^ n - 1 := by
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective
    simp only [Polynomial.map_prod, int_cyclotomic_spec, Polynomial.map_pow, map_X,
      Polynomial.map_one, Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.isPrimitiveRoot_exp n hpos.ne')
  simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) integer
set_option linter.uppercaseLean3 false in
#align polynomial.prod_cyclotomic_eq_X_pow_sub_one Polynomial.prod_cyclotomic_eq_X_pow_sub_one

theorem cyclotomic.dvd_X_pow_sub_one (n : ℕ) (R : Type*) [Ring R] :
    cyclotomic n R ∣ X ^ n - 1 := by
  suffices cyclotomic n ℤ ∣ X ^ n - 1 by
    simpa only [map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X] using map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn]
  exact Finset.dvd_prod_of_mem _ (n.mem_divisors_self hn.ne')
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic.dvd_X_pow_sub_one Polynomial.cyclotomic.dvd_X_pow_sub_one

theorem prod_cyclotomic_eq_geom_sum {n : ℕ} (h : 0 < n) (R) [CommRing R] :
    ∏ i in n.divisors.erase 1, cyclotomic i R = ∑ i in Finset.range n, X ^ i := by
  suffices (∏ i in n.divisors.erase 1, cyclotomic i ℤ) = ∑ i in Finset.range n, X ^ i by
    simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) this
  rw [← mul_left_inj' (cyclotomic_ne_zero 1 ℤ), prod_erase_mul _ _ (Nat.one_mem_divisors.2 h.ne'),
    cyclotomic_one, geom_sum_mul, prod_cyclotomic_eq_X_pow_sub_one h]
#align polynomial.prod_cyclotomic_eq_geom_sum Polynomial.prod_cyclotomic_eq_geom_sum

/-- If `p` is prime, then `cyclotomic p R = ∑ i in range p, X ^ i`. -/
theorem cyclotomic_prime (R : Type*) [Ring R] (p : ℕ) [hp : Fact p.Prime] :
    cyclotomic p R = ∑ i in Finset.range p, X ^ i := by
  suffices cyclotomic p ℤ = ∑ i in range p, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      congr_arg (map (Int.castRingHom R)) this
  rw [← prod_cyclotomic_eq_geom_sum hp.out.pos, hp.out.divisors,
    erase_insert (mem_singleton.not.2 hp.out.ne_one.symm), prod_singleton]
#align polynomial.cyclotomic_prime Polynomial.cyclotomic_prime

theorem cyclotomic_prime_mul_X_sub_one (R : Type*) [Ring R] (p : ℕ) [hn : Fact (Nat.Prime p)] :
    cyclotomic p R * (X - 1) = X ^ p - 1 := by rw [cyclotomic_prime, geom_sum_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic_prime_mul_X_sub_one Polynomial.cyclotomic_prime_mul_X_sub_one

@[simp]
theorem cyclotomic_two (R : Type*) [Ring R] : cyclotomic 2 R = X + 1 := by simp [cyclotomic_prime]
#align polynomial.cyclotomic_two Polynomial.cyclotomic_two

@[simp]
theorem cyclotomic_three (R : Type*) [Ring R] : cyclotomic 3 R = X ^ 2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ']
#align polynomial.cyclotomic_three Polynomial.cyclotomic_three

theorem cyclotomic_dvd_geom_sum_of_dvd (R) [Ring R] {d n : ℕ} (hdn : d ∣ n) (hd : d ≠ 1) :
    cyclotomic d R ∣ ∑ i in Finset.range n, X ^ i := by
  suffices cyclotomic d ℤ ∣ ∑ i in Finset.range n, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [hd, hdn, hn.ne']
#align polynomial.cyclotomic_dvd_geom_sum_of_dvd Polynomial.cyclotomic_dvd_geom_sum_of_dvd

theorem X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : ℕ}
    (h : d ∈ n.properDivisors) :
    ((X ^ d - 1) * ∏ x in n.divisors \ d.divisors, cyclotomic x R) = X ^ n - 1 := by
  obtain ⟨hd, hdn⟩ := Nat.mem_properDivisors.mp h
  have h0n : 0 < n := pos_of_gt hdn
  have h0d : 0 < d := Nat.pos_of_dvd_of_pos hd h0n
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d, ← prod_cyclotomic_eq_X_pow_sub_one h0n, mul_comm,
    Finset.prod_sdiff (Nat.divisors_subset_of_dvd h0n.ne' hd)]
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd

theorem X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : ℕ}
    (h : d ∈ n.properDivisors) : (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1 := by
  have hdn := (Nat.mem_properDivisors.mp h).2
  use ∏ x in n.properDivisors \ d.divisors, cyclotomic x R
  symm
  convert X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h using 1
  rw [mul_assoc]
  congr 1
  rw [← Nat.insert_self_properDivisors hdn.ne_bot, insert_sdiff_of_not_mem, prod_insert]
  · exact Finset.not_mem_sdiff_of_not_mem_left Nat.properDivisors.not_self_mem
  · exact fun hk => hdn.not_le <| Nat.divisor_le hk
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd Polynomial.X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd

section ArithmeticFunction

open ArithmeticFunction

open scoped ArithmeticFunction

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `R[X]`
  using Möbius inversion. -/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (R : Type*) [CommRing R]
    [IsDomain R] : algebraMap _ (RatFunc R) (cyclotomic n R) =
      ∏ i in n.divisorsAntidiagonal, algebraMap R[X] _ (X ^ i.snd - 1) ^ μ i.fst := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  have h : ∀ n : ℕ, 0 < n → (∏ i in Nat.divisors n, algebraMap _ (RatFunc R) (cyclotomic i R)) =
      algebraMap _ _ (X ^ n - 1 : R[X]) := by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R, map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    simp_rw [Ne.def, IsFractionRing.to_map_eq_zero_iff]
  · simp [cyclotomic_ne_zero]
  · intro n hn
    apply Monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gt hn)
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius

end ArithmeticFunction

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in Nat.properDivisors k, cyclotomic i K)`. -/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) :
    cyclotomic n R = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomic i R := by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos, ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
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
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic_eq_X_pow_sub_one_div Polynomial.cyclotomic_eq_X_pow_sub_one_div

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i in Nat.properDivisors n, cyclotomic i R`. -/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [CommRing R] {n m : ℕ} (hpos : 0 < n)
    (hm : m ∣ n) (hdiff : m ≠ n) : X ^ m - 1 ∣ ∏ i in Nat.properDivisors n, cyclotomic i R := by
  replace hm := Nat.mem_properDivisors.2
    ⟨hm, lt_of_le_of_ne (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, hpos.ne'⟩)) hdiff⟩
  rw [← Finset.sdiff_union_of_subset (Nat.divisors_subset_properDivisors (ne_of_lt hpos).symm
    (Nat.mem_properDivisors.1 hm).1 (ne_of_lt (Nat.mem_properDivisors.1 hm).2)),
    Finset.prod_union Finset.sdiff_disjoint,
    prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_properDivisors hm)]
  exact ⟨∏ x : ℕ in n.properDivisors \ m.divisors, cyclotomic x R, by rw [mul_comm]⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_one_dvd_prod_cyclotomic Polynomial.X_pow_sub_one_dvd_prod_cyclotomic

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitiveRoots n K, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
theorem cyclotomic_eq_prod_X_sub_primitiveRoots {K : Type*} [CommRing K] [IsDomain K] {ζ : K}
    {n : ℕ} (hz : IsPrimitiveRoot ζ n) : cyclotomic n K = ∏ μ in primitiveRoots n K, (X - C μ) := by
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
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic_eq_prod_X_sub_primitive_roots Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots

theorem eq_cyclotomic_iff {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) (P : R[X]) :
    P = cyclotomic n R ↔
    (P * ∏ i in Nat.properDivisors n, Polynomial.cyclotomic i R) = X ^ n - 1 := by
  nontriviality R
  refine' ⟨fun hcycl => _, fun hP => _⟩
  · rw [hcycl, ← prod_cyclotomic_eq_X_pow_sub_one hpos R, ← Nat.cons_self_properDivisors hpos.ne',
      Finset.prod_cons]
  · have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i _
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos, (div_modByMonic_unique P 0 prod_monic _).1]
    refine' ⟨by rwa [zero_add, mul_comm], _⟩
    rw [degree_zero, bot_lt_iff_ne_bot]
    intro h
    exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)
#align polynomial.eq_cyclotomic_iff Polynomial.eq_cyclotomic_iff

/-- If `p ^ k` is a prime power, then
`cyclotomic (p ^ (n + 1)) R = ∑ i in range p, (X ^ (p ^ n)) ^ i`. -/
theorem cyclotomic_prime_pow_eq_geom_sum {R : Type*} [CommRing R] {p n : ℕ} (hp : p.Prime) :
    cyclotomic (p ^ (n + 1)) R = ∑ i in Finset.range p, (X ^ p ^ n) ^ i := by
  have : ∀ m, (cyclotomic (p ^ (m + 1)) R = ∑ i in Finset.range p, (X ^ p ^ m) ^ i) ↔
      ((∑ i in Finset.range p, (X ^ p ^ m) ^ i) *
        ∏ x : ℕ in Finset.range (m + 1), cyclotomic (p ^ x) R) = X ^ p ^ (m + 1) - 1 := by
    intro m
    have := eq_cyclotomic_iff (R := R) (P := ∑ i in range p, (X ^ p ^ m) ^ i)
      (pow_pos hp.pos (m + 1))
    rw [eq_comm] at this
    rw [this, Nat.prod_properDivisors_prime_pow hp]
  induction' n with n_n n_ih
  · haveI := Fact.mk hp; simp [cyclotomic_prime]
  rw [((eq_cyclotomic_iff (pow_pos hp.pos (n_n.succ + 1)) _).mpr _).symm]
  rw [Nat.prod_properDivisors_prime_pow hp, Finset.prod_range_succ, n_ih]
  rw [this] at n_ih
  rw [mul_comm _ (∑ i in _, _), n_ih, geom_sum_mul, sub_left_inj, ← pow_mul, pow_add, pow_one]
#align polynomial.cyclotomic_prime_pow_eq_geom_sum Polynomial.cyclotomic_prime_pow_eq_geom_sum

theorem cyclotomic_prime_pow_mul_X_pow_sub_one (R : Type*) [CommRing R] (p k : ℕ)
    [hn : Fact (Nat.Prime p)] :
    cyclotomic (p ^ (k + 1)) R * (X ^ p ^ k - 1) = X ^ p ^ (k + 1) - 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_mul, ← pow_mul, pow_succ, mul_comm]
set_option linter.uppercaseLean3 false in
#align polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
theorem cyclotomic_coeff_zero (R : Type*) [CommRing R] {n : ℕ} (hn : 1 < n) :
    (cyclotomic n R).coeff 0 = 1 := by
  induction' n using Nat.strong_induction_on with n hi
  have hprod : (∏ i in Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_properDivisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn)), Finset.prod_insert (Finset.not_mem_erase 1 _),
      cyclotomic_one R]
    have hleq : ∀ j ∈ n.properDivisors.erase 1, 2 ≤ j := by
      intro j hj
      apply Nat.succ_le_of_lt
      exact (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
        (Nat.succ_le_of_lt (Nat.pos_of_mem_properDivisors (Finset.mem_erase.1 hj).2))
    have hcongr : ∀ j ∈ n.properDivisors.erase 1, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_properDivisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x : ℕ in n.properDivisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
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
#align polynomial.cyclotomic_coeff_zero Polynomial.cyclotomic_coeff_zero

/-- If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
theorem coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) : a.Coprime p := by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (ZMod.nat_cast_zmod_eq_zero_iff_dvd a p).2 h
  rw [IsRoot.definition, eq_natCast, h, ← coeff_zero_eq_eval_zero] at hroot
  by_cases hone : n = 1
  · simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
      one_ne_zero, coeff_sub] at hroot
  rw [cyclotomic_coeff_zero (ZMod p) (Nat.succ_le_of_lt
    (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hone)))] at hroot
  exact one_ne_zero hroot
#align polynomial.coprime_of_root_cyclotomic Polynomial.coprime_of_root_cyclotomic

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
  rw [IsRoot.definition] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (ZMod p), ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons, eval_mul, hroot, zero_mul]
#align polynomial.order_of_root_cyclotomic_dvd Polynomial.orderOf_root_cyclotomic_dvd

end Order

end Polynomial
