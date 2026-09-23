module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.QuadraticField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open Ideal

open scoped QuadraticAlgebra

open Polynomial in
/-- The `discrim` of `a`, `b`, `c` is the discriminant of the polynomial `a * X ^ 2 + b * X + c`. -/
theorem discrim_eq_polynomial_discr {R : Type*} [CommRing R] (a b c : R) (ha : a ≠ 0) :
    discrim a b c = (C a * X ^ 2 + C b * X + C c).discr := by
  rw [discr_of_degree_eq_two (by compute_degree!), discrim]
  simp [mul_right_comm]

-- TODO: for `Mathlib/Algebra/QuadraticAlgebra/Int.lean`, to replace `discr_intCast`, which is
-- this for `R = ℚ`; its eight call sites should then use this one, and the prime can go.
/-- The discriminant commutes with the coercion `ℤ → R`. -/
@[simp, norm_cast]
theorem QuadraticAlgebra.discr_intCast' {R : Type*} [CommRing R] (a b : ℤ) :
    discr (a : R) (b : R) = ((discr a b : ℤ) : R) := by
  simpa using discr_algebraMap (S := R) a b

-- TODO: for `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean`, next to
-- `not_dvd_discr_iff_forall_liesOver`, of which this is the contrapositive in terms of `e`.
open scoped NumberField Ideal in
/-- A prime divides the discriminant exactly when some prime above it is ramified. -/
theorem NumberField.dvd_discr_iff_exists_two_le_ramificationIdx (K 𝒪 : Type*) [Field K]
    [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [IsDedekindDomain 𝒪]
    [CharZero 𝒪] [Module.Finite ℤ 𝒪] [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    p ∣ discr K ↔
      ∃ P : Ideal 𝒪, P.IsMaximal ∧ P.LiesOver (span {p}) ∧ 2 ≤ P.ramificationIdx ℤ := by
  rw [← not_iff_not, NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  simp only [not_exists, not_and, not_le, Order.lt_two_iff]
  exact forall₃_congr fun P _ _ ↦ by grind [ramificationIdx_eq_one_iff, ramificationIdx_pos]

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Finite (p.primesOver S)]

theorem ramificationIdx_le_finrank' (P : p.primesOver S) :
    P.1.ramificationIdx R ≤ Module.finrank R S := by
  have : Fintype (p.primesOver S) := Fintype.ofFinite (p.primesOver S)
  rw [← sum_ramification_inertia_eq_finrank p S, ← Finset.add_sum_erase _ _ (Finset.mem_univ P)]
  exact le_trans (Nat.le_mul_of_pos_right _ (inertiaDeg_pos P.1 R)) (Nat.le_add_right _ _)

end Ideal

section quadratic

open Polynomial UniqueFactorizationMonoid

variable {K : Type*} [Field K] {a b c : K}

/-- A quadratic is irreducible when its discriminant is not a square. -/
theorem irreducible_quadratic_of_not_isSquare_discrim (ha : a ≠ 0)
    (hs : ¬ IsSquare (discrim a b c)) :
    Irreducible (C a * X ^ 2 + C b * X + C c) := by
  have hd : (C a * X ^ 2 + C b * X + C c).natDegree = 2 := by compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hd]) ?_
  replace hs :  ∀ (s : K), discrim a b c ≠ s ^ 2 := by
    simpa [IsSquare, not_exists, ← pow_two] using hs
  simpa [IsRoot.def, pow_two] using quadratic_ne_zero_of_discrim_ne_sq hs

/-- If the discriminant is not a square, the only normalized factor is the monic quadratic. -/
theorem normalizedFactors_quadratic_of_not_isSquare_discrim [DecidableEq K] (ha : a ≠ 0)
    (hs : ¬ IsSquare (discrim a b c)) :
    normalizedFactors (C a * X ^ 2 + C b * X + C c) = {X ^ 2 + C (b * a⁻¹) * X + C (c * a⁻¹)} := by
  rw [normalizedFactors_irreducible (irreducible_quadratic_of_not_isSquare_discrim ha hs),
    normalize_apply, coe_normUnit, leadingCoeff_quadratic ha, CommGroupWithZero.coe_normUnit _ ha,
    add_mul, add_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul,
    mul_right_comm, ← map_mul, ← map_mul]

variable [NeZero (2 : K)] {s : K}

/-- If the discriminant is the square of `s`, the quadratic splits into the two linear factors
given by the quadratic formula. -/
theorem quadratic_eq_mul_of_discrim_eq_sq (ha : a ≠ 0) (h : discrim a b c = s ^ 2) :
    C a * X ^ 2 + C b * X + C c =
      C a * (X - C ((-b + s) / (2 * a))) * (X - C ((-b - s) / (2 * a))) := by
  polynomial_nf
  congr <;> field_simp; grind [discrim]

/-- If the discriminant is the square of `s`, the normalized factors are the two linear factors
given by the quadratic formula, equal to each other when `s = 0`. -/
theorem normalizedFactors_quadratic_of_discrim_eq_sq [DecidableEq K] (ha : a ≠ 0)
    (h : discrim a b c = s ^ 2) :
    normalizedFactors (C a * X ^ 2 + C b * X + C c) =
      {X - C ((-b + s) / (2 * a)), X - C ((-b - s) / (2 * a))} := by
  rw [quadratic_eq_mul_of_discrim_eq_sq ha h, normalizedFactors_mul
    (mul_ne_zero (C_ne_zero.mpr ha) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _),
    normalizedFactors_irreducible (irreducible_X_sub_C _),
    normalizedFactors_irreducible]
  · simp only [normalize_apply, coe_normUnit, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_X_sub_C, mul_one, CommGroupWithZero.coe_normUnit _ ha, normUnit_one, Units.val_one,
    map_one, Multiset.singleton_add, Multiset.insert_eq_cons, Multiset.cons_inj_left]
    rw [mul_rotate, mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, mul_one]
  · rw [irreducible_isUnit_mul (isUnit_C.mpr ha.isUnit)]
    exact irreducible_X_sub_C _

end quadratic

-- TODO: for `Mathlib/Algebra/QuadraticAlgebra/Defs.lean`, next to `algebraMap_im`.
/-- `ω` is not a scalar. -/
theorem QuadraticAlgebra.omega_notMem_range_algebraMap {R : Type*} [CommRing R] [Nontrivial R]
    {a b : R} :
    (ω : QuadraticAlgebra R a b) ∉ Set.range (algebraMap R (QuadraticAlgebra R a b)) :=
  fun ⟨r, hr⟩ ↦ by simpa using congr_arg im hr

-- TODO: for `Mathlib/Algebra/QuadraticAlgebra/Basic.lean`, next to `omega_mul_omega_eq_add`.
open Polynomial in
/-- The minimal polynomial of `ω` is `X ^ 2 - b * X - a`. -/
theorem QuadraticAlgebra.minpoly_omega {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {a b : R} [IsDomain (QuadraticAlgebra R a b)] :
    minpoly R (ω : QuadraticAlgebra R a b) = X ^ 2 - C b * X - C a := by
  refine (minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly (by monicity!) ?_ ?_).symm
  · simp [aeval_sub, map_pow, aeval_X, map_mul, omega_pow_two_eq_add,
      Algebra.algebraMap_eq_smul_one]
  · compute_degree
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero (Algebra.IsIntegral.isIntegral ω)),
      Nat.ofNat_le_cast, minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral ω)]
    exact QuadraticAlgebra.omega_notMem_range_algebraMap

-- TODO: for `Mathlib/RingTheory/DedekindDomain/Basic.lean`, next to
-- `Ring.DimensionLEOne.of_ringEquiv`. An `IsDedekindRing` version belongs there too.
/-- A ring isomorphic to a Dedekind domain is a Dedekind domain. -/
theorem IsDedekindDomain.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
    (e : R ≃+* S) : IsDedekindDomain R := by
  have : IsDomain R := e.toMulEquiv.isDomain S
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := .of_ringEquiv e
  have : IsIntegrallyClosed R := .of_equiv e.symm
  have : IsDedekindRing R := ⟨⟩
  exact ⟨⟩

namespace NumberField.QuadraticField

open Polynomial

variable (K : Type*) [Field K] [CharZero K] [Algebra.IsQuadraticExtension ℚ K]

/-- A chosen isomorphism between the quadratic algebra of discriminant `discr K` and `𝓞 K`. -/
noncomputable def quadraticAlgebraAlgEquiv :
    QuadraticAlgebra ℤ (discr K / 4) (discr K % 4) ≃ₐ[ℤ] 𝓞 K :=
  (nonempty_algEquiv_ringOfIntegers K).some.symm

/-- The quadratic algebra modelling `𝓞 K` is a Dedekind domain. -/
instance isDedekindDomain_quadraticAlgebra :
    IsDedekindDomain (QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) :=
  .of_ringEquiv (quadraticAlgebraAlgEquiv K).toRingEquiv

/-- A generator of `𝓞 K` over `ℤ`, pulled back from `ω`. -/
noncomputable abbrev integralGen : 𝓞 K := (quadraticAlgebraAlgEquiv K) ω

/-- `𝓞 K = ℤ[ω]`: a quadratic field is monogenic. Transport `adjoin_omega_eq_top` along
`quadraticAlgebraAlgEquiv`. -/
theorem adjoin_integralGen_eq_top : Algebra.adjoin ℤ {integralGen K} = ⊤ := by
  rw [integralGen, ← AlgEquiv.coe_toAlgHom, ← AlgHom.map_adjoin_singleton,
    QuadraticAlgebra.adjoin_omega_eq_top, Algebra.map_top,
    (AlgHom.range_eq_top _).mpr (AlgEquiv.surjective _)]

/-- The hypothesis gating the Kummer-Dedekind API holds for every prime, `2` included. -/
theorem exponent_integralGen : RingOfIntegers.exponent (integralGen K) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (adjoin_integralGen_eq_top K)

theorem not_dvd_exponent_integralGen (p : ℕ) [hp : Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent (integralGen K) := by
  rw [exponent_integralGen, Nat.dvd_one]
  exact hp.out.ne_one

/-- The minimal polynomial of the generator is the characteristic polynomial of `ω`, whose
discriminant is `discr K`. -/
theorem minpoly_integralGen :
    minpoly ℤ (integralGen K) = X ^ 2 - C (discr K % 4) * X - C (discr K / 4) := by
  rw [minpoly.algEquiv_eq (quadraticAlgebraAlgEquiv K), QuadraticAlgebra.minpoly_omega]

/-- The minimal polynomial of the generator has degree `2`. -/
theorem natDegree_minpoly_integralGen : (minpoly ℤ (integralGen K)).natDegree = 2 := by
  rw [minpoly_integralGen]
  compute_degree!

/-- The minimal polynomial of the generator is monic. -/
theorem monic_minpoly_integralGen : (minpoly ℤ (integralGen K)).Monic :=
  minpoly.monic <| RingOfIntegers.isIntegral (integralGen K)

/-- The discriminant of the minimal polynomial of the generator is `discr K`. -/
theorem discrim_minpoly_integralGen (p : ℕ) [Fact p.Prime] :
    discrim (1 : ZMod p) (-(discr K % 4 : ℤ)) (-(discr K / 4 : ℤ)) = (discr K : ZMod p) := by
  rw [discrim_eq_polynomial_discr _ _ _ one_ne_zero, map_one, one_mul, Polynomial.C_mul',
    neg_smul, ← sub_eq_add_neg, map_neg, ← sub_eq_add_neg,
    QuadraticAlgebra.polynomial_discr_eq_discr, QuadraticAlgebra.discr_intCast',
    (isFundamentalDiscr_discr K).discr_ediv_four_emod_four]

variable {K} in
/-- The fundamental identity `g * e * f = 2` for a quadratic field. -/
theorem ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg (P : Ideal (𝓞 K)) [P.IsPrime] :
    ((under ℤ P).primesOver (𝓞 K)).ncard * (P.ramificationIdx ℤ * P.inertiaDeg ℤ) = 2 := by
  rw [← ramificationIdxIn_eq_ramificationIdx (under ℤ P) P Gal(K/ℚ),
    ← inertiaDegIn_eq_inertiaDeg (under ℤ P) P Gal(K/ℚ),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ _ Gal(K/ℚ),
    IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two']

namespace KD

variable {K} (p : ℕ) [Fact p.Prime]

local notation3 "𝒑" => (span {(p : ℤ)})

section inert

open NumberField.Ideal

variable (hd : ¬ IsSquare ((discr K : ZMod p)))

include hd

/-- If the discriminant is not a square mod `p`, then `p` is inert: `f = 2` at every prime
above `p`. -/
theorem inertiaDeg_of_not_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 2 := by
  have h₀ : ¬ p ∣ RingOfIntegers.exponent (integralGen K) := not_dvd_exponent_integralGen K p
  let 𝓟 : 𝒑.primesOver (𝓞 K) := ⟨P, ⟨inferInstance, inferInstance⟩⟩
  have h₁ : RingOfIntegers.monicFactorsMod (integralGen K) p =
      {(minpoly ℤ (integralGen K)).map (Int.castRingHom (ZMod p))} := by
    simp only [RingOfIntegers.monicFactorsMod, minpoly_integralGen, eq_intCast, Polynomial.map_sub,
      Polynomial.map_pow, map_X, Polynomial.map_mul, Polynomial.map_intCast]
    rw [show X ^ 2 = C (1 : ZMod p) * X ^ 2 by rw [map_one, one_mul], ← C_eq_intCast,
      ← C_eq_intCast, sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← map_neg, ← map_neg,
      normalizedFactors_quadratic_of_not_isSquare_discrim one_ne_zero
      (by rwa [discrim_minpoly_integralGen])]
    simp
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₀ 𝓟).2
  simp only [h₁, Finset.mem_singleton] at h₂
  rw [inertiaDeg_primesOverSpanEquivMonicFactorsMod_apply h₀ 𝓟, h₂,
    Polynomial.Monic.natDegree_map (monic_minpoly_integralGen K)]
  exact natDegree_minpoly_integralGen K

/-- If the discriminant is not a square mod `p`, then `p` is inert: `e = 1` at every prime
above `p`. -/
theorem ramificationIdx_of_not_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 1 := by
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [inertiaDeg_of_not_isSquare p hd, ← mul_assoc, mul_eq_right₀ two_ne_zero] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- If the discriminant is not a square mod `p`, then `p` is inert: `g = 1`. -/
theorem ncard_primesOver_of_not_isSquare : (𝒑.primesOver (𝓞 K)).ncard = 1 := by
  obtain ⟨P, _, _⟩ := exists_isPrime_liesOver_of_faithfullyFlat 𝒑 (B := 𝓞 K)
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [inertiaDeg_of_not_isSquare p hd, ← mul_assoc, mul_eq_right₀ two_ne_zero,
    ← over_def P 𝒑] at h
  exact Nat.eq_one_of_mul_eq_one_right h

end inert

section ramified

open NumberField.Ideal

variable (hd : (p : ℤ) ∣ discr K)

include hd

/-- If `p` divides the discriminant, it is ramified: `e = 2` at every prime above `p`. -/
theorem ramificationIdx_of_dvd_discr (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 2 := by
  refine Nat.le_antisymm ?_ ?_
  · rw [← ‹Algebra.IsQuadraticExtension ℚ K›.finrank_eq_two, ← RingOfIntegers.rank K]
    exact ramificationIdx_le_finrank' 𝒑 (𝓞 K) ⟨P, ⟨hP₁, hP₂⟩⟩
  · obtain ⟨Q, _, _, _⟩ := (dvd_discr_iff_exists_two_le_ramificationIdx K (𝓞 K)
      (Nat.prime_iff_prime_int.mp Fact.out)).mp hd
    rwa [ramificationIdx_eq_of_isGaloisGroup 𝒑 P Q Gal(K/ℚ)]

/-- If `p` divides the discriminant, it is ramified: `f = 1` at every prime above `p`. -/
theorem inertiaDeg_of_dvd_discr (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 1 := by
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [ramificationIdx_of_dvd_discr p hd, mul_comm 2, ← mul_assoc, mul_eq_right₀ two_ne_zero] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- If `p` divides the discriminant, it is ramified: `g = 1`. -/
theorem ncard_primesOver_of_dvd_discr : (𝒑.primesOver (𝓞 K)).ncard = 1 := by
  obtain ⟨P, _, _⟩ := exists_isPrime_liesOver_of_faithfullyFlat 𝒑 (B := 𝓞 K)
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [ramificationIdx_of_dvd_discr p hd, mul_comm 2, ← mul_assoc, mul_eq_right₀ two_ne_zero,
    ← over_def P 𝒑] at h
  exact Nat.eq_one_of_mul_eq_one_right h

end ramified

section split


open NumberField.Ideal

variable (hp2 : p ≠ 2) (hnd : ¬ (p : ℤ) ∣ discr K)
  (hd : IsSquare ((discr K : ZMod p)))

include hp2 hnd hd

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `g = 2`. -/
theorem ncard_primesOver_of_isSquare : (𝒑.primesOver (𝓞 K)).ncard = 2 := by
  have :  NeZero (2 : ZMod p) := ⟨Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])⟩
  obtain ⟨s, hs⟩ := hd
  have h₀ :  discrim (1 : ZMod p) (-(discr K % 4 : ℤ)) (-↑(discr K / 4 : ℤ)) = s ^ 2 := by
    rwa [discrim_minpoly_integralGen, pow_two]
  have h₁ : ¬ p ∣ RingOfIntegers.exponent (integralGen K) := not_dvd_exponent_integralGen K p
  rw [← Nat.card_coe_set_eq, Nat.card_congr (primesOverSpanEquivMonicFactorsMod h₁),
    RingOfIntegers.monicFactorsMod, minpoly_integralGen]
  simp only [eq_intCast, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_mul,
    Polynomial.map_intCast, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [show X ^ 2 = C (1 : ZMod p) * X ^ 2 by rw [map_one, one_mul], ← C_eq_intCast,
    ← C_eq_intCast, sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← map_neg, ← map_neg,
    normalizedFactors_quadratic_of_discrim_eq_sq one_ne_zero h₀, Multiset.insert_eq_cons,
    Multiset.toFinset_cons, Multiset.toFinset_singleton, Finset.card_pair]
  rw [ne_eq, sub_right_inj, C_inj, mul_one, div_left_inj' two_ne_zero, sub_eq_add_neg,
    add_right_inj]
  refine fun h ↦ hnd ?_
  rw [eq_comm, Ring.eq_self_iff_eq_zero_of_char_ne_two (by rwa [ZMod.ringChar_zmod_n])] at h
  rwa [h, zero_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at hs

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `e = 1` at every prime
above `p`. -/
theorem ramificationIdx_of_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 1 := by
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [← over_def P 𝒑, ncard_primesOver_of_isSquare p hp2 hnd hd, mul_eq_left₀ two_ne_zero] at h
  exact Nat.eq_one_of_mul_eq_one_right h

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `f = 1` at every prime
above `p`. -/
theorem inertiaDeg_of_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 1 := by
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [← over_def P 𝒑, ncard_primesOver_of_isSquare p hp2 hnd hd, mul_eq_left₀ two_ne_zero] at h
  exact Nat.eq_one_of_mul_eq_one_left h

end split

section two

open NumberField.Ideal

/-- `2` is inert exactly when `discr K % 8 = 5`: `f = 2` at every prime above `2`. -/
theorem inertiaDeg_two_of_discr_emod_eight (h : discr K % 8 = 5)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.inertiaDeg ℤ = 2 := by
  have h₁ : ¬ 2 ∣ RingOfIntegers.exponent (integralGen K) := not_dvd_exponent_integralGen K 2
  have h₂ : (discr K / 4 : ℤ) = ((1 : ℤ) : ZMod 2) := by
    rw [ZMod.intCast_eq_intCast_iff']
    grind
  have h₃ : discr K % 4 = 1 := by grind
  have hd : (X ^ 2 - X - (1 : (ZMod 2)[X])).natDegree = 2 := by compute_degree!
  have h₄ : RingOfIntegers.monicFactorsMod (integralGen K) 2 =
      {X ^ 2 - X - 1} := by
    rw [RingOfIntegers.monicFactorsMod, minpoly_integralGen]
    simp only [h₃, map_one, one_mul, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      Int.coe_castRingHom, h₂, Int.cast_one]
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible,
      Monic.normalize_eq_self (by monicity!),
      Multiset.toFinset_singleton]
    exact Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hd])
      (by simp [IsRoot.def])
  let 𝓟 : (span {(2 : ℤ)}).primesOver (𝓞 K) := ⟨P, ⟨inferInstance, inferInstance⟩⟩
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ 𝓟).2
  simp only [h₄, Finset.mem_singleton] at h₂
  rw [inertiaDeg_primesOverSpanEquivMonicFactorsMod_apply h₁ 𝓟, h₂, hd]

/-- `2` is inert exactly when `discr K % 8 = 5`: `e = 1` at every prime above `2`. -/
theorem ramificationIdx_two_of_discr_emod_eight_five (h : discr K % 8 = 5)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 1 := by
  have h' := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [inertiaDeg_two_of_discr_emod_eight h, ← mul_assoc, mul_eq_right₀ two_ne_zero] at h'
  exact Nat.eq_one_of_mul_eq_one_left h'

/-- `2` is inert exactly when `discr K % 8 = 5`: `g = 1`. -/
theorem ncard_primesOver_two_of_discr_emod_eight_five (h : discr K % 8 = 5) :
    ((span {(2 : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by
  have : (span {(2 : ℤ)}).IsPrime := (span_singleton_prime two_ne_zero).mpr Int.prime_two
  obtain ⟨P, _, _⟩ := exists_isPrime_liesOver_of_faithfullyFlat (span {(2 : ℤ)}) (B := 𝓞 K)
  have h' := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [inertiaDeg_two_of_discr_emod_eight h, ← mul_assoc, mul_eq_right₀ two_ne_zero,
    ← over_def P (span {(2 : ℤ)})] at h'
  exact Nat.eq_one_of_mul_eq_one_right h'

open UniqueFactorizationMonoid in
/-- `2` splits exactly when `discr K % 8 = 1`: `g = 2`. -/
theorem ncard_primesOver_two_of_discr_emod_eight_one (h : discr K % 8 = 1) :
    ((span {(2 : ℤ)}).primesOver (𝓞 K)).ncard = 2 := by
  have h₁ : ¬ 2 ∣ RingOfIntegers.exponent (integralGen K) := not_dvd_exponent_integralGen K 2
  have h₂ : (discr K / 4 : ℤ) = (0 : ZMod 2) := by
    grind [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  have h₃ : discr K % 4 = 1 := by grind
  rw [show (2 : ℤ) = (2 : ℕ) by rfl, ← Nat.card_coe_set_eq,
    Nat.card_congr (primesOverSpanEquivMonicFactorsMod h₁), RingOfIntegers.monicFactorsMod,
    minpoly_integralGen, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_mul, map_X, Polynomial.map_C, Polynomial.map_C, eq_intCast, h₃, eq_intCast, h₂,
    map_zero, sub_zero, Int.cast_one, map_one, one_mul,
    show (X : (ZMod 2)[X]) ^ 2 - X = X * (X - C 1) by polynomial,
    normalizedFactors_mul X_ne_zero (X_sub_C_ne_zero 1),
    normalizedFactors_irreducible (irreducible_X_sub_C 1),
    normalizedFactors_irreducible (irreducible_X), Multiset.singleton_add, Nat.card_eq_finsetCard,
    Multiset.toFinset_cons, Multiset.toFinset_singleton, Finset.card_pair]
  rw [(monic_X_sub_C 1).normalize_eq_self, (monic_X).normalize_eq_self]
  grind

/-- `2` splits exactly when `discr K % 8 = 1`: `e = 1` at every prime above `2`. -/
theorem ramificationIdx_two_of_discr_emod_eight_one (h : discr K % 8 = 1)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 1 := by
  have h' := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [← over_def P (span {(2 : ℤ)}), ncard_primesOver_two_of_discr_emod_eight_one h,
    mul_eq_left₀ two_ne_zero] at h'
  exact Nat.eq_one_of_mul_eq_one_right h'

/-- `2` splits exactly when `discr K % 8 = 1`: `f = 1` at every prime above `2`. -/
theorem inertiaDeg_two_of_discr_emod_eight_one (h : discr K % 8 = 1)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.inertiaDeg ℤ = 1 := by
  have h' := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [← over_def P (span {(2 : ℤ)}), ncard_primesOver_two_of_discr_emod_eight_one h,
    mul_eq_left₀ two_ne_zero] at h'
  exact Nat.eq_one_of_mul_eq_one_left h'

end two

end KD

end NumberField.QuadraticField
