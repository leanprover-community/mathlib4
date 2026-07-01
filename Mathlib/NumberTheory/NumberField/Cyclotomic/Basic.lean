/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.Cyclotomic.Discriminant
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Prime

/-!
# Ring of integers of cyclotomic fields
We gather results about cyclotomic extensions of `ℚ`. In particular, we compute the ring of
integers of a cyclotomic extension of `ℚ`.

## Main results
* `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`: if `K` is a cyclotomic
  extension of `ℚ`, then `adjoin ℤ {ζ}` is the integral closure of `ℤ` in `K`.
* `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure`: the integral
  closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ ℚ`.
* `IsCyclotomicExtension.Rat.discr` and related results: the absolute discriminant
  of cyclotomic fields.
-/

@[expose] public section

universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic Nat

variable {p k n : ℕ} {K : Type u} [Field K] {ζ : K} [hp : Fact p.Prime]

namespace IsCyclotomicExtension.Rat

variable [CharZero K]

variable (k K) in
theorem finrank [NeZero k] [IsCyclotomicExtension {k} ℚ K] : Module.finrank ℚ K = k.totient :=
  IsCyclotomicExtension.finrank K <| Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)

/-- The discriminant of the power basis given by `ζ - 1`. -/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hk : p ^ (k + 1) ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (NeZero.pos _)) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

theorem discr_odd_prime' [IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/-- The discriminant of the power basis given by `ζ - 1`. Beware that in the cases `p ^ k = 1` and
`p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform
result. See also `IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'`. -/
theorem discr_prime_pow' [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of the power basis given by `ζ - 1` is `u * p ^ n`. Often this is
enough and less cumbersome to use than `IsCyclotomicExtension.Rat.discr_prime_pow'`. -/
theorem discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    ∃ (u : ℤˣ) (n : ℕ), discr ℚ (hζ.subOnePowerBasis ℚ).basis = u * p ^ n := by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))

/-- If `K` is a `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the
integral closure of `ℤ` in `K`. -/
theorem isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (NeZero.pos _)))).isIntegral _)
  let B := hζ.subOnePowerBasis ℚ
  have hint : IsIntegral ℤ B.gen := (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one
  -- This can't be a `local instance` because it has metavariables.
  letI := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ K
  have H := discr_mul_isIntegral_mem_adjoin ℚ hint h
  obtain ⟨u, n, hun⟩ := discr_prime_pow_eq_unit_mul_pow' hζ
  rw [hun] at H
  replace H := Subalgebra.smul_mem _ H u.inv
  rw [← smul_assoc, ← smul_mul_assoc, Units.inv_eq_val_inv, zsmul_eq_mul, ← Int.cast_mul,
    Units.inv_mul, Int.cast_one, one_mul, smul_def, map_pow] at H
  cases k
  · haveI : IsCyclotomicExtension {1} ℚ K := by simpa using hcycl
    have : x ∈ (⊥ : Subalgebra ℚ K) := by
      rw [singleton_one ℚ K]
      exact mem_top
    obtain ⟨y, rfl⟩ := mem_bot.1 this
    replace h := (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hz, ← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ _
  · have hmin : (minpoly ℤ B.gen).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat (NeZero.pos _))
      rw [IsPrimitiveRoot.subOnePowerBasis_gen] at h₁
      rw [h₁, ← map_cyclotomic_int, ← algebraMap_int_eq,
        show X + 1 = map (algebraMap ℤ ℚ) (X + 1) by simp, ← map_comp] at h₂
      rw [IsPrimitiveRoot.subOnePowerBasis_gen,
        map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int h₂]
      exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p _
    refine
      adjoin_le ?_
        (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (n := n)
          (Nat.prime_iff_prime_int.1 hp.out) hint h (by simpa using H) hmin)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)

theorem isIntegralClosure_adjoin_singleton_of_prime [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ

set_option backward.isDefEq.respectTransparency false in
/-- The integral closure of `ℤ` inside `CyclotomicField (p ^ k) ℚ` is
`CyclotomicRing (p ^ k) ℤ ℚ`. -/
theorem cyclotomicRing_isIntegralClosure_of_prime_pow :
    IsIntegralClosure (CyclotomicRing (p ^ k) ℤ ℚ) ℤ (CyclotomicField (p ^ k) ℚ) := by
  have hζ := zeta_spec (p ^ k) ℚ (CyclotomicField (p ^ k) ℚ)
  refine ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_setOf_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {p ^ k} ℤ _).isIntegral _)

theorem cyclotomicRing_isIntegralClosure_of_prime :
    IsIntegralClosure (CyclotomicRing p ℤ ℚ) ℤ (CyclotomicField p ℚ) := by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow

end IsCyclotomicExtension.Rat

section PowerBasis

open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

section CharZero

variable [CharZero K]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p ^ k`-th root of
unity and `K` is a `p ^ k`-th cyclotomic extension of `ℚ`. -/
@[simps!]
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
    [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)

/-- The ring of integers of a `p ^ k`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance IsCyclotomicExtension.ringOfIntegersOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclotomicExtension {p ^ k} ℤ (𝓞 K) :=
  let _ := (zeta_spec (p ^ k) ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec (p ^ k) ℚ K).adjoinEquivRingOfIntegersOfPrimePow

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p ^ k`
cyclotomic extension of `ℚ`. -/
noncomputable def integralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map
    hζ.adjoinEquivRingOfIntegersOfPrimePow

/-- Abbreviation to see a primitive root of unity as a member of the ring of integers. -/
abbrev toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : 𝓞 K :=
  ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

end CharZero

lemma coe_toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.toInteger.1 = ζ := rfl

@[simp]
lemma toInteger_coe {k : ℕ} [NeZero k] {x : 𝓞 K} (hx : IsPrimitiveRoot (x : K) k) :
    hx.toInteger = x := rfl

/-- `𝓞 K ⧸ Ideal.span {ζ - 1}` is finite. -/
lemma finite_quotient_toInteger_sub_one [NumberField K] {k : ℕ} (hk : 1 < k)
    (hζ : IsPrimitiveRoot ζ k) :
    haveI : NeZero k := NeZero.of_gt hk
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one hk (RingOfIntegers.ext_iff.1 h)

/-- We have that `𝓞 K ⧸ Ideal.span {ζ - 1}` has cardinality equal to the norm of `ζ - 1`.

See the results below to compute this norm in various cases. -/
lemma card_quotient_toInteger_sub_one [NumberField K] {k : ℕ} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) :
    Nat.card (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) =
      (Algebra.norm ℤ (hζ.toInteger - 1)).natAbs := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]

lemma toInteger_isPrimitiveRoot {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot hζ.toInteger k :=
  IsPrimitiveRoot.of_map_of_injective (by exact hζ) RingOfIntegers.coe_injective

variable [CharZero K]

@[simp]
theorem integralPowerBasisOfPrimePow_gen [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.integralPowerBasisOfPrimePow.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasisOfPrimePow.gen = _ by
    rw [integralPowerBasisOfPrimePow, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegersOfPrimePow_apply, IsIntegralClosure.algebraMap_lift]
    rfl

/- We name `hcycl` so it can be used as a named argument. -/
@[simp]
theorem integralPowerBasisOfPrimePow_dim [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.integralPowerBasisOfPrimePow.dim = φ (p ^ k) := by
  simp [integralPowerBasisOfPrimePow, ← cyclotomic_eq_minpoly hζ (NeZero.pos _),
    natDegree_cyclotomic]

/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasisOfPrimePow_gen, toInteger])

@[simp]
theorem subOneIntegralPowerBasisOfPrimePow_gen [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.subOneIntegralPowerBasisOfPrimePow.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasisOfPrimePow]

/-- `ζ - 1` is prime if `p ≠ 2` and `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
theorem zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (hζ.toInteger - 1) := by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ hp.out.one_lt (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  convert! Nat.prime_iff_prime_int.1 hp.out
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ)]
  simp only [algebraMap_int_eq, map_natCast]
  exact hζ.norm_sub_one_of_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)) hodd

/-- `ζ - 1` is prime if `ζ` is a primitive `2 ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
theorem zeta_sub_one_prime_of_two_pow [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Prime (hζ.toInteger - 1) := by
  have := IsCyclotomicExtension.numberField {2 ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ (by decide) (by simp))
    rw [sub_eq_zero] at h
    simpa using! congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  cases k
  · convert! Prime.neg Int.prime_two
    apply RingHom.injective_int (algebraMap ℤ ℚ)
    rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ)]
    simp only [algebraMap_int_eq, map_neg, map_ofNat]
    simpa only [zero_add, pow_one, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
        pow_zero]
      using! hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat
        (by simp only [zero_add, pow_one, Nat.ofNat_pos]))
  convert! Int.prime_two
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), algebraMap_int_eq]
  exact hζ.norm_sub_one_two Nat.AtLeastTwo.prop (cyclotomic.irreducible_rat (by simp))

/-- `ζ - 1` is prime if `ζ` is a primitive `p ^ (k + 1)`-th root of unity. -/
theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.toInteger - 1) := by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

/-- `ζ - 1` is prime if `ζ` is a primitive `p`-th root of unity. -/
theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    Prime ((hζ.toInteger - 1)) := by
  convert! zeta_sub_one_prime (k := 0) (by simpa only [zero_add, pow_one])
  simpa only [zero_add, pow_one]

theorem subOneIntegralPowerBasisOfPrimePow_gen_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Prime hζ.subOneIntegralPowerBasisOfPrimePow.gen := by
  simpa only [subOneIntegralPowerBasisOfPrimePow_gen] using! hζ.zeta_sub_one_prime

/--
The norm, relative to `ℤ`, of `ζ - 1` in an `n`-th cyclotomic extension of `ℚ` where `n` is not a
power of a prime number is `1`.
-/
theorem norm_toInteger_sub_one_eq_one {n : ℕ} [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) (h₁ : 2 < n) (h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n) :
    have : NeZero n := NeZero.of_gt h₁
    norm ℤ (hζ.toInteger - 1) = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  have : NeZero n := NeZero.of_gt h₁
  dsimp only
  rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl, map_sub, map_one, map_one, RingOfIntegers.map_mk,
    sub_one_norm_eq_eval_cyclotomic hζ h₁ (cyclotomic.irreducible_rat (NeZero.pos _)),
    eval_one_cyclotomic_not_prime_pow h₂, Int.cast_one]

/-- The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ^ (k - s + 1) ≠ 2`. -/
lemma norm_toInteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : ℕ} (hs : s ≤ k) (htwo : p ^ (k - s + 1) ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl]
  simp [hζ.norm_pow_sub_one_of_prime_pow_ne_two (cyclotomic.irreducible_rat (NeZero.pos _)) hs htwo]

/-- The norm, relative to `ℤ`, of `ζ ^ 2 ^ k - 1` in a `2 ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `(-2) ^ 2 ^ k`. -/
lemma norm_toInteger_pow_sub_one_of_two [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Algebra.norm ℤ (hζ.toInteger ^ 2 ^ k - 1) = (-2) ^ 2 ^ k := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 1)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl]
  simp [hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat (pow_pos (by decide) _))]

/-- The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ≠ 2`. -/
lemma norm_toInteger_pow_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : ℕ} (hs : s ≤ k) (hodd : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  refine hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two hs (fun h ↦ hodd ?_)
  apply eq_of_prime_pow_eq hp.out.prime Nat.prime_two.prime (k - s).succ_pos
  rwa [pow_one]

/--
The norm, relative to `ℤ`, of `ζ - 1` in a `2 ^ (k + 2)`-th cyclotomic extension of `ℚ` is `2`.
-/
theorem norm_toInteger_sub_one_of_eq_two_pow {k : ℕ} {K : Type*} [Field K]
    {ζ : K} [CharZero K] [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    norm ℤ (hζ.toInteger - 1) = 2 := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 2)} ℚ K
  rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl, map_sub, map_one, eq_intCast, Int.cast_ofNat,
    RingOfIntegers.map_mk, hζ.norm_sub_one_two (Nat.le_add_left 2 k)
    (Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos _))]

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
`p` if `p ≠ 2`. -/
lemma norm_toInteger_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger - 1) = p := by
  simpa only [pow_zero, pow_one] using
    hζ.norm_toInteger_pow_sub_one_of_prime_ne_two (Nat.zero_le _) hodd

/--
The norm, relative to `ℤ`, of `ζ - 1` in a `2`-th cyclotomic extension of `ℚ` is `-2`.
-/
theorem norm_toInteger_sub_one_of_eq_two [IsCyclotomicExtension {2} ℚ K]
    (hζ : IsPrimitiveRoot ζ 2) :
    norm ℤ (hζ.toInteger - 1) = -2 := by
  rw [show 2 = (2 ^ (0 + 1)) by norm_num] at hζ
  simpa using hζ.norm_toInteger_pow_sub_one_of_two

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p`-th cyclotomic extension of `ℚ` is `p` if
`p ≠ 2`. -/
lemma norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) (h : p ≠ 2) : Algebra.norm ℤ (hζ.toInteger - 1) = p := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.norm_toInteger_sub_one_of_prime_ne_two h

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
a prime if `p ^ (k  + 1) ≠ 2`. -/
lemma prime_norm_toInteger_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  simp only [pow_zero, pow_one] at this
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
a prime if `p ≠ 2`. -/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p`-th cyclotomic extension of `ℚ` is a prime if
`p ≠ 2`. -/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.prime_norm_toInteger_sub_one_of_prime_ne_two hodd

/-- In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to an
  integer modulo `p` if `p ^ (k  + 1) ≠ 2`. -/
theorem not_exists_int_prime_dvd_sub_of_prime_pow_ne_two
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) ≠ 2) :
    ¬(∃ n : ℤ, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  intro ⟨n, x, h⟩
  -- Let `pB` be the power basis of `𝓞 K` given by powers of `ζ`.
  let pB := hζ.integralPowerBasisOfPrimePow
  have hdim : pB.dim = p ^ k * (↑p - 1) := by
    simp [integralPowerBasisOfPrimePow_dim, pB, Nat.totient_prime_pow hp.1 (Nat.zero_lt_succ k)]
  replace hdim : 1 < pB.dim := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one, hdim]
    refine ⟨by simp only [ne_eq, mul_eq_zero, NeZero.ne _, Nat.sub_eq_zero_iff_le, false_or,
      not_le, Nat.Prime.one_lt hp.out], ne_of_gt ?_⟩
    by_cases hk : k = 0
    · simp only [hk, zero_add, pow_one, pow_zero, one_mul, Nat.lt_sub_iff_add_lt,
        Nat.reduceAdd] at htwo ⊢
      exact htwo.symm.lt_of_le hp.1.two_le
    · exact one_lt_mul_of_lt_of_le (one_lt_pow₀ hp.1.one_lt hk)
        (have := Nat.Prime.two_le hp.out; by lia)
  rw [sub_eq_iff_eq_add] at h
  -- We are assuming that `ζ = n + p * x` for some integer `n` and `x : 𝓞 K`. Looking at the
  -- coordinates in the base `pB`, we obtain that `1` is a multiple of `p`, contradiction.
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasisOfPrimePow_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this, show pB.gen = pB.gen ^ (⟨1, hdim⟩ : Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (p : 𝓞 K) * x = (p : ℤ) • x by simp, ← pB.basis.coord_apply,
    map_smul, ← zsmul_one, ← pB.basis.coord_apply, map_smul,
    show 1 = pB.gen ^ (⟨0, by lia⟩ : Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.coord_apply, pB.basis.coord_apply, pB.basis.repr_self_apply] at h
  simp only [smul_eq_mul, Fin.mk.injEq, zero_ne_one, ↓reduceIte, mul_zero, add_zero] at h
  exact (Int.prime_iff_natAbs_prime.2 (by simp [hp.1])).not_dvd_one ⟨_, h⟩

/-- In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to an
  integer modulo `p` if `p ≠ 2`. -/
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    ¬(∃ n : ℤ, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  refine not_exists_int_prime_dvd_sub_of_prime_pow_ne_two hζ (fun h ↦ ?_)
  simp_all only [(@Nat.Prime.pow_eq_iff 2 p (k + 1) Nat.prime_two).mp (by assumption_mod_cast),
    pow_one, ne_eq]

/-- In a `p`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to an
  integer modulo `p` if `p ≠ 2`. -/
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two'
    [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    ¬(∃ n : ℤ, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact not_exists_int_prime_dvd_sub_of_prime_ne_two hζ hodd

theorem finite_quotient_span_sub_one [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one (one_lt_pow₀ hp.1.one_lt (Nat.zero_ne_add_one k).symm)
    (RingOfIntegers.ext_iff.1 h)

theorem finite_quotient_span_sub_one' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) :
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.finite_quotient_span_sub_one

/-- In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`, we have that
  `ζ - 1` divides `p` in `𝓞 K`. -/
lemma toInteger_sub_one_dvd_prime [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ((hζ.toInteger - 1)) ∣ p := by
  by_cases htwo : p ^ (k + 1) = 2
  · have ⟨hp2, hk⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 htwo
    simp only [add_eq_right] at hk
    have hζ' : ζ = -1 := by
      refine IsPrimitiveRoot.eq_neg_one_of_two_right ?_
      rwa [hk, zero_add, pow_one, hp2] at hζ
    replace hζ' : hζ.toInteger = -1 := by
      ext
      exact hζ'
    rw [hζ', hp2]
    exact ⟨-1, by ring⟩
  suffices (hζ.toInteger - 1) ∣ (p : ℤ) by simpa
  have := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  have H := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  rw [pow_zero, pow_one] at H
  rw [← Ideal.norm_dvd_iff, H]
  · simp
  · exact prime_norm_toInteger_sub_one_of_prime_pow_ne_two hζ htwo

/-- In a `p`-th cyclotomic extension of `ℚ`, we have that `ζ - 1` divides `p` in `𝓞 K`. -/
lemma toInteger_sub_one_dvd_prime' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : hζ.toInteger - 1 ∣ p := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact toInteger_sub_one_dvd_prime hζ

/-- We have that `hζ.toInteger - 1` does not divide `2`. -/
lemma toInteger_sub_one_not_dvd_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) : ¬ hζ.toInteger - 1 ∣ 2 := fun h ↦ by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  replace h : hζ.toInteger - 1 ∣ (2 : ℤ) := by simp [h]
  rw [← Ideal.norm_dvd_iff, hζ.norm_toInteger_sub_one_of_prime_ne_two hodd] at h
  · refine hodd <| (prime_dvd_prime_iff_eq ?_ ?_).1 ?_
    · exact Nat.prime_iff.1 hp.1
    · exact Nat.prime_iff.1 Nat.prime_two
    · exact Int.ofNat_dvd.mp h
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two hodd]
    exact Nat.prime_iff_prime_int.1 hp.1

open IntermediateField in
/--
Let `ζ` be a primitive root of unity of order `n` with `2 ≤ n`. Any prime number that divides the
norm, relative to `ℤ`, of `ζ - 1` divides also `n`.
-/
theorem prime_dvd_of_dvd_norm_sub_one {n : ℕ} (hn : 2 ≤ n) {K : Type*}
    [Field K] [NumberField K] {ζ : K} {p : ℕ} [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveRoot ζ n)
    (hp : haveI : NeZero n := NeZero.of_gt hn; (p : ℤ) ∣ norm ℤ (hζ.toInteger - 1)) :
    p ∣ n := by
  have : NeZero n := NeZero.of_gt hn
  obtain ⟨μ, hC, hμ, h⟩ :
      ∃ μ : ℚ⟮ζ⟯, ∃ (_ : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯), ∃ (hμ : IsPrimitiveRoot μ n),
      norm ℤ (hζ.toInteger - 1) = norm ℤ (hμ.toInteger - 1) ^ Module.finrank ℚ⟮ζ⟯ K := by
    refine ⟨IntermediateField.AdjoinSimple.gen ℚ ζ,
      intermediateField_adjoin_isCyclotomicExtension ℚ hζ, coe_submonoidClass_iff.mp hζ, ?_⟩
    have : NumberField ℚ⟮ζ⟯ := of_intermediateField _
    rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl, map_sub, map_one, RingOfIntegers.map_mk,
      show ζ - 1 = algebraMap ℚ⟮ζ⟯ K (IntermediateField.AdjoinSimple.gen ℚ ζ - 1) by rfl,
      ← norm_norm (S := ℚ⟮ζ⟯), Algebra.norm_algebraMap, map_pow, map_pow, ← norm_localization ℤ
      (nonZeroDivisors ℤ) (Sₘ := ℚ⟮ζ⟯), map_sub (algebraMap _ _), RingOfIntegers.map_mk, map_one]
  rw [h] at hp
  rsuffices ⟨q, hq, t, s, ht₁, ht₂, hs⟩ :
      ∃ q, q.Prime ∧ ∃ t s, t ≠ 0 ∧ n = q ^ t ∧ (p : ℤ) ∣ (q : ℤ) ^ s := by
    obtain hn | hn := lt_or_eq_of_le hn
    · by_cases! h : ∃ q, q.Prime ∧ ∃ t, q ^ t = n
      · obtain ⟨q, hq, t, hn'⟩ := h
        have : Fact (Nat.Prime q) := ⟨hq⟩
        cases t with
        | zero => simp [← hn'] at hn
        | succ r =>
          rw [← hn'] at hC hμ
          refine ⟨q, hq, r + 1, Module.finrank (ℚ⟮ζ⟯) K, r.add_one_ne_zero, hn'.symm, ?_⟩
          by_cases hq' : q = 2
          · cases r with
            | zero =>
                rw [← hn', hq', zero_add, pow_one] at hn
                exact hn.false.elim
            | succ k =>
                rw [hq'] at hC hμ ⊢
                rwa [hμ.norm_toInteger_sub_one_of_eq_two_pow] at hp
          · rwa [hμ.norm_toInteger_sub_one_of_prime_ne_two hq'] at hp
      · rw [IsPrimitiveRoot.norm_toInteger_sub_one_eq_one hμ hn, one_pow,
          Int.natCast_dvd_ofNat, Nat.dvd_one] at hp
        · exact (Nat.Prime.ne_one hF.out hp).elim
        · exact fun {p} a k ↦ h p a k
    · rw [← hn] at hμ hC ⊢
      refine ⟨2, Nat.prime_two, 1, Module.finrank ℚ⟮ζ⟯ K, one_ne_zero, by rw [pow_one], ?_⟩
      rwa [hμ.norm_toInteger_sub_one_of_eq_two, neg_eq_neg_one_mul, mul_pow, IsUnit.dvd_mul_left
        ((isUnit_pow_iff Module.finrank_pos.ne').mpr isUnit_neg_one)] at hp
  have : p = q := by
    rw [← Int.natCast_pow, Int.natCast_dvd_natCast] at hs
    exact (Nat.prime_dvd_prime_iff_eq hF.out hq).mp (hF.out.dvd_of_dvd_pow hs)
  rw [ht₂, this]
  exact dvd_pow_self _ ht₁

end IsPrimitiveRoot

section discr

namespace IsCyclotomicExtension.Rat

open nonZeroDivisors IsPrimitiveRoot

variable (K p k)
variable [CharZero K]

set_option backward.defeqAttrib.useBackward true in
/-- We compute the absolute discriminant of a `p ^ k`-th cyclotomic field.
  Beware that in the cases `p ^ k = 1` and `p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`.
  See also the results below. -/
theorem discr_prime_pow [IsCyclotomicExtension {p ^ k} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ k} ℚ K
    NumberField.discr K =
    (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k) ℚ K
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ k} ℚ K
  let pB₁ := integralPowerBasisOfPrimePow hζ
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB₁.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  convert!
    IsCyclotomicExtension.discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _)) using 1
  · have : pB₁.dim = (IsPrimitiveRoot.powerBasis ℚ hζ).dim := by
      rw [← PowerBasis.finrank, ← PowerBasis.finrank]
      exact RingOfIntegers.rank K
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp_rw [Function.comp_apply, Module.Basis.localizationLocalization_apply, powerBasis_dim,
      PowerBasis.coe_basis, pB₁, integralPowerBasisOfPrimePow_gen]
    convert! ← ((IsPrimitiveRoot.powerBasis ℚ hζ).basis_eq_pow i).symm using 1
  · simp_rw [algebraMap_int_eq, map_mul, map_pow, map_neg, map_one, map_natCast]

open Nat in
/-- We compute the absolute discriminant of a `p ^ (k + 1)`-th cyclotomic field.
  Beware that in the case `p ^ k = 2` the formula uses `1 / 2 = 0`. See also the results below. -/
theorem discr_prime_pow_succ [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
    NumberField.discr K =
    (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow p (k + 1) K

/-- We compute the absolute discriminant of a `p`-th cyclotomic field where `p` is prime. -/
theorem discr_prime [IsCyclotomicExtension {p} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p} ℚ K
    NumberField.discr K = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
  rw [discr_prime_pow_succ p 0 K]
  simp [Nat.sub_sub]

variable (n) [hn : NeZero n]

set_option backward.isDefEq.respectTransparency false in
open Algebra IntermediateField Nat in
/--
Computes the absolute discriminant of the `n`-th cyclotomic field.
-/
theorem discr [hK : IsCyclotomicExtension {n} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
    discr K = (-1) ^ (φ n / 2) * (n ^ φ n / ∏ p ∈ n.primeFactors, p ^ (φ n / (p - 1))) := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  rw [← Int.sign_mul_natAbs (NumberField.discr K), sign_discr, nrComplexPlaces_eq_totient_div_two n]
  congr
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [discr_prime_pow p k K]
    cases k with
    | zero => simp
    | succ k =>
      simpa only [Int.reduceNeg, add_tsub_cancel_right, Int.natAbs_mul, Int.natAbs_pow,
        IsUnit.neg_iff, isUnit_one, Int.natAbs_of_isUnit, one_pow, Int.natAbs_natCast, one_mul]
        using! (Nat.prime_pow_pow_totient_ediv_prod hp k.zero_lt_succ).symm
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    let ζ := zeta (n₁ * n₂) ℚ K
    have hζ := zeta_spec (n₁ * n₂) ℚ K
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₁' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₁ := @hK₁ ℚ⟮ζ ^ n₂⟯ _ _ _ _ (of_intermediateField _)
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₂' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₂ := @hK₂ ℚ⟮ζ ^ n₁⟯ _ _ _ _ (of_intermediateField _)
    have : IsGalois ℚ ℚ⟮ζ ^ n₂⟯ := isGalois {n₁} ℚ _
    have h_top : ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯ = ⊤ := by
      have : IsCyclotomicExtension {n₁ * n₂} ℚ (⊤ : IntermediateField ℚ K) :=
          hK.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {n₁ * n₂} ℚ ↥(ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯) := by
        rw [← Nat.Coprime.lcm_eq_mul h]
        exact isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯
      exact isCyclotomicExtension_eq {n₁ * n₂} ℚ K _ _
    have h_cpr : IsCoprime (discr ℚ⟮ζ ^ n₂⟯) (discr ℚ⟮ζ ^ n₁⟯) := by
      rw [Int.isCoprime_iff_nat_coprime, hK₁, hK₂]
      refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
      refine Coprime.coprime_div_right ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
      exact Coprime.pow_left _ (Coprime.pow_right _ h)
    have h_dsj : ℚ⟮ζ ^ n₂⟯.LinearDisjoint ℚ⟮ζ ^ n₁⟯ :=
      linearDisjoint_of_isGalois_isCoprime_discr _ _ _ h_cpr
    have h_div₁ := prod_primeFactors_pow_totient_ediv_dvd n₁.pos_of_neZero
    have h_div₂ := prod_primeFactors_pow_totient_ediv_dvd n₂.pos_of_neZero
    rw [natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow K ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯ h_dsj h_top
      (isCoprime_differentIdeal_of_isCoprime_discr _ h_cpr), hK₁, hK₂,
      finrank n₁ ℚ⟮ζ ^ n₂⟯, finrank n₂ ℚ⟮ζ ^ n₁⟯, Nat.div_pow h_div₁, Nat.div_pow h_div₂,
      ← Nat.mul_div_mul_comm (pow_dvd_pow_of_dvd h_div₁ n₂.totient)
      (pow_dvd_pow_of_dvd h_div₂ n₁.totient), primeFactors_mul (NeZero.ne _) (NeZero.ne _),
      Finset.prod_union h.disjoint_primeFactors, ← Finset.prod_pow, ← Finset.prod_pow]
    have {n p : ℕ} (hp : p ∈ n.primeFactors) : p - 1 ∣ n.totient :=
      p.totient_prime (prime_of_mem_primeFactors hp) ▸ totient_dvd_of_dvd (b := n)
        <| dvd_of_mem_primeFactors hp
    simp_rw +contextual [← pow_mul, Nat.div_mul_right_comm (this _), Nat.totient_mul h]
    rw [mul_pow, mul_comm n₂.totient]

theorem natAbs_discr [hK : IsCyclotomicExtension {n} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
    (NumberField.discr K).natAbs = n ^ φ n / ∏ p ∈ n.primeFactors, p ^ (φ n / (p - 1)) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  rw [discr n K, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
    Int.natAbs_ediv_of_dvd, Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [← Nat.cast_pow, Int.natCast_dvd_natCast]
  exact Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _)

open IntermediateField Algebra Nat in
private theorem adjoin_singleton_eq_top_aux [NumberField K] (F₁ F₂ : IntermediateField ℚ K)
    {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂] [IsCyclotomicExtension {n₁} ℚ F₁]
    [IsCyclotomicExtension {n₂} ℚ F₂] {ζ₁ : F₁} (hζ₁ : IsPrimitiveRoot ζ₁ n₁)
    (h₁ : ℤ[hζ₁.toInteger] = ⊤) {ζ₂ : F₂} (hζ₂ : IsPrimitiveRoot ζ₂ n₂)
    (h₂ : ℤ[hζ₂.toInteger] = ⊤) (h : n₁.Coprime n₂) (htop : F₁ ⊔ F₂ = ⊤)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (n₁ * n₂)) :
    ℤ[hζ.toInteger] = ⊤ := by
  have h_cpr : IsCoprime (NumberField.discr F₁) (NumberField.discr F₂) := by
    rw [Int.isCoprime_iff_nat_coprime, natAbs_discr n₁ F₁, natAbs_discr n₂ F₂]
    refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    refine Coprime.coprime_div_right ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    exact Coprime.pow_left _ (Coprime.pow_right _ h)
  have h_disj : F₁.LinearDisjoint F₂ := by
    have : IsGalois ℚ F₁ := IsCyclotomicExtension.isGalois {n₁} ℚ F₁
    apply linearDisjoint_of_isGalois_isCoprime_discr
    exact h_cpr
  replace hζ₁ : IsPrimitiveRoot hζ₁.toInteger n₁ := hζ₁.toInteger_isPrimitiveRoot
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₁) (𝓞 K))
  replace hζ₂ : IsPrimitiveRoot hζ₂.toInteger n₂ := hζ₂.toInteger_isPrimitiveRoot
  replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₂) (𝓞 K))
  rw [← IsDedekindDomain.adjoin_union_eq_top_of_isCoprime_differentialIdeal ℤ (𝓞 K) (𝓞 F₁)
    (𝓞 F₂) h_disj _ _ h₁ h₂, Set.image_singleton, Set.image_singleton, Set.singleton_union]
  · refine (IsPrimitiveRoot.adjoin_pair_eq ℤ hζ₁ hζ₂ (NeZero.ne _) (NeZero.ne _) ?_).symm
    rw [Nat.Coprime.lcm_eq_mul h]
    exact toInteger_isPrimitiveRoot hζ
  · simp [← sup_toSubalgebra_of_left, htop]
  · exact isCoprime_differentIdeal_of_isCoprime_discr _ h_cpr

variable {n K}

set_option backward.isDefEq.respectTransparency false in
open IntermediateField Algebra in
theorem adjoin_singleton_eq_top [hK : IsCyclotomicExtension {n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ℤ[hζ.toInteger] = ⊤ := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (p.Prime) := ⟨hp⟩
    rw [← hζ.integralPowerBasisOfPrimePow.adjoin_gen_eq_top, hζ.integralPowerBasisOfPrimePow_gen]
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension ℚ
    replace hζ₁ : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₁ := @hK₁ ℚ⟮ζ ^ n₂⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₁ (of_intermediateField _)
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension ℚ
    replace hζ₂ : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₂ := @hK₂ ℚ⟮ζ ^ n₁⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₂ (of_intermediateField _)
    have h_top : ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯ = ⊤ := by
      have : IsCyclotomicExtension {n₁ * n₂} ℚ (⊤ : IntermediateField ℚ K) :=
          hK.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {n₁ * n₂} ℚ ↥(ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯) := by
        rw [← Nat.Coprime.lcm_eq_mul h]
        exact isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯
      exact isCyclotomicExtension_eq {n₁ * n₂} ℚ K _ _
    exact adjoin_singleton_eq_top_aux K ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯ hζ₁ hK₁ hζ₂ hK₂ h h_top hζ

open Algebra in
theorem isIntegralClosure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) :
    IsIntegralClosure (ℤ[ζ]) ℤ K := by
  constructor
  · exact FaithfulSMul.algebraMap_injective _ K
  · intro _
    have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
      (adjoin_singleton_eq_top hζ)
    simp only [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom', RingOfIntegers.map_mk,
      Algebra.map_top] at this
    simp [IsIntegralClosure.isIntegral_iff (A := 𝓞 K), this, ← SetLike.mem_coe]

variable (n)

set_option backward.isDefEq.respectTransparency false in
/-- The integral closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ ℚ`. -/
theorem cyclotomicRing_isIntegralClosure :
    IsIntegralClosure (CyclotomicRing n ℤ ℚ) ℤ (CyclotomicField n ℚ) := by
  have hζ := zeta_spec n ℚ (CyclotomicField n ℚ)
  refine ⟨IsFractionRing.injective _ _, fun {x} => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_setOf_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {n} ℤ _).isIntegral _)

end IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable [NeZero n] [CharZero K]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `n`-th root of
unity and `K` is an `n`-th cyclotomic extension of `ℚ`. -/
@[simps!]
noncomputable def adjoinEquivRingOfIntegers [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)

/-- The ring of integers of an `n`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance _root_.IsCyclotomicExtension.ringOfIntegers [IsCyclotomicExtension {n} ℚ K] :
    IsCyclotomicExtension {n} ℤ (𝓞 K) :=
  let _ := (zeta_spec n ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec n ℚ K).adjoinEquivRingOfIntegers

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is an `n`-th
cyclotomic extension of `ℚ`. -/
noncomputable def integralPowerBasis [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map hζ.adjoinEquivRingOfIntegers

@[simp]
theorem integralPowerBasis_gen [hcycl : IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    hζ.integralPowerBasis.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp

@[simp]
theorem integralPowerBasis_dim [IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    hζ.integralPowerBasis.dim = φ n := by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ (NeZero.pos _), natDegree_cyclotomic]

/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasis [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasis.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasis_gen, toInteger])

@[simp]
theorem subOneIntegralPowerBasis_gen [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) :
    hζ.subOneIntegralPowerBasis.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasis]

end IsPrimitiveRoot

end discr

end PowerBasis

section NumberField

open Units

theorem NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot [NeZero n] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : n ∣ torsionOrder K := by
  rw [torsionOrder, Fintype.card_eq_nat_card]
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  convert! orderOf_dvd_natCard (⟨(hζ.isUnit (NeZero.ne n)).unit, ?_⟩ : torsion K)
  · rw [Subgroup.orderOf_mk]
    exact hζ.eq_orderOf
  · refine (CommGroup.mem_torsion _).mpr ⟨n, NeZero.pos n, ?_⟩
    rw [isPeriodicPt_mul_iff_pow_eq_one]
    exact hζ.pow_eq_one

/--
The order of the torsion group of the `n`-th cyclotomic field is `n` if `n` is even and
`2n` if `n` is odd.
-/
theorem IsCyclotomicExtension.Rat.torsionOrder_eq [NeZero n] [NumberField K]
    [hK : IsCyclotomicExtension {n} ℚ K] :
    torsionOrder K = if Even n then n else 2 * n := by
  have hζ := hK.zeta_spec
  -- We first prove that `K` contains a primitive root of order `torsionOrder K`
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K := by
    rw [torsionOrder, Fintype.card_eq_nat_card]
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  -- Thus, `K` contains a primitive root of order `l = lcm (n, torsionOrder K)`.
  have h := hζ.pow_mul_pow_lcm hμ (NeZero.ne _) (torsionOrder_ne_zero K)
  have : NeZero (n.lcm (torsionOrder K)) :=
    NeZero.of_pos <| Nat.lcm_pos_iff.mpr ⟨NeZero.pos n, torsionOrder_pos K⟩
  -- and therefore `K` is the `l`-th cyclotomic field
  have : IsCyclotomicExtension {n.lcm (torsionOrder K)} ℚ K := by
    have := hK.union_of_isPrimitiveRoot _ _ _ h
    rwa [Set.union_comm, ← IsCyclotomicExtension.iff_union_of_dvd] at this
    exact ⟨n.lcm (torsionOrder K), by simp, NeZero.ne _, Nat.dvd_lcm_left _ _⟩
  -- We deduce the identity `φ(n) = φ(lcm (n, torsionOrder K))`.
  have h_main := (IsCyclotomicExtension.Rat.finrank n K).symm.trans <|
    (IsCyclotomicExtension.Rat.finrank (n.lcm (torsionOrder K)) K)
  obtain hn | hn := Nat.even_or_odd n
  · rw [if_pos hn]
    apply dvd_antisymm
    · have := hn.eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) h_main
      rwa [eq_comm, Nat.lcm_eq_left_iff_dvd] at this
    · exact dvd_torsionOrder_of_isPrimitiveRoot hζ
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    have := (Nat.eq_or_eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) h_main).resolve_left ?_
    · rw [this, eq_comm, Nat.lcm_eq_right_iff_dvd]
      exact dvd_torsionOrder_of_isPrimitiveRoot hζ
    · rw [eq_comm, Nat.lcm_eq_left_iff_dvd]
      exact fun h ↦ Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hn h) (even_torsionOrder K)

end NumberField
