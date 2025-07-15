/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Prime

/-!
# Ring of integers of `p ^ n`-th cyclotomic fields
We gather results about cyclotomic extensions of `ℚ`. In particular, we compute the ring of
integers of a `p ^ n`-th cyclotomic extension of `ℚ`.

## Main results
* `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow`: if `K` is a
  `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the integral closure of
  `ℤ` in `K`.
* `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime_pow`: the integral
  closure of `ℤ` inside `CyclotomicField (p ^ k) ℚ` is `CyclotomicRing (p ^ k) ℤ ℚ`.
* `IsCyclotomicExtension.Rat.absdiscr_prime_pow` and related results: the absolute discriminant
  of cyclotomic fields.
-/

universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic Nat

variable {p : ℕ} {k : ℕ} {K : Type u} [Field K] {ζ : K} [hp : Fact p.Prime]

namespace IsCyclotomicExtension.Rat

variable [CharZero K]

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
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p^ (k - 1) * ((p - 1) * k - 1)) := by
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
  -- Porting note: the following `letI` was not needed because the locale `cyclotomic` set it
  -- as instances.
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
      rw [h₁, ← map_cyclotomic_int, show Int.castRingHom ℚ = algebraMap ℤ ℚ by rfl,
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
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers
    [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)

/-- The ring of integers of a `p ^ k`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance IsCyclotomicExtension.ringOfIntegers [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclotomicExtension {p ^ k} ℤ (𝓞 K) :=
  let _ := (zeta_spec (p ^ k) ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec (p ^ k) ℚ K).adjoinEquivRingOfIntegers

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p ^ k`
cyclotomic extension of `ℚ`. -/
noncomputable def integralPowerBasis [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map hζ.adjoinEquivRingOfIntegers

/-- Abbreviation to see a primitive root of unity as a member of the ring of integers. -/
abbrev toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : 𝓞 K :=
  ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

end CharZero

lemma coe_toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.toInteger.1 = ζ := rfl

/-- `𝓞 K ⧸ Ideal.span {ζ - 1}` is finite. -/
lemma finite_quotient_toInteger_sub_one [NumberField K] {k : ℕ} (hk : 1 < k)
    (hζ : IsPrimitiveRoot ζ k) :
    have : NeZero k := NeZero.of_gt hk
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
theorem integralPowerBasis_gen [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.integralPowerBasis.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegers_apply, IsIntegralClosure.algebraMap_lift]
    rfl

#adaptation_note /-- https://github.com/leanprover/lean4/pull/5338
We name `hcycl` so it can be used as a named argument,
but since https://github.com/leanprover/lean4/pull/5338, this is considered unused,
so we need to disable the linter. -/
set_option linter.unusedVariables false in
@[simp]
theorem integralPowerBasis_dim [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.integralPowerBasis.dim = φ (p ^ k) := by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ (NeZero.pos _), natDegree_cyclotomic]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p`-th root of
unity and `K` is a `p`-th cyclotomic extension of `ℚ`. -/
@[simps!]
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers'
    [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  have : IsCyclotomicExtension {p ^ 1} ℚ K := by convert hcycl; rw [pow_one]
  adjoinEquivRingOfIntegers (p := p) (k := 1) (ζ := ζ) (by rwa [pow_one])

/-- The ring of integers of a `p`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance _root_.IsCyclotomicExtension.ring_of_integers' [IsCyclotomicExtension {p} ℚ K] :
    IsCyclotomicExtension {p} ℤ (𝓞 K) :=
  let _ := (zeta_spec p ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec p ℚ K).adjoinEquivRingOfIntegers'

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p`-th
cyclotomic extension of `ℚ`. -/
noncomputable def integralPowerBasis' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : PowerBasis ℤ (𝓞 K) :=
  have : IsCyclotomicExtension {p ^ 1} ℚ K := by convert hcycl; rw [pow_one]
  integralPowerBasis (p := p) (k := 1) (ζ := ζ) (by rwa [pow_one])

@[simp]
theorem integralPowerBasis'_gen [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    hζ.integralPowerBasis'.gen = hζ.toInteger :=
  integralPowerBasis_gen (hcycl := by rwa [pow_one]) (by rwa [pow_one])

@[simp]
theorem power_basis_int'_dim [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    hζ.integralPowerBasis'.dim = φ p := by
  rw [integralPowerBasis', integralPowerBasis_dim (hcycl := by rwa [pow_one]) (by rwa [pow_one]),
    pow_one]


/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasis [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofGenMemAdjoin' hζ.integralPowerBasis (RingOfIntegers.isIntegral _)
    (by
      simp only [integralPowerBasis_gen, toInteger]
      convert Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ (⟨ζ - 1, _⟩ : 𝓞 K))
        (Subalgebra.one_mem _)
      · simp
      · exact Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _))

@[simp]
theorem subOneIntegralPowerBasis_gen [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.subOneIntegralPowerBasis.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasis]

/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p`-th cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasis' [IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : PowerBasis ℤ (𝓞 K) :=
  have : IsCyclotomicExtension {p ^ 1} ℚ K := by rwa [pow_one]
  subOneIntegralPowerBasis (p := p) (k := 1) (ζ := ζ) (by rwa [pow_one])

@[simp, nolint unusedHavesSuffices]
theorem subOneIntegralPowerBasis'_gen [IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) :
    hζ.subOneIntegralPowerBasis'.gen = hζ.toInteger - 1 :=
  -- The `unusedHavesSuffices` linter incorrectly thinks this `have` is unnecessary.
  have : IsCyclotomicExtension {p ^ 1} ℚ K := by rwa [pow_one]
  subOneIntegralPowerBasis_gen (by rwa [pow_one])

/-- `ζ - 1` is prime if `p ≠ 2` and `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
theorem zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (hζ.toInteger - 1) := by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow₀ hp.out.one_lt (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  convert Nat.prime_iff_prime_int.1 hp.out
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
  · apply hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow₀ (by decide) (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  cases k
  · convert Prime.neg Int.prime_two
    apply RingHom.injective_int (algebraMap ℤ ℚ)
    rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ)]
    simp only [algebraMap_int_eq, map_neg, map_ofNat]
    simpa only [zero_add, pow_one, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
        pow_zero]
      using hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat
        (by simp only [zero_add, pow_one, Nat.ofNat_pos]))
  convert Int.prime_two
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
  convert zeta_sub_one_prime (k := 0) (by simpa only [zero_add, pow_one])
  simpa only [zero_add, pow_one]

theorem subOneIntegralPowerBasis_gen_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Prime hζ.subOneIntegralPowerBasis.gen := by
  simpa only [subOneIntegralPowerBasis_gen] using hζ.zeta_sub_one_prime

theorem subOneIntegralPowerBasis'_gen_prime [IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) :
    Prime hζ.subOneIntegralPowerBasis'.gen := by
  simpa only [subOneIntegralPowerBasis'_gen] using hζ.zeta_sub_one_prime'

/-- The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`
is p ^ p ^ s` if `s ≤ k` and `p ^ (k - s + 1) ≠ 2`. -/
lemma norm_toInteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : ℕ} (hs : s ≤ k) (htwo : p ^ (k - s + 1) ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le]
  simp [hζ.norm_pow_sub_one_of_prime_pow_ne_two (cyclotomic.irreducible_rat (NeZero.pos _)) hs htwo]

/-- The norm, relative to `ℤ`, of `ζ ^ 2 ^ k - 1` in a `2 ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `(-2) ^ 2 ^ k`. -/
lemma norm_toInteger_pow_sub_one_of_two [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Algebra.norm ℤ (hζ.toInteger ^ 2 ^ k - 1) = (-2) ^ 2 ^ k := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 1)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le]
  simp [hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat (pow_pos (by decide) _))]

/-- The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ≠ 2`. -/
lemma norm_toInteger_pow_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : ℕ} (hs : s ≤ k) (hodd : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  refine hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two hs (fun h ↦ hodd ?_)
  apply eq_of_prime_pow_eq hp.out.prime Nat.prime_two.prime (k - s).succ_pos
  rwa [pow_one]

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
`p` if `p ≠ 2`. -/
lemma norm_toInteger_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger - 1) = p := by
  simpa only [pow_zero, pow_one] using
    hζ.norm_toInteger_pow_sub_one_of_prime_ne_two (Nat.zero_le _) hodd

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
  have := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two (zero_le _) htwo
  simp only [pow_zero, pow_one] at this
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
a prime if `p ≠ 2`. -/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  simp only [pow_zero, pow_one] at this
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
  let pB := hζ.integralPowerBasis
  have hdim : pB.dim = p ^ k * (↑p - 1) := by
    simp [integralPowerBasis_dim, pB, Nat.totient_prime_pow hp.1 (Nat.zero_lt_succ k)]
  replace hdim : 1 < pB.dim := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one, hdim]
    refine ⟨by simp only [ne_eq, mul_eq_zero, NeZero.ne _, Nat.sub_eq_zero_iff_le, false_or,
      not_le, Nat.Prime.one_lt hp.out, pB], ne_of_gt ?_⟩
    by_cases hk : k = 0
    · simp only [hk, zero_add, pow_one, pow_zero, one_mul, Nat.lt_sub_iff_add_lt,
        Nat.reduceAdd] at htwo ⊢
      exact htwo.symm.lt_of_le hp.1.two_le
    · exact one_lt_mul_of_lt_of_le (one_lt_pow₀ hp.1.one_lt hk)
        (have := Nat.Prime.two_le hp.out; by omega)
  rw [sub_eq_iff_eq_add] at h
  -- We are assuming that `ζ = n + p * x` for some integer `n` and `x : 𝓞 K`. Looking at the
  -- coordinates in the base `pB`, we obtain that `1` is a multiple of `p`, contradiction.
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasis_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this, show pB.gen = pB.gen ^ (⟨1, hdim⟩ : Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (p : 𝓞 K) * x = (p : ℤ) • x by simp, ← pB.basis.coord_apply,
    LinearMap.map_smul, ← zsmul_one, ← pB.basis.coord_apply, LinearMap.map_smul,
    show 1 = pB.gen ^ (⟨0, by omega⟩ : Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
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
  simp_all only [(@Nat.Prime.pow_eq_iff 2 p (k+1) Nat.prime_two).mp (by assumption_mod_cast),
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
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero, ← Subtype.coe_inj] at h
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
  have H := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two (zero_le _) htwo
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

end IsPrimitiveRoot

section absdiscr

namespace IsCyclotomicExtension.Rat

open nonZeroDivisors IsPrimitiveRoot

variable (K p k)
variable [CharZero K]

/-- We compute the absolute discriminant of a `p ^ k`-th cyclotomic field.
  Beware that in the cases `p ^ k = 1` and `p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`.
  See also the results below. -/
theorem absdiscr_prime_pow [IsCyclotomicExtension {p ^ k} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ k} ℚ K
    NumberField.discr K =
    (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k) ℚ K
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ k} ℚ K
  let pB₁ := integralPowerBasis hζ
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB₁.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  convert IsCyclotomicExtension.discr_prime_pow hζ
    (cyclotomic.irreducible_rat (NeZero.pos _)) using 1
  · have : pB₁.dim = (IsPrimitiveRoot.powerBasis ℚ hζ).dim := by
      rw [← PowerBasis.finrank, ← PowerBasis.finrank]
      exact RingOfIntegers.rank K
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp_rw [Function.comp_apply, Basis.localizationLocalization_apply, powerBasis_dim,
      PowerBasis.coe_basis, pB₁, integralPowerBasis_gen]
    convert ← ((IsPrimitiveRoot.powerBasis ℚ hζ).basis_eq_pow i).symm using 1
  · simp_rw [algebraMap_int_eq, map_mul, map_pow, map_neg, map_one, map_natCast]

open Nat in
/-- We compute the absolute discriminant of a `p ^ (k + 1)`-th cyclotomic field.
  Beware that in the case `p ^ k = 2` the formula uses `1 / 2 = 0`. See also the results below. -/
theorem absdiscr_prime_pow_succ [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
    NumberField.discr K =
    (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using absdiscr_prime_pow p (k + 1) K

/-- We compute the absolute discriminant of a `p`-th cyclotomic field where `p` is prime. -/
theorem absdiscr_prime [IsCyclotomicExtension {p} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p} ℚ K
    NumberField.discr K = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
  rw [absdiscr_prime_pow_succ p 0 K]
  simp only [Int.reduceNeg, pow_zero, one_mul, zero_add, mul_one, mul_eq_mul_left_iff,
    pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and, or_false]
  rfl

end IsCyclotomicExtension.Rat

end absdiscr

end PowerBasis
