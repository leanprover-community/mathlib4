/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Ideal.Norm

#align_import number_theory.cyclotomic.rat from "leanprover-community/mathlib"@"b353176c24d96c23f0ce1cc63efc3f55019702d9"

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
-/


universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic NumberField Nat

variable {p : ℕ+} {k : ℕ} {K : Type u} [Field K] [CharZero K] {ζ : K} [hp : Fact (p : ℕ).Prime]

namespace IsCyclotomicExtension.Rat

/-- The discriminant of the power basis given by `ζ - 1`. -/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hk : p ^ (k + 1) ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ (k + 1) : ℕ).totient / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) := by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (p ^ (k + 1)).pos) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
#align is_cyclotomic_extension.rat.discr_prime_pow_ne_two' IsCyclotomicExtension.Rat.discr_prime_pow_ne_two'

theorem discr_odd_prime' [IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis = (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) := by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
#align is_cyclotomic_extension.rat.discr_odd_prime' IsCyclotomicExtension.Rat.discr_odd_prime'

/-- The discriminant of the power basis given by `ζ - 1`. Beware that in the cases `p ^ k = 1` and
`p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform
result. See also `IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'`. -/
theorem discr_prime_pow' [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ k : ℕ).totient / 2) * p ^ ((p : ℕ) ^ (k - 1) * ((p - 1) * k - 1)) := by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (p ^ k).pos)]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
#align is_cyclotomic_extension.rat.discr_prime_pow' IsCyclotomicExtension.Rat.discr_prime_pow'

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of the power basis given by `ζ - 1` is `u * p ^ n`. Often this is
enough and less cumbersome to use than `IsCyclotomicExtension.Rat.discr_prime_pow'`. -/
theorem discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    ∃ (u : ℤˣ) (n : ℕ), discr ℚ (hζ.subOnePowerBasis ℚ).basis = u * p ^ n := by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (p ^ k).pos)
#align is_cyclotomic_extension.rat.discr_prime_pow_eq_unit_mul_pow' IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'

/-- If `K` is a `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the
integral closure of `ℤ` in `K`. -/
theorem isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  refine' ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, _⟩, rfl⟩, _⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        (le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (p ^ k).pos)) _)
  let B := hζ.subOnePowerBasis ℚ
  have hint : IsIntegral ℤ B.gen := (hζ.isIntegral (p ^ k).pos).sub isIntegral_one
-- Porting note: the following `haveI` was not needed because the locale `cyclotomic` set it
-- as instances.
  letI := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ K
  have H := discr_mul_isIntegral_mem_adjoin ℚ hint h
  obtain ⟨u, n, hun⟩ := discr_prime_pow_eq_unit_mul_pow' hζ
  rw [hun] at H
  replace H := Subalgebra.smul_mem _ H u.inv
-- Porting note: the proof is slightly different because of coercions.
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
  · have hmin : (minpoly ℤ B.gen).IsEisensteinAt (Submodule.span ℤ {((p : ℕ) : ℤ)}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat (p ^ _).pos)
      rw [IsPrimitiveRoot.subOnePowerBasis_gen] at h₁
      rw [h₁, ← map_cyclotomic_int, show Int.castRingHom ℚ = algebraMap ℤ ℚ by rfl,
        show X + 1 = map (algebraMap ℤ ℚ) (X + 1) by simp, ← map_comp] at h₂
      haveI : CharZero ℚ := StrictOrderedSemiring.to_charZero
      rw [IsPrimitiveRoot.subOnePowerBasis_gen,
        map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int h₂]
      exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p _
    refine'
      adjoin_le _
        (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (n := n)
          (Nat.prime_iff_prime_int.1 hp.out) hint h (by simpa using H) hmin)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
#align is_cyclotomic_extension.rat.is_integral_closure_adjoin_singleton_of_prime_pow IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow

theorem isIntegralClosure_adjoin_singleton_of_prime [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑p) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ
#align is_cyclotomic_extension.rat.is_integral_closure_adjoin_singleton_of_prime IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime

/-- The integral closure of `ℤ` inside `CyclotomicField (p ^ k) ℚ` is
`CyclotomicRing (p ^ k) ℤ ℚ`. -/
theorem cyclotomicRing_isIntegralClosure_of_prime_pow :
    IsIntegralClosure (CyclotomicRing (p ^ k) ℤ ℚ) ℤ (CyclotomicField (p ^ k) ℚ) := by
  haveI : CharZero ℚ := StrictOrderedSemiring.to_charZero
  have hζ := zeta_spec (p ^ k) ℚ (CyclotomicField (p ^ k) ℚ)
  refine' ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, _⟩, rfl⟩, _⟩⟩
-- Porting note: having `.isIntegral_iff` inside the definition of `this` causes an error.
  · have := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ)
    obtain ⟨y, rfl⟩ := this.isIntegral_iff.1 h
    refine' adjoin_mono _ y.2
    simp only [PNat.pow_coe, Set.singleton_subset_iff, Set.mem_setOf_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {p ^ k} ℤ _) _)
#align is_cyclotomic_extension.rat.cyclotomic_ring_is_integral_closure_of_prime_pow IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime_pow

theorem cyclotomicRing_isIntegralClosure_of_prime :
    IsIntegralClosure (CyclotomicRing p ℤ ℚ) ℤ (CyclotomicField p ℚ) := by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow
#align is_cyclotomic_extension.rat.cyclotomic_ring_is_integral_closure_of_prime IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime

end IsCyclotomicExtension.Rat

section PowerBasis

open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p ^ k`-th root of
unity and `K` is a `p ^ k`-th cyclotomic extension of `ℚ`. -/
@[simps!]
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers
    [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)
#align is_primitive_root.adjoin_equiv_ring_of_integers IsPrimitiveRoot.adjoinEquivRingOfIntegers

/-- The ring of integers of a `p ^ k`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance IsCyclotomicExtension.ringOfIntegers [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclotomicExtension {p ^ k} ℤ (𝓞 K) :=
  let _ := (zeta_spec (p ^ k) ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec (p ^ k) ℚ K).adjoinEquivRingOfIntegers
#align is_cyclotomic_extension.ring_of_integers IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegers

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p ^ k`
cyclotomic extension of `ℚ`. -/
noncomputable def integralPowerBasis [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (p ^ k).pos)).map hζ.adjoinEquivRingOfIntegers
#align is_primitive_root.integral_power_basis IsPrimitiveRoot.integralPowerBasis

/-- Abbreviation to see a primitive root of unity as a member of the ring of integers. -/
abbrev toInteger {k : ℕ+} (hζ : IsPrimitiveRoot ζ k) : 𝓞 K := ⟨ζ, hζ.isIntegral k.pos⟩

--Porting note: the proof changed because `simp` unfolds too much.
@[simp]
theorem integralPowerBasis_gen [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    hζ.integralPowerBasis.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegers_apply, IsIntegralClosure.algebraMap_lift]
    rfl
#align is_primitive_root.integral_power_basis_gen IsPrimitiveRoot.integralPowerBasis_gen

@[simp]
theorem integralPowerBasis_dim [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : hζ.integralPowerBasis.dim = φ (p ^ k) := by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ, natDegree_cyclotomic]
#align is_primitive_root.integral_power_basis_dim IsPrimitiveRoot.integralPowerBasis_dim

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p`-th root of
unity and `K` is a `p`-th cyclotomic extension of `ℚ`. -/
@[simps!]
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegers'
    [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  @adjoinEquivRingOfIntegers p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])
#align is_primitive_root.adjoin_equiv_ring_of_integers' IsPrimitiveRoot.adjoinEquivRingOfIntegers'

/-- The ring of integers of a `p`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance _root_.IsCyclotomicExtension.ring_of_integers' [IsCyclotomicExtension {p} ℚ K] :
    IsCyclotomicExtension {p} ℤ (𝓞 K) :=
  let _ := (zeta_spec p ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec p ℚ K).adjoinEquivRingOfIntegers'
#align is_cyclotomic_extension.ring_of_integers' IsCyclotomicExtension.ring_of_integers'

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p`-th
cyclotomic extension of `ℚ`. -/
noncomputable def integralPowerBasis' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : PowerBasis ℤ (𝓞 K) :=
  @integralPowerBasis p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])
#align is_primitive_root.integral_power_basis' IsPrimitiveRoot.integralPowerBasis'

@[simp]
theorem integralPowerBasis'_gen [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    hζ.integralPowerBasis'.gen = hζ.toInteger :=
  @integralPowerBasis_gen p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])
#align is_primitive_root.integral_power_basis'_gen IsPrimitiveRoot.integralPowerBasis'_gen

@[simp]
theorem power_basis_int'_dim [hcycl : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    hζ.integralPowerBasis'.dim = φ p := by
  erw [@integralPowerBasis_dim p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one]),
    pow_one]
#align is_primitive_root.power_basis_int'_dim IsPrimitiveRoot.power_basis_int'_dim

/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasis [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofGenMemAdjoin' hζ.integralPowerBasis
    (isIntegral_of_mem_ringOfIntegers <|
      Subalgebra.sub_mem _ (hζ.isIntegral (p ^ k).pos) (Subalgebra.one_mem _))
    (by
      simp only [integralPowerBasis_gen, toInteger]
      convert Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ (⟨ζ - 1, _⟩ : 𝓞 K))
        (Subalgebra.one_mem _)
-- Porting note: `simp` was able to finish the proof.
      simp only [Subsemiring.coe_add, Subalgebra.coe_toSubsemiring,
        OneMemClass.coe_one, sub_add_cancel]
      exact Subalgebra.sub_mem _ (hζ.isIntegral (by simp)) (Subalgebra.one_mem _))
#align is_primitive_root.sub_one_integral_power_basis IsPrimitiveRoot.subOneIntegralPowerBasis

@[simp]
theorem subOneIntegralPowerBasis_gen [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    hζ.subOneIntegralPowerBasis.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (p ^ k).pos) (Subalgebra.one_mem _)⟩ :=
  by simp [subOneIntegralPowerBasis]
#align is_primitive_root.sub_one_integral_power_basis_gen IsPrimitiveRoot.subOneIntegralPowerBasis_gen

/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p`-th cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasis' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : PowerBasis ℤ (𝓞 K) :=
  @subOneIntegralPowerBasis p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])
#align is_primitive_root.sub_one_integral_power_basis' IsPrimitiveRoot.subOneIntegralPowerBasis'

@[simp]
theorem subOneIntegralPowerBasis'_gen [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) :
    hζ.subOneIntegralPowerBasis'.gen = hζ.toInteger - 1 :=
  @subOneIntegralPowerBasis_gen p 1 K _ _ _ _ (by convert hcycl; rw [pow_one]) (by rwa [pow_one])
#align is_primitive_root.sub_one_integral_power_basis'_gen IsPrimitiveRoot.subOneIntegralPowerBasis'_gen

/-- `ζ - 1` is prime if `p ≠ 2` and `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
theorem zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (hζ.toInteger - 1) := by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow hp.out.one_lt (by simp))
    rw [← Subalgebra.coe_eq_zero] at h
    simpa [sub_eq_zero] using h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  convert Nat.prime_iff_prime_int.1 hp.out
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
  simp only [PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
    Subalgebra.coe_val, algebraMap_int_eq, map_natCast]
  exact hζ.sub_one_norm_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (PNat.pos _)) hodd

/-- `ζ - 1` is prime if `ζ` is a primitive `2 ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
theorem zeta_sub_one_prime_of_two_pow [IsCyclotomicExtension {(2 : ℕ+) ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑((2 : ℕ+) ^ (k + 1))) :
    Prime (hζ.toInteger - 1) := by
  letI := IsCyclotomicExtension.numberField {(2 : ℕ+) ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow (by decide) (by simp))
    rw [← Subalgebra.coe_eq_zero] at h
    simpa [sub_eq_zero] using h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  cases k
  · convert Prime.neg Int.prime_two
    apply RingHom.injective_int (algebraMap ℤ ℚ)
    rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
    simp only [Nat.zero_eq, PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
      Subalgebra.coe_val, algebraMap_int_eq, map_neg, map_ofNat]
    simpa using hζ.pow_sub_one_norm_two (cyclotomic.irreducible_rat (by simp))
  convert Int.prime_two
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
  simp only [PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
    Subalgebra.coe_val, algebraMap_int_eq, map_natCast]
  exact hζ.sub_one_norm_two Nat.AtLeastTwo.prop (cyclotomic.irreducible_rat (by simp))

/-- `ζ - 1` is prime if `ζ` is a primitive `p ^ (k + 1)`-th root of unity. -/
theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) : Prime (hζ.toInteger - 1) := by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

/-- `ζ - 1` is prime if `ζ` is a primitive `p`-th root of unity. -/
theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    Prime ((hζ.toInteger - 1)) := by
  convert zeta_sub_one_prime (k := 0) (by simpa)
  simpa

theorem subOneIntegralPowerBasis_gen_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) :
    Prime hζ.subOneIntegralPowerBasis.gen := by simpa using hζ.zeta_sub_one_prime

theorem subOneIntegralPowerBasis'_gen_prime [IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑p) :
    Prime hζ.subOneIntegralPowerBasis'.gen := by simpa using hζ.zeta_sub_one_prime'

end IsPrimitiveRoot

end PowerBasis
