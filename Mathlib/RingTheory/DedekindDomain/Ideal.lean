/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio

! This file was ported from Lean 3 source module ring_theory.dedekind_domain.ideal
! leanprover-community/mathlib commit 2bbc7e3884ba234309d2a43b19144105a753292e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Subalgebra.Pointwise
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathbin.Order.Hom.Basic
import Mathbin.RingTheory.DedekindDomain.Basic
import Mathbin.RingTheory.FractionalIdeal
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.RingTheory.ChainOfDivisors

/-!
# Dedekind domains and ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible.
Then we prove some results on the unique factorization monoid structure of the ideals.

## Main definitions

 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.
 - `is_dedekind_domain.height_one_spectrum` defines the type of nonzero prime ideals of `R`.

## Main results:
 - `is_dedekind_domain_iff_is_dedekind_domain_inv`
 - `ideal.unique_factorization_monoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type _) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

variable [IsDomain A]

section Inverse

namespace FractionalIdeal

variable {R₁ : Type _} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]

variable {I J : FractionalIdeal R₁⁰ K}

noncomputable instance : Inv (FractionalIdeal R₁⁰ K) :=
  ⟨fun I => 1 / I⟩

theorem inv_eq : I⁻¹ = 1 / I :=
  rfl
#align fractional_ideal.inv_eq FractionalIdeal.inv_eq

theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 :=
  div_zero
#align fractional_ideal.inv_zero' FractionalIdeal.inv_zero'

theorem inv_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, fractional_div_of_nonzero h⟩ :=
  div_nonzero _
#align fractional_ideal.inv_nonzero FractionalIdeal.inv_nonzero

theorem coe_inv_of_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / J := by rwa [inv_nonzero _]; rfl;
  assumption
#align fractional_ideal.coe_inv_of_nonzero FractionalIdeal.coe_inv_of_nonzero

variable {K}

theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : FractionalIdeal R₁⁰ K) :=
  mem_div_iff_of_nonzero hI
#align fractional_ideal.mem_inv_iff FractionalIdeal.mem_inv_iff

theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ := fun x => by
  simp only [mem_inv_iff hI, mem_inv_iff hJ]; exact fun h y hy => h y (hIJ hy)
#align fractional_ideal.inv_anti_mono FractionalIdeal.inv_anti_mono

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * I⁻¹ :=
  le_self_mul_one_div hI
#align fractional_ideal.le_self_mul_inv FractionalIdeal.le_self_mul_inv

variable (K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) : (I : FractionalIdeal R₁⁰ K) ≤ I * I⁻¹ :=
  le_self_mul_inv coeIdeal_le_one
#align fractional_ideal.coe_ideal_le_self_mul_inv FractionalIdeal.coe_ideal_le_self_mul_inv

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ :=
  by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1
  ·
    exact
      congr_arg Units.inv <|
        @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_nonzero hI).mp hy x hx
  rw [← h]
  apply mul_left_mono I
  apply (le_div_iff_of_nonzero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact mul_mem_mul hx hy
#align fractional_ideal.right_inverse_eq FractionalIdeal.right_inverse_eq

theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩
#align fractional_ideal.mul_inv_cancel_iff FractionalIdeal.mul_inv_cancel_iff

theorem mul_inv_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm
#align fractional_ideal.mul_inv_cancel_iff_is_unit FractionalIdeal.mul_inv_cancel_iff_isUnit

variable {K' : Type _} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    I⁻¹.map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ := by rw [inv_eq, map_div, map_one, inv_eq]
#align fractional_ideal.map_inv FractionalIdeal.map_inv

open Submodule Submodule.IsPrincipal

@[simp]
theorem spanSingleton_inv (x : K) : (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹ :=
  one_div_spanSingleton x
#align fractional_ideal.span_singleton_inv FractionalIdeal.spanSingleton_inv

@[simp]
theorem spanSingleton_div_spanSingleton (x y : K) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R₁⁰ (x / y) := by
  rw [div_span_singleton, mul_comm, span_singleton_mul_span_singleton, div_eq_mul_inv]
#align fractional_ideal.span_singleton_div_span_singleton FractionalIdeal.spanSingleton_div_spanSingleton

theorem spanSingleton_div_self {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ x = 1 := by
  rw [span_singleton_div_span_singleton, div_self hx, span_singleton_one]
#align fractional_ideal.span_singleton_div_self FractionalIdeal.spanSingleton_div_self

theorem coe_ideal_span_singleton_div_self {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) / Ideal.span ({x} : Set R₁) = 1 := by
  rw [coe_ideal_span_singleton,
    span_singleton_div_self K <|
      (map_ne_zero_iff _ <| NoZeroSMulDivisors.algebraMap_injective R₁ K).mpr hx]
#align fractional_ideal.coe_ideal_span_singleton_div_self FractionalIdeal.coe_ideal_span_singleton_div_self

theorem spanSingleton_mul_inv {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1 := by
  rw [span_singleton_inv, span_singleton_mul_span_singleton, mul_inv_cancel hx, span_singleton_one]
#align fractional_ideal.span_singleton_mul_inv FractionalIdeal.spanSingleton_mul_inv

theorem coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) * (Ideal.span ({x} : Set R₁))⁻¹ = 1 := by
  rw [coe_ideal_span_singleton,
    span_singleton_mul_inv K <|
      (map_ne_zero_iff _ <| NoZeroSMulDivisors.algebraMap_injective R₁ K).mpr hx]
#align fractional_ideal.coe_ideal_span_singleton_mul_inv FractionalIdeal.coe_ideal_span_singleton_mul_inv

theorem spanSingleton_inv_mul {x : K} (hx : x ≠ 0) :
    (spanSingleton R₁⁰ x)⁻¹ * spanSingleton R₁⁰ x = 1 := by
  rw [mul_comm, span_singleton_mul_inv K hx]
#align fractional_ideal.span_singleton_inv_mul FractionalIdeal.spanSingleton_inv_mul

theorem coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ * Ideal.span ({x} : Set R₁) = 1 := by
  rw [mul_comm, coe_ideal_span_singleton_mul_inv K hx]
#align fractional_ideal.coe_ideal_span_singleton_inv_mul FractionalIdeal.coe_ideal_span_singleton_inv_mul

theorem mul_generator_self_inv {R₁ : Type _} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
  by
  -- Rewrite only the `I` that appears alone.
  conv_lhs =>
    congr
    rw [eq_span_singleton_of_principal I]
  rw [span_singleton_mul_span_singleton, mul_inv_cancel, span_singleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_span_singleton_of_principal I, generator_I_eq_zero, span_singleton_zero]
#align fractional_ideal.mul_generator_self_inv FractionalIdeal.mul_generator_self_inv

theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) : I * I⁻¹ = 1 :=
  mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩
#align fractional_ideal.invertible_of_principal FractionalIdeal.invertible_of_principal

theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) ≠ 0 :=
  by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_span_singleton_of_principal I, hg, span_singleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_span_singleton_of_principal I]
    intro hI
    have := mem_span_singleton_self _ (generator (I : Submodule R₁ K))
    rw [hI, mem_zero_iff] at this 
    contradiction
#align fractional_ideal.invertible_iff_generator_nonzero FractionalIdeal.invertible_iff_generator_nonzero

theorem isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
    (h : I ≠ 0) : Submodule.IsPrincipal I⁻¹.1 :=
  by
  rw [val_eq_coe, is_principal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * span_singleton _ (generator (I : Submodule R₁ K))⁻¹ = 1
  apply mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (span_singleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm
#align fractional_ideal.is_principal_inv FractionalIdeal.isPrincipal_inv

noncomputable instance : InvOneClass (FractionalIdeal R₁⁰ K) :=
  { FractionalIdeal.hasOne, FractionalIdeal.hasInv K with inv_one := div_one }

end FractionalIdeal

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ≠ » («expr⊥»() : fractional_ideal[fractional_ideal] non_zero_divisors(A) (fraction_ring[fraction_ring] A))) -/
/-- A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.cancel_comm_monoid_with_zero`.
-/
def IsDedekindDomainInv : Prop :=
  ∀ (I) (_ : I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A))), I * I⁻¹ = 1
#align is_dedekind_domain_inv IsDedekindDomainInv

open FractionalIdeal

variable {R A K}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ≠ » («expr⊥»() : fractional_ideal[fractional_ideal] non_zero_divisors(A) K)) -/
theorem isDedekindDomainInv_iff [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomainInv A ↔ ∀ (I) (_ : I ≠ (⊥ : FractionalIdeal A⁰ K)), I * I⁻¹ = 1 :=
  by
  let h := map_equiv (FractionRing.algEquiv A K)
  refine' h.to_equiv.forall_congr fun I => _
  rw [← h.to_equiv.apply_eq_iff_eq]
  simp [IsDedekindDomainInv, show ⇑h.to_equiv = h from rfl]
#align is_dedekind_domain_inv_iff isDedekindDomainInv_iff

theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 :=
  by
  set I := adjoin_integral A⁰ x hx
  have mul_self : I * I = I := by apply coe_to_submodule_injective; simp
  convert congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_iff_is_unit K).mpr hI, mul_assoc, mul_one]
#align fractional_ideal.adjoin_integral_eq_one_of_is_unit FractionalIdeal.adjoinIntegral_eq_one_of_isUnit

namespace IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K] (h : IsDedekindDomainInv A)

include h

theorem mul_inv_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : I * I⁻¹ = 1 :=
  isDedekindDomainInv_iff.mp h I hI
#align is_dedekind_domain_inv.mul_inv_eq_one IsDedekindDomainInv.mul_inv_eq_one

theorem inv_mul_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : I⁻¹ * I = 1 :=
  (mul_comm _ _).trans (h.mul_inv_eq_one hI)
#align is_dedekind_domain_inv.inv_mul_eq_one IsDedekindDomainInv.inv_mul_eq_one

protected theorem isUnit {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : IsUnit I :=
  isUnit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)
#align is_dedekind_domain_inv.is_unit IsDedekindDomainInv.isUnit

theorem isNoetherianRing : IsNoetherianRing A :=
  by
  refine' is_noetherian_ring_iff.mpr ⟨fun I : Ideal A => _⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coe_ideal_ne_zero.mpr hI
  exact I.fg_of_is_unit (IsFractionRing.injective A (FractionRing A)) (h.is_unit hI)
#align is_dedekind_domain_inv.is_noetherian_ring IsDedekindDomainInv.isNoetherianRing

theorem integrallyClosed : IsIntegrallyClosed A :=
  by
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine' ⟨fun x hx => _⟩
  rw [← Set.mem_range, ← Algebra.mem_bot, ← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot, ←
    coe_span_singleton A⁰ (1 : FractionRing A), span_singleton_one, ←
    FractionalIdeal.adjoinIntegral_eq_one_of_isUnit x hx (h.is_unit _)]
  · exact mem_adjoin_integral_self A⁰ x hx
  · exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Subalgebra.one_mem _))
#align is_dedekind_domain_inv.integrally_closed IsDedekindDomainInv.integrallyClosed

open Ring

theorem dimensionLeOne : DimensionLeOne A :=
  by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  rintro P P_ne hP
  refine' ideal.is_maximal_def.mpr ⟨hP.ne_top, fun M hM => _⟩
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coe_ideal_ne_zero.mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    coe_ideal_ne_zero.mpr (lt_of_le_of_lt bot_le hM).ne'
  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices (M⁻¹ * P : FractionalIdeal A⁰ (FractionRing A)) ≤ P
    by
    rw [eq_top_iff, ← coe_ideal_le_coe_ideal (FractionRing A), coe_ideal_top]
    calc
      (1 : FractionalIdeal A⁰ (FractionRing A)) = _ * _ * _ := _
      _ ≤ _ * _ := (mul_right_mono (P⁻¹ * M : FractionalIdeal A⁰ (FractionRing A)) this)
      _ = M := _
      
    · rw [mul_assoc, ← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mul, h.inv_mul_eq_one M'_ne]
    · rw [← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mul]
    · infer_instance
  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebra_map _ _ y` for some `y`.
  intro x hx
  have le_one : (M⁻¹ * P : FractionalIdeal A⁰ (FractionRing A)) ≤ 1 :=
    by
    rw [← h.inv_mul_eq_one M'_ne]
    exact mul_left_mono _ ((coe_ideal_le_coe_ideal (FractionRing A)).mpr hM.le)
  obtain ⟨y, hy, rfl⟩ := (mem_coe_ideal _).mp (le_one hx)
  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := mul_mem_mul (mem_coe_ideal_of_mem A⁰ hzM) hx
  rw [← RingHom.map_mul, ← mul_assoc, h.mul_inv_eq_one M'_ne, one_mul] at zy_mem 
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coe_ideal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy 
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coe_ideal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)
#align is_dedekind_domain_inv.dimension_le_one IsDedekindDomainInv.dimensionLeOne

/-- Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem isDedekindDomain : IsDedekindDomain A :=
  ⟨h.IsNoetherianRing, h.DimensionLeOne, h.integrallyClosed⟩
#align is_dedekind_domain_inv.is_dedekind_domain IsDedekindDomainInv.isDedekindDomain

end IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K]

/-- Specialization of `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
theorem exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsField A)
    {I M : Ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).Prod ≤ I ∧
        ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I :=
  by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    multiset.well_founded_lt.has_min
      (fun Z => (Z.map PrimeSpectrum.asIdeal).Prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).Prod ≠ ⊥)
      ⟨Z₀, hZ₀⟩
  have hZM : Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ M := le_trans hZI hIM
  have hZ0 : Z ≠ 0 := by rintro rfl; simpa [hM.ne_top] using hZM
  obtain ⟨_, hPZ', hPM⟩ := (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase PrimeSpectrum.asIdeal PrimeSpectrum.ext P Z
    obtain ⟨hP0, hZP0⟩ : P.as_ideal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).Prod ≠ ⊥ := by
      rwa [Ne.def, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ 
    -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
    have hPM' := (IsDedekindDomain.dimensionLeOne _ hP0 P.is_prime).eq_of_le hM.ne_top hPM
    subst hPM'
    -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
    refine' ⟨Z.erase P, _, _⟩
    · convert hZI
      rw [this, Multiset.cons_erase hPZ']
    · refine' fun h => h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ)
      exact hZP0
#align exists_multiset_prod_cons_le_and_prod_not_le exists_multiset_prod_cons_le_and_prod_not_le

namespace FractionalIdeal

open Ideal

theorem exists_not_mem_one_of_ne_bot [IsDedekindDomain A] (hNF : ¬IsField A) {I : Ideal A}
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ∃ x : K, x ∈ (I⁻¹ : FractionalIdeal A⁰ K) ∧ x ∉ (1 : FractionalIdeal A⁰ K) :=
  by
  -- WLOG, let `I` be maximal.
  suffices
    ∀ {M : Ideal A} (hM : M.IsMaximal),
      ∃ x : K, x ∈ (M⁻¹ : FractionalIdeal A⁰ K) ∧ x ∉ (1 : FractionalIdeal A⁰ K)
    by
    obtain ⟨M, hM, hIM⟩ : ∃ M : Ideal A, is_maximal M ∧ I ≤ M := Ideal.exists_le_maximal I hI1
    skip
    have hM0 := (M.bot_lt_of_maximal hNF).ne'
    obtain ⟨x, hxM, hx1⟩ := this hM
    refine' ⟨x, inv_anti_mono _ _ ((coe_ideal_le_coe_ideal _).mpr hIM) hxM, hx1⟩ <;>
        rw [coe_ideal_ne_zero] <;>
      assumption
  -- Let `a` be a nonzero element of `M` and `J` the ideal generated by `a`.
  intro M hM
  skip
  obtain ⟨⟨a, haM⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt (M.bot_lt_of_maximal hNF)
  replace ha0 : a ≠ 0 := subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp ha0
  have hJM : J ≤ M := ideal.span_le.mpr (set.singleton_subset_iff.mpr haM)
  have hM0 : ⊥ < M := M.bot_lt_of_maximal hNF
  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJM
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := set_like.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  have hb0 : algebraMap A K b ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) b) fun h =>
      hbJ <| h.symm ▸ J.zero_mem
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine' ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff _).mpr _, _⟩
  · exact coe_ideal_ne_zero.mpr hM0.ne'
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coe_ideal _).mp hy₀
    rw [mul_comm, ← mul_assoc, ← RingHom.map_mul]
    have h_yb : y * b ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb 
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, RingHom.map_mul, mul_assoc, mul_inv_cancel hnz_fa, mul_one]
    apply coe_mem_one
  · refine' mt (mem_one_iff _).mp _
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← RingHom.map_mul] at h₂_abs 
    have := ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction
#align fractional_ideal.exists_not_mem_one_of_ne_bot FractionalIdeal.exists_not_mem_one_of_ne_bot

theorem one_mem_inv_coe_ideal {I : Ideal A} (hI : I ≠ ⊥) : (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ :=
  by
  rw [mem_inv_iff (coe_ideal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact coe_ideal_le_one hy
  assumption
#align fractional_ideal.one_mem_inv_coe_ideal FractionalIdeal.one_mem_inv_coe_ideal

theorem mul_inv_cancel_of_le_one [h : IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI : ((I * I⁻¹)⁻¹ : FractionalIdeal A⁰ K) ≤ 1) : (I * I⁻¹ : FractionalIdeal A⁰ K) = 1 :=
  by
  -- Handle a few trivial cases.
  by_cases hI1 : I = ⊤
  · rw [hI1, coe_ideal_top, one_mul, inv_one]
  by_cases hNF : IsField A
  · letI := hNF.to_field; rcases hI1 (I.eq_bot_or_top.resolve_left hI0) with ⟨⟩
  -- We'll show a contradiction with `exists_not_mem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I * I⁻¹ :=
    le_one_iff_exists_coe_ideal.mp mul_one_div_le_one
  by_cases hJ0 : J = ⊥
  · subst hJ0
    refine' absurd _ hI0
    rw [eq_bot_iff, ← coe_ideal_le_coe_ideal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
    infer_instance
  by_cases hJ1 : J = ⊤
  · rw [← hJ, hJ1, coe_ideal_top]
  obtain ⟨x, hx, hx1⟩ :
    ∃ x : K, x ∈ (J : FractionalIdeal A⁰ K)⁻¹ ∧ x ∉ (1 : FractionalIdeal A⁰ K) :=
    exists_not_mem_one_of_ne_bot hNF hJ0 hJ1
  contrapose! hx1 with h_abs
  rw [hJ] at hx 
  exact hI hx
#align fractional_ideal.mul_inv_cancel_of_le_one FractionalIdeal.mul_inv_cancel_of_le_one

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
theorem coe_ideal_mul_inv [h : IsDedekindDomain A] (I : Ideal A) (hI0 : I ≠ ⊥) :
    (I * I⁻¹ : FractionalIdeal A⁰ K) = 1 :=
  by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : (I * I⁻¹ : FractionalIdeal A⁰ K) = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot, Set.mem_range, ←
        mem_one_iff] at this  <;>
      assumption
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integralClosure_iff_mem_FG]
  have x_mul_mem : ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), x * b ∈ (I⁻¹ : FractionalIdeal A⁰ K) :=
    by
    intro b hb
    rw [mem_inv_iff] at hx ⊢
    swap; · exact coe_ideal_ne_zero.mpr hI0
    swap; · exact hJ0
    simp only [mul_assoc, mul_comm b] at hx ⊢
    intro y hy
    exact hx _ (mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine'
    ⟨AlgHom.range (Polynomial.aeval x : A[X] →ₐ[A] K),
      is_noetherian_submodule.mp (IsNoetherian I⁻¹) _ fun y hy => _,
      ⟨Polynomial.X, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine' Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ _
  clear hi
  induction' i with i ih
  · rw [pow_zero]; exact one_mem_inv_coe_ideal hI0
  · show x ^ i.succ ∈ (I⁻¹ : FractionalIdeal A⁰ K)
    rw [pow_succ]; exact x_mul_mem _ ih
#align fractional_ideal.coe_ideal_mul_inv FractionalIdeal.coe_ideal_mul_inv

/-- Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem mul_inv_cancel [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hne : I ≠ 0) :
    I * I⁻¹ = 1 :=
  by
  obtain ⟨a, J, ha, hJ⟩ :
    ∃ (a : A) (aI : Ideal A), a ≠ 0 ∧ I = span_singleton A⁰ (algebraMap _ _ a)⁻¹ * aI :=
    exists_eq_span_singleton_mul I
  suffices h₂ : I * (span_singleton A⁰ (algebraMap _ _ a) * J⁻¹) = 1
  · rw [mul_inv_cancel_iff]
    exact ⟨span_singleton A⁰ (algebraMap _ _ a) * J⁻¹, h₂⟩
  subst hJ
  rw [mul_assoc, mul_left_comm (J : FractionalIdeal A⁰ K), coe_ideal_mul_inv, mul_one,
    span_singleton_mul_span_singleton, inv_mul_cancel, span_singleton_one]
  · exact mt ((injective_iff_map_eq_zero (algebraMap A K)).mp (IsFractionRing.injective A K) _) ha
  · exact coe_ideal_ne_zero.mp (right_ne_zero_of_mul hne)
#align fractional_ideal.mul_inv_cancel FractionalIdeal.mul_inv_cancel

theorem mul_right_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) :
    ∀ {I I'}, I * J ≤ I' * J ↔ I ≤ I' := by
  intro I I'
  constructor
  · intro h;
    convert mul_right_mono J⁻¹ h <;> rw [mul_assoc, FractionalIdeal.mul_inv_cancel hJ, mul_one]
  · exact fun h => mul_right_mono J h
#align fractional_ideal.mul_right_le_iff FractionalIdeal.mul_right_le_iff

theorem mul_left_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) {I I'} :
    J * I ≤ J * I' ↔ I ≤ I' := by convert mul_right_le_iff hJ using 1 <;> simp only [mul_comm]
#align fractional_ideal.mul_left_le_iff FractionalIdeal.mul_left_le_iff

theorem mul_right_strictMono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    StrictMono (· * I) :=
  strictMono_of_le_iff_le fun _ _ => (mul_right_le_iff hI).symm
#align fractional_ideal.mul_right_strict_mono FractionalIdeal.mul_right_strictMono

theorem mul_left_strictMono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    StrictMono ((· * ·) I) :=
  strictMono_of_le_iff_le fun _ _ => (mul_left_le_iff hI).symm
#align fractional_ideal.mul_left_strict_mono FractionalIdeal.mul_left_strictMono

/-- This is also available as `_root_.div_eq_mul_inv`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem div_eq_mul_inv [IsDedekindDomain A] (I J : FractionalIdeal A⁰ K) :
    I / J = I * J⁻¹ := by
  by_cases hJ : J = 0
  · rw [hJ, div_zero, inv_zero', MulZeroClass.mul_zero]
  refine' le_antisymm ((mul_right_le_iff hJ).mp _) ((le_div_iff_mul_le hJ).mpr _)
  · rw [mul_assoc, mul_comm J⁻¹, FractionalIdeal.mul_inv_cancel hJ, mul_one, mul_le]
    intro x hx y hy
    rw [mem_div_iff_of_nonzero hJ] at hx 
    exact hx y hy
  rw [mul_assoc, mul_comm J⁻¹, FractionalIdeal.mul_inv_cancel hJ, mul_one]
  exact le_refl I
#align fractional_ideal.div_eq_mul_inv FractionalIdeal.div_eq_mul_inv

end FractionalIdeal

/-- `is_dedekind_domain` and `is_dedekind_domain_inv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem isDedekindDomain_iff_isDedekindDomainInv : IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun h I hI => FractionalIdeal.mul_inv_cancel hI, fun h => h.IsDedekindDomain⟩
#align is_dedekind_domain_iff_is_dedekind_domain_inv isDedekindDomain_iff_isDedekindDomainInv

end Inverse

section IsDedekindDomain

variable {R A} [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

open Ideal

noncomputable instance FractionalIdeal.semifield : Semifield (FractionalIdeal A⁰ K) :=
  { FractionalIdeal.commSemiring,
    coeIdeal_injective.Nontrivial with
    inv := fun I => I⁻¹
    inv_zero := inv_zero' _
    div := (· / ·)
    div_eq_mul_inv := FractionalIdeal.div_eq_mul_inv
    mul_inv_cancel := fun I => FractionalIdeal.mul_inv_cancel }
#align fractional_ideal.semifield FractionalIdeal.semifield

/-- Fractional ideals have cancellative multiplication in a Dedekind domain.

Although this instance is a direct consequence of the instance
`fractional_ideal.comm_group_with_zero`, we define this instance to provide
a computable alternative.
-/
instance FractionalIdeal.cancelCommMonoidWithZero :
    CancelCommMonoidWithZero (FractionalIdeal A⁰ K) :=
  {
    FractionalIdeal.commSemiring,-- Project out the computable fields first.
    (by infer_instance : CancelCommMonoidWithZero (FractionalIdeal A⁰ K)) with }
#align fractional_ideal.cancel_comm_monoid_with_zero FractionalIdeal.cancelCommMonoidWithZero

instance Ideal.cancelCommMonoidWithZero : CancelCommMonoidWithZero (Ideal A) :=
  { Ideal.idemCommSemiring,
    Function.Injective.cancelCommMonoidWithZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
      (RingHom.map_zero _) (RingHom.map_one _) (RingHom.map_mul _) (RingHom.map_pow _) with }
#align ideal.cancel_comm_monoid_with_zero Ideal.cancelCommMonoidWithZero

instance Ideal.isDomain : IsDomain (Ideal A) :=
  { (inferInstance : IsCancelMulZero _), Ideal.nontrivial with }
#align ideal.is_domain Ideal.isDomain

/-- For ideals in a Dedekind domain, to divide is to contain. -/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h 
      rw [hI, hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coe_ideal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J ≤ 1 :=
      le_trans (mul_left_mono (↑I)⁻¹ ((coe_ideal_le_coe_ideal _).mpr h))
        (le_of_eq (inv_mul_cancel hI'))
    obtain ⟨H, hH⟩ := le_one_iff_exists_coe_ideal.mp this
    use H
    refine' coe_ideal_injective (show (J : FractionalIdeal A⁰ (FractionRing A)) = ↑(I * H) from _)
    rw [coe_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]⟩
#align ideal.dvd_iff_le Ideal.dvd_iff_le

theorem Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_lt h))
      (mt Ideal.dvd_iff_le.mp (not_le_of_lt h))⟩
#align ideal.dvd_not_unit_iff_lt Ideal.dvdNotUnit_iff_lt

instance : WfDvdMonoid (Ideal A)
    where wellFounded_dvdNotUnit :=
    by
    have : WellFounded ((· > ·) : Ideal A → Ideal A → Prop) :=
      isNoetherian_iff_wellFounded.mp (isNoetherianRing_iff.mp IsDedekindDomain.isNoetherianRing)
    convert this
    ext
    rw [Ideal.dvdNotUnit_iff_lt]

instance Ideal.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Ideal A) :=
  { Ideal.wfDvdMonoid with
    irreducible_iff_prime := fun P =>
      ⟨fun hirr =>
        ⟨hirr.NeZero, hirr.not_unit, fun I J =>
          by
          have : P.is_maximal :=
            by
            refine' ⟨⟨mt ideal.is_unit_iff.mpr hirr.not_unit, _⟩⟩
            intro J hJ
            obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ
            exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit)
          rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, SetLike.le_def, SetLike.le_def,
            SetLike.le_def]
          contrapose!
          rintro ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩
          exact
            ⟨x * y, Ideal.mul_mem_mul x_mem y_mem,
              mt this.is_prime.mem_or_mem (not_or_of_not x_not_mem y_not_mem)⟩⟩,
        Prime.irreducible⟩ }
#align ideal.unique_factorization_monoid Ideal.uniqueFactorizationMonoid

instance Ideal.normalizationMonoid : NormalizationMonoid (Ideal A) :=
  normalizationMonoidOfUniqueUnits
#align ideal.normalization_monoid Ideal.normalizationMonoid

@[simp]
theorem Ideal.dvd_span_singleton {I : Ideal A} {x : A} : I ∣ Ideal.span {x} ↔ x ∈ I :=
  Ideal.dvd_iff_le.trans (Ideal.span_le.trans Set.singleton_subset_iff)
#align ideal.dvd_span_singleton Ideal.dvd_span_singleton

theorem Ideal.isPrime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P :=
  by
  refine' ⟨_, fun x y hxy => _⟩
  · rintro rfl
    rw [← Ideal.one_eq_top] at h 
    exact h.not_unit isUnit_one
  · simp only [← Ideal.dvd_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy
#align ideal.is_prime_of_prime Ideal.isPrime_of_prime

theorem Ideal.prime_of_isPrime {P : Ideal A} (hP : P ≠ ⊥) (h : IsPrime P) : Prime P :=
  by
  refine' ⟨hP, mt ideal.is_unit_iff.mp h.ne_top, fun I J hIJ => _⟩
  simpa only [Ideal.dvd_iff_le] using h.mul_le.mp (Ideal.le_of_dvd hIJ)
#align ideal.prime_of_is_prime Ideal.prime_of_isPrime

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `ideal A`
are exactly the prime ideals. -/
theorem Ideal.prime_iff_isPrime {P : Ideal A} (hP : P ≠ ⊥) : Prime P ↔ IsPrime P :=
  ⟨Ideal.isPrime_of_prime, Ideal.prime_of_isPrime hP⟩
#align ideal.prime_iff_is_prime Ideal.prime_iff_isPrime

/-- In a Dedekind domain, the the prime ideals are the zero ideal together with the prime elements
of the monoid with zero `ideal A`. -/
theorem Ideal.isPrime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P :=
  ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => Ideal.prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ Ideal.bot_prime) Ideal.isPrime_of_prime⟩
#align ideal.is_prime_iff_bot_or_prime Ideal.isPrime_iff_bot_or_prime

theorem Ideal.strictAnti_pow (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    StrictAnti ((· ^ ·) I : ℕ → Ideal A) :=
  strictAnti_nat_of_succ_lt fun e =>
    Ideal.dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ' I e⟩
#align ideal.strict_anti_pow Ideal.strictAnti_pow

theorem Ideal.pow_lt_self (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) :
    I ^ e < I := by convert I.strict_anti_pow hI0 hI1 he <;> rw [pow_one]
#align ideal.pow_lt_self Ideal.pow_lt_self

theorem Ideal.exists_mem_pow_not_mem_pow_succ (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
    ∃ x ∈ I ^ e, x ∉ I ^ (e + 1) :=
  SetLike.exists_of_lt (I.strictAnti_pow hI0 hI1 e.lt_succ_self)
#align ideal.exists_mem_pow_not_mem_pow_succ Ideal.exists_mem_pow_not_mem_pow_succ

open UniqueFactorizationMonoid

theorem Ideal.eq_prime_pow_of_succ_lt_of_le {P I : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥)
    {i : ℕ} (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) : I = P ^ i :=
  by
  letI := Classical.decEq (Ideal A)
  refine' le_antisymm hle _
  have P_prime' := Ideal.prime_of_isPrime hP P_prime
  have : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have := pow_ne_zero (i + 1) hP
  rw [← Ideal.dvdNotUnit_iff_lt, dvd_not_unit_iff_normalized_factors_lt_normalized_factors,
    normalized_factors_pow, normalized_factors_irreducible P_prime'.irreducible,
    Multiset.nsmul_singleton, Multiset.lt_replicate_succ] at hlt 
  rw [← Ideal.dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors, normalized_factors_pow,
    normalized_factors_irreducible P_prime'.irreducible, Multiset.nsmul_singleton]
  all_goals assumption
#align ideal.eq_prime_pow_of_succ_lt_of_le Ideal.eq_prime_pow_of_succ_lt_of_le

theorem Ideal.pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥) (i : ℕ) :
    P ^ (i + 1) < P ^ i :=
  lt_of_le_of_ne (Ideal.pow_le_pow (Nat.le_succ _))
    (mt (pow_eq_pow_iff hP (mt Ideal.isUnit_iff.mp P_prime.ne_top)).mp i.succ_ne_self)
#align ideal.pow_succ_lt_pow Ideal.pow_succ_lt_pow

theorem Associates.le_singleton_iff (x : A) (n : ℕ) (I : Ideal A) :
    Associates.mk I ^ n ≤ Associates.mk (Ideal.span {x}) ↔ x ∈ I ^ n := by
  rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk, Ideal.dvd_span_singleton]
#align associates.le_singleton_iff Associates.le_singleton_iff

open FractionalIdeal

variable {A K}

/-- Strengthening of `is_localization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `A` that is not completely contained in `J`. -/
theorem Ideal.exist_integer_multiples_not_mem {J : Ideal A} (hJ : J ≠ ⊤) {ι : Type _} (s : Finset ι)
    (f : ι → K) {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
    ∃ a : K,
      (∀ i ∈ s, IsLocalization.IsInteger A (a * f i)) ∧
        ∃ i ∈ s, a * f i ∉ (J : FractionalIdeal A⁰ K) :=
  by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := span_finset A s f
  have hI0 : I ≠ 0 := span_finset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹
    by
    obtain ⟨_, a, hI, hpI⟩ := set_like.lt_iff_le_and_exists.mp this
    rw [mem_inv_iff hI0] at hI 
    refine' ⟨a, fun i hi => _, _⟩
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    · exact (mem_one_iff _).mp (hI (f i) (Submodule.subset_span (Set.mem_image_of_mem f hi)))
    · contrapose! hpI
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine' (mem_div_iff_of_nonzero hI0).mpr fun y hy => Submodule.span_induction hy _ _ _ _
      · rintro _ ⟨i, hi, rfl⟩; exact hpI i hi
      · rw [MulZeroClass.mul_zero]; exact Submodule.zero_mem _
      · intro x y hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
      · intro b x hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  calc
    ↑J / I = ↑J * I⁻¹ := div_eq_mul_inv (↑J) I
    _ < 1 * I⁻¹ := (mul_right_strict_mono (inv_ne_zero hI0) _)
    _ = I⁻¹ := one_mul _
    
  · rw [← coe_ideal_top]
    -- And multiplying by `I⁻¹` is indeed strictly monotone.
    exact
      strictMono_of_le_iff_le (fun _ _ => (coe_ideal_le_coe_ideal K).symm)
        (lt_top_iff_ne_top.mpr hJ)
#align ideal.exist_integer_multiples_not_mem Ideal.exist_integer_multiples_not_mem

section Gcd

namespace Ideal

/-! ### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `normalized_gcd_monoid (ideal A)`.
-/


@[simp]
theorem sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I * J :=
  by
  letI := Classical.decEq (Ideal A)
  letI := Classical.decEq (Associates (Ideal A))
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J :=
    by
    rw [gcd_eq_normalize _ _, normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le, dvd_iff_le]
      simp
  have hlcm : lcm I J = I ⊓ J :=
    by
    rw [lcm_eq_normalize _ _, normalize_eq]
    · rw [lcm_dvd_iff, dvd_iff_le, dvd_iff_le]
      simp
    · rw [dvd_iff_le, le_inf_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩
  rw [← hgcd, ← hlcm, associated_iff_eq.mp (gcd_mul_lcm _ _)]
  infer_instance
#align ideal.sup_mul_inf Ideal.sup_mul_inf

/-- Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are compatible with
the normalization operator. -/
instance : NormalizedGCDMonoid (Ideal A) :=
  { Ideal.normalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := fun _ _ _ => by simpa only [dvd_iff_le] using sup_le
    lcm := (· ⊓ ·)
    lcm_zero_left := fun _ => by simp only [zero_eq_bot, bot_inf_eq]
    lcm_zero_right := fun _ => by simp only [zero_eq_bot, inf_bot_eq]
    gcd_mul_lcm := fun _ _ => by rw [associated_iff_eq, sup_mul_inf]
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

-- In fact, any lawful gcd and lcm would equal sup and inf respectively.
@[simp]
theorem gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J :=
  rfl
#align ideal.gcd_eq_sup Ideal.gcd_eq_sup

@[simp]
theorem lcm_eq_inf (I J : Ideal A) : lcm I J = I ⊓ J :=
  rfl
#align ideal.lcm_eq_inf Ideal.lcm_eq_inf

theorem inf_eq_mul_of_coprime {I J : Ideal A} (coprime : I ⊔ J = ⊤) : I ⊓ J = I * J := by
  rw [← associated_iff_eq.mp (gcd_mul_lcm I J), lcm_eq_inf I J, gcd_eq_sup, coprime, top_mul]
#align ideal.inf_eq_mul_of_coprime Ideal.inf_eq_mul_of_coprime

end Ideal

end Gcd

end IsDedekindDomain

section IsDedekindDomain

variable {T : Type _} [CommRing T] [IsDomain T] [IsDedekindDomain T] {I J : Ideal T}

open scoped Classical

open Multiset UniqueFactorizationMonoid Ideal

theorem prod_normalizedFactors_eq_self (hI : I ≠ ⊥) : (normalizedFactors I).Prod = I :=
  associated_iff_eq.1 (normalizedFactors_prod hI)
#align prod_normalized_factors_eq_self prod_normalizedFactors_eq_self

theorem count_le_of_ideal_ge {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
    count K (normalizedFactors J) ≤ count K (normalizedFactors I) :=
  le_iff_count.1
    ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
      (dvd_iff_le.2 h))
    _
#align count_le_of_ideal_ge count_le_of_ideal_ge

theorem sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊔ J = (normalizedFactors I ∩ normalizedFactors J).Prod :=
  by
  have H :
    normalized_factors (normalized_factors I ∩ normalized_factors J).Prod =
      normalized_factors I ∩ normalized_factors J :=
    by
    apply normalized_factors_prod_of_prime
    intro p hp
    rw [mem_inter] at hp 
    exact prime_of_normalized_factor p hp.left
  have :=
    Multiset.prod_ne_zero_of_prime (normalized_factors I ∩ normalized_factors J) fun _ h =>
      prime_of_normalized_factor _ (Multiset.mem_inter.1 h).1
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor
    · rw [dvd_iff_normalized_factors_le_normalized_factors this hI, H]
      exact inf_le_left
    · rw [dvd_iff_normalized_factors_le_normalized_factors this hJ, H]
      exact inf_le_right
  · rw [← dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors,
      normalized_factors_prod_of_prime, le_iff_count]
    · intro a
      rw [Multiset.count_inter]
      exact le_min (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)
    · intro p hp
      rw [mem_inter] at hp 
      exact prime_of_normalized_factor p hp.left
    · exact ne_bot_of_le_ne_bot hI le_sup_left
    · exact this
#align sup_eq_prod_inf_factors sup_eq_prod_inf_factors

theorem irreducible_pow_sup (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ) :
    J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n := by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI, min_comm,
    normalized_factors_of_irreducible_pow hJ, normalize_eq J, replicate_inter, prod_replicate]
#align irreducible_pow_sup irreducible_pow_sup

theorem irreducible_pow_sup_of_le (hJ : Irreducible J) (n : ℕ) (hn : ↑n ≤ multiplicity J I) :
    J ^ n ⊔ I = J ^ n := by
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ, min_eq_right]
  rwa [multiplicity_eq_count_normalized_factors hJ hI, PartENat.coe_le_coe, normalize_eq J] at hn 
#align irreducible_pow_sup_of_le irreducible_pow_sup_of_le

theorem irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ)
    (hn : multiplicity J I ≤ n) :
    J ^ n ⊔ I = J ^ (multiplicity J I).get (PartENat.dom_of_le_natCast hn) :=
  by
  rw [irreducible_pow_sup hI hJ, min_eq_left]
  congr
  ·
    rw [← PartENat.natCast_inj, PartENat.natCast_get,
      multiplicity_eq_count_normalized_factors hJ hI, normalize_eq J]
  · rwa [multiplicity_eq_count_normalized_factors hJ hI, PartENat.coe_le_coe, normalize_eq J] at hn 
#align irreducible_pow_sup_of_ge irreducible_pow_sup_of_ge

end IsDedekindDomain

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `height_one_spectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible.
-/


namespace IsDedekindDomain

variable [IsDomain R] [IsDedekindDomain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint has_nonempty_instance unused_arguments]
structure HeightOneSpectrum where
  asIdeal : Ideal R
  IsPrime : as_ideal.IsPrime
  ne_bot : as_ideal ≠ ⊥
#align is_dedekind_domain.height_one_spectrum IsDedekindDomain.HeightOneSpectrum

attribute [instance] height_one_spectrum.is_prime

variable (v : HeightOneSpectrum R) {R}

namespace HeightOneSpectrum

instance isMaximal : v.asIdeal.IsMaximal :=
  dimensionLeOne v.asIdeal v.ne_bot v.IsPrime
#align is_dedekind_domain.height_one_spectrum.is_maximal IsDedekindDomain.HeightOneSpectrum.isMaximal

theorem prime : Prime v.asIdeal :=
  Ideal.prime_of_isPrime v.ne_bot v.IsPrime
#align is_dedekind_domain.height_one_spectrum.prime IsDedekindDomain.HeightOneSpectrum.prime

theorem irreducible : Irreducible v.asIdeal :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.Prime
#align is_dedekind_domain.height_one_spectrum.irreducible IsDedekindDomain.HeightOneSpectrum.irreducible

theorem associates_irreducible : Irreducible <| Associates.mk v.asIdeal :=
  (Associates.irreducible_mk _).mpr v.Irreducible
#align is_dedekind_domain.height_one_spectrum.associates_irreducible IsDedekindDomain.HeightOneSpectrum.associates_irreducible

/-- An equivalence between the height one and maximal spectra for rings of Krull dimension 1. -/
def equivMaximalSpectrum (hR : ¬IsField R) : HeightOneSpectrum R ≃ MaximalSpectrum R
    where
  toFun v := ⟨v.asIdeal, dimensionLeOne v.asIdeal v.ne_bot v.IsPrime⟩
  invFun v :=
    ⟨v.asIdeal, v.IsMaximal.IsPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.IsMaximal hR⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align is_dedekind_domain.height_one_spectrum.equiv_maximal_spectrum IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum

variable (R K)

/-- A Dedekind domain is equal to the intersection of its localizations at all its height one
non-zero prime ideals viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot [Algebra R K] [hK : IsFractionRing R K] :
    (⨅ v : HeightOneSpectrum R,
        Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) =
      ⊥ :=
  by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  by_cases hR : IsField R
  · rcases function.bijective_iff_has_inverse.mp
        (IsField.localization_map_bijective (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR) with
      ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exact fun _ => algebra.mem_bot.mpr ⟨algebra_map_inv x, algebra_map_right_inv x⟩
    exact hK
  all_goals rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
  · exact fun hx ⟨v, hv⟩ => hx ((equiv_maximal_spectrum hR).symm ⟨v, hv⟩)
  · exact fun hx ⟨v, hv, hbot⟩ => hx ⟨v, dimension_le_one v hbot hv⟩
#align is_dedekind_domain.height_one_spectrum.infi_localization_eq_bot IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot

end HeightOneSpectrum

end IsDedekindDomain

section

open Ideal

variable {R} {A} [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps]
def idealFactorsFunOfQuotHom {f : R ⧸ I →+* A ⧸ J} (hf : Function.Surjective f) :
    { p : Ideal R | p ∣ I } →o { p : Ideal A | p ∣ J }
    where
  toFun X :=
    ⟨comap J.Quotient.mk (map f (map I.Quotient.mk X)),
      by
      have : J.Quotient.mk.ker ≤ comap J.Quotient.mk (map f (map I.Quotient.mk X)) :=
        ker_le_comap J.Quotient.mk
      rw [mk_ker] at this 
      exact dvd_iff_le.mpr this⟩
  monotone' := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    rw [← Subtype.coe_le_coe, Subtype.coe_mk, Subtype.coe_mk] at h ⊢
    rw [Subtype.coe_mk, comap_le_comap_iff_of_surjective J.Quotient.mk quotient.mk_surjective,
      map_le_iff_le_comap, Subtype.coe_mk, comap_map_of_surjective _ hf (map I.Quotient.mk Y)]
    suffices map I.Quotient.mk X ≤ map I.Quotient.mk Y by exact le_sup_of_le_left this
    rwa [map_le_iff_le_comap, comap_map_of_surjective I.Quotient.mk quotient.mk_surjective, ←
      RingHom.ker_eq_comap_bot, mk_ker, sup_eq_left.mpr <| le_of_dvd hY]
#align ideal_factors_fun_of_quot_hom idealFactorsFunOfQuotHom

@[simp]
theorem idealFactorsFunOfQuotHom_id :
    idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)).is_surjective = OrderHom.id :=
  OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_fun_mk, OrderHom.id_coe, id.def,
        comap_map_of_surjective J.Quotient.mk quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot J.Quotient.mk, mk_ker, sup_eq_left.mpr (dvd_iff_le.mp X.prop),
        Subtype.coe_eta])
#align ideal_factors_fun_of_quot_hom_id idealFactorsFunOfQuotHom_id

variable {B : Type _} [CommRing B] [IsDomain B] [IsDedekindDomain B] {L : Ideal B}

theorem idealFactorsFunOfQuotHom_comp {f : R ⧸ I →+* A ⧸ J} {g : A ⧸ J →+* B ⧸ L}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (idealFactorsFunOfQuotHom hg).comp (idealFactorsFunOfQuotHom hf) =
      idealFactorsFunOfQuotHom (show Function.Surjective (g.comp f) from hg.comp hf) :=
  by
  refine' OrderHom.ext _ _ (funext fun x => _)
  rw [idealFactorsFunOfQuotHom, idealFactorsFunOfQuotHom, OrderHom.comp_coe, OrderHom.coe_fun_mk,
    OrderHom.coe_fun_mk, Function.comp_apply, idealFactorsFunOfQuotHom, OrderHom.coe_fun_mk,
    Subtype.mk_eq_mk, Subtype.coe_mk, map_comap_of_surjective J.Quotient.mk quotient.mk_surjective,
    map_map]
#align ideal_factors_fun_of_quot_hom_comp idealFactorsFunOfQuotHom_comp

variable [IsDomain R] [IsDedekindDomain R] (f : R ⧸ I ≃+* A ⧸ J)

/-- The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing `J` induced by
  an isomorphism `f : R/I ≅ A/J`. -/
@[simps]
def idealFactorsEquivOfQuotEquiv : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J } :=
  OrderIso.ofHomInv
    (idealFactorsFunOfQuotHom (show Function.Surjective (f : R ⧸ I →+* A ⧸ J) from f.Surjective))
    (idealFactorsFunOfQuotHom
      (show Function.Surjective (f.symm : A ⧸ J →+* R ⧸ I) from f.symm.Surjective))
    (by
      simp only [← idealFactorsFunOfQuotHom_id, OrderHom.coe_eq, OrderHom.coe_eq,
        idealFactorsFunOfQuotHom_comp, ← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, ←
        RingEquiv.toRingHom_trans, RingEquiv.symm_trans_self, RingEquiv.toRingHom_refl])
    (by
      simp only [← idealFactorsFunOfQuotHom_id, OrderHom.coe_eq, OrderHom.coe_eq,
        idealFactorsFunOfQuotHom_comp, ← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, ←
        RingEquiv.toRingHom_trans, RingEquiv.self_trans_symm, RingEquiv.toRingHom_refl])
#align ideal_factors_equiv_of_quot_equiv idealFactorsEquivOfQuotEquiv

theorem idealFactorsEquivOfQuotEquiv_symm :
    (idealFactorsEquivOfQuotEquiv f).symm = idealFactorsEquivOfQuotEquiv f.symm :=
  rfl
#align ideal_factors_equiv_of_quot_equiv_symm idealFactorsEquivOfQuotEquiv_symm

theorem idealFactorsEquivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) :
    (idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ↔
      L ∣ M :=
  by
  suffices
    idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ≤ idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ ↔
      (⟨M, hM⟩ : { p : Ideal R | p ∣ I }) ≤ ⟨L, hL⟩
    by rw [dvd_iff_le, dvd_iff_le, Subtype.coe_le_coe, this, Subtype.mk_le_mk]
  exact (idealFactorsEquivOfQuotEquiv f).le_iff_le
#align ideal_factors_equiv_of_quot_equiv_is_dvd_iso idealFactorsEquivOfQuotEquiv_is_dvd_iso

open UniqueFactorizationMonoid

variable [DecidableEq (Ideal R)] [DecidableEq (Ideal A)]

theorem idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors (hJ : J ≠ ⊥)
    {L : Ideal R} (hL : L ∈ normalizedFactors I) :
    ↑(idealFactorsEquivOfQuotEquiv f ⟨L, dvd_of_mem_normalizedFactors hL⟩) ∈ normalizedFactors J :=
  by
  by_cases hI : I = ⊥
  · exfalso
    rw [hI, bot_eq_zero, normalized_factors_zero, ← Multiset.empty_eq_zero] at hL 
    exact hL
  · apply mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL _
    rintro ⟨l, hl⟩ ⟨l', hl'⟩
    rw [Subtype.coe_mk, Subtype.coe_mk]
    apply idealFactorsEquivOfQuotEquiv_is_dvd_iso f
#align ideal_factors_equiv_of_quot_equiv_mem_normalized_factors_of_mem_normalized_factors idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors

/-- The bijection between the sets of normalized factors of I and J induced by a ring
    isomorphism `f : R/I ≅ A/J`. -/
@[simps apply]
def normalizedFactorsEquivOfQuotEquiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    { L : Ideal R | L ∈ normalizedFactors I } ≃ { M : Ideal A | M ∈ normalizedFactors J }
    where
  toFun j :=
    ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.Prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.Prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.Prop⟩,
      by
      rw [idealFactorsEquivOfQuotEquiv_symm]
      exact
        idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f.symm hI
          j.prop⟩
  left_inv := fun ⟨j, hj⟩ => by simp
  right_inv := fun ⟨j, hj⟩ => by simp
#align normalized_factors_equiv_of_quot_equiv normalizedFactorsEquivOfQuotEquiv

@[simp]
theorem normalizedFactorsEquivOfQuotEquiv_symm (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (normalizedFactorsEquivOfQuotEquiv f hI hJ).symm =
      normalizedFactorsEquivOfQuotEquiv f.symm hJ hI :=
  rfl
#align normalized_factors_equiv_of_quot_equiv_symm normalizedFactorsEquivOfQuotEquiv_symm

variable [DecidableRel ((· ∣ ·) : Ideal R → Ideal R → Prop)]

variable [DecidableRel ((· ∣ ·) : Ideal A → Ideal A → Prop)]

/-- The map `normalized_factors_equiv_of_quot_equiv` preserves multiplicities. -/
theorem normalizedFactorsEquivOfQuotEquiv_multiplicity_eq_multiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (L : Ideal R) (hL : L ∈ normalizedFactors I) :
    multiplicity (↑(normalizedFactorsEquivOfQuotEquiv f hI hJ ⟨L, hL⟩)) J = multiplicity L I :=
  by
  rw [normalizedFactorsEquivOfQuotEquiv, Equiv.coe_fn_mk, Subtype.coe_mk]
  exact
    multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalizedFactors hI hJ hL
      fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_iso f hl hl'
#align normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity normalizedFactorsEquivOfQuotEquiv_multiplicity_eq_multiplicity

end

section ChineseRemainder

open Ideal UniqueFactorizationMonoid

open scoped BigOperators

variable {R}

theorem Ring.DimensionLeOne.prime_le_prime_iff_eq (h : Ring.DimensionLeOne R) {P Q : Ideal R}
    [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : P ≠ ⊥) : P ≤ Q ↔ P = Q :=
  ⟨(h P hP0 hP).eq_of_le hQ.ne_top, Eq.le⟩
#align ring.dimension_le_one.prime_le_prime_iff_eq Ring.DimensionLeOne.prime_le_prime_iff_eq

theorem Ideal.coprime_of_no_prime_ge {I J : Ideal R} (h : ∀ P, I ≤ P → J ≤ P → ¬IsPrime P) :
    I ⊔ J = ⊤ := by
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.is_prime
#align ideal.coprime_of_no_prime_ge Ideal.coprime_of_no_prime_ge

section DedekindDomain

variable {R} [IsDomain R] [IsDedekindDomain R]

theorem Ideal.IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ∨ b ∈ I ^ n :=
  by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  simp only [← Submodule.span_singleton_le_iff_mem, Ideal.submodule_span_eq, ← Ideal.dvd_iff_le, ←
    Ideal.span_singleton_mul_span_singleton] at h ⊢
  by_cases ha : I ∣ span {a}
  · exact Or.inl ha
  rw [mul_comm] at h 
  exact Or.inr (Prime.pow_dvd_of_dvd_mul_right ((Ideal.prime_iff_isPrime hI0).mpr hI) _ ha h)
#align ideal.is_prime.mul_mem_pow Ideal.IsPrime.mul_mem_pow

section

open scoped Classical

theorem Ideal.count_normalizedFactors_eq {p x : Ideal R} [hp : p.IsPrime] {n : ℕ} (hle : x ≤ p ^ n)
    (hlt : ¬x ≤ p ^ (n + 1)) : (normalizedFactors x).count p = n :=
  count_normalizedFactors_eq' ((Ideal.isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (by haveI : Unique (Ideal R)ˣ := Ideal.uniqueUnits; apply normalize_eq)
    (by convert ideal.dvd_iff_le.mpr hle) (by convert mt Ideal.le_of_dvd hlt)
#align ideal.count_normalized_factors_eq Ideal.count_normalizedFactors_eq

/- Warning: even though a pure term-mode proof typechecks (the `by convert` can simply be
  removed), it's slower to the point of a possible timeout. -/
end

theorem Ideal.le_mul_of_no_prime_factors {I J K : Ideal R}
    (coprime : ∀ P, J ≤ P → K ≤ P → ¬IsPrime P) (hJ : I ≤ J) (hK : I ≤ K) : I ≤ J * K :=
  by
  simp only [← Ideal.dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, MulZeroClass.zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  exact
    mul_dvd_mul_left K
      (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors hJ0
        (fun P hPJ hPK => mt Ideal.isPrime_of_prime (coprime P hPJ hPK)) hJ)
#align ideal.le_mul_of_no_prime_factors Ideal.le_mul_of_no_prime_factors

theorem Ideal.le_of_pow_le_prime {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (h : I ^ n ≤ P) : I ≤ P :=
  by
  by_cases hP0 : P = ⊥
  · simp only [hP0, le_bot_iff] at h ⊢
    exact pow_eq_zero h
  rw [← Ideal.dvd_iff_le] at h ⊢
  exact ((Ideal.prime_iff_isPrime hP0).mpr hP).dvd_of_dvd_pow h
#align ideal.le_of_pow_le_prime Ideal.le_of_pow_le_prime

theorem Ideal.pow_le_prime_iff {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (hn : n ≠ 0) :
    I ^ n ≤ P ↔ I ≤ P :=
  ⟨Ideal.le_of_pow_le_prime, fun h => trans (Ideal.pow_le_self hn) h⟩
#align ideal.pow_le_prime_iff Ideal.pow_le_prime_iff

theorem Ideal.prod_le_prime {ι : Type _} {s : Finset ι} {f : ι → Ideal R} {P : Ideal R}
    [hP : P.IsPrime] : (∏ i in s, f i) ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  by
  by_cases hP0 : P = ⊥
  · simp only [hP0, le_bot_iff]
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
  simp only [← Ideal.dvd_iff_le]
  exact ((Ideal.prime_iff_isPrime hP0).mpr hP).dvd_finset_prod_iff _
#align ideal.prod_le_prime Ideal.prod_le_prime

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i j «expr ∈ » s) -/
/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers. -/
theorem IsDedekindDomain.inf_prime_pow_eq_prod {ι : Type _} (s : Finset ι) (f : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (f i))
    (coprime : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), i ≠ j → f i ≠ f j) :
    (s.inf fun i => f i ^ e i) = ∏ i in s, f i ^ e i :=
  by
  letI := Classical.decEq ι
  revert prime coprime
  refine' s.induction _ _
  · simp
  intro a s ha ih prime coprime
  specialize
    ih (fun i hi => Prime i (Finset.mem_insert_of_mem hi)) fun i hi j hj =>
      coprime i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
  rw [Finset.inf_insert, Finset.prod_insert ha, ih]
  refine' le_antisymm (Ideal.le_mul_of_no_prime_factors _ inf_le_left inf_le_right) Ideal.mul_le_inf
  intro P hPa hPs hPp
  haveI := hPp
  obtain ⟨b, hb, hPb⟩ := ideal.prod_le_prime.mp hPs
  haveI := Ideal.isPrime_of_prime (Prime a (Finset.mem_insert_self a s))
  haveI := Ideal.isPrime_of_prime (Prime b (Finset.mem_insert_of_mem hb))
  refine'
    coprime a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) _
      (((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq _).mp
            (Ideal.le_of_pow_le_prime hPa)).trans
        ((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq _).mp
            (Ideal.le_of_pow_le_prime hPb)).symm)
  · rintro rfl; contradiction
  · exact (Prime a (Finset.mem_insert_self a s)).NeZero
  · exact (Prime b (Finset.mem_insert_of_mem hb)).NeZero
#align is_dedekind_domain.inf_prime_pow_eq_prod IsDedekindDomain.inf_prime_pow_eq_prod

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def IsDedekindDomain.quotientEquivPiOfProdEq {ι : Type _} [Fintype ι] (I : Ideal R)
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i, Prime (P i)) (coprime : ∀ i j, i ≠ j → P i ≠ P j)
    (prod_eq : (∏ i, P i ^ e i) = I) : R ⧸ I ≃+* ∀ i, R ⧸ P i ^ e i :=
  (Ideal.quotEquivOfEq
        (by
          simp only [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ, ciInf_pos, ←
            IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun i _ => Prime i) fun i _ j _ =>
              coprime i j])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij =>
      Ideal.coprime_of_no_prime_ge
        (by
          intro P hPi hPj hPp
          haveI := hPp
          haveI := Ideal.isPrime_of_prime (Prime i); haveI := Ideal.isPrime_of_prime (Prime j)
          exact
            coprime i j hij
              (((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq (Prime i).NeZero).mp
                    (Ideal.le_of_pow_le_prime hPi)).trans
                ((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq (Prime j).NeZero).mp
                    (Ideal.le_of_pow_le_prime hPj)).symm))
#align is_dedekind_domain.quotient_equiv_pi_of_prod_eq IsDedekindDomain.quotientEquivPiOfProdEq

open scoped Classical

/-- **Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multiplicities. -/
noncomputable def IsDedekindDomain.quotientEquivPiFactors {I : Ideal R} (hI : I ≠ ⊥) :
    R ⧸ I ≃+* ∀ P : (factors I).toFinset, R ⧸ (P : Ideal R) ^ (factors I).count P :=
  IsDedekindDomain.quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.Prop))
    (fun i j hij => Subtype.coe_injective.Ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P in (factors I).toFinset, P ^ (factors I).count P :=
        (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
      _ = ((factors I).map fun P => P).Prod := (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).Prod := by rw [Multiset.map_id']
      _ = I := (@associated_iff_eq (Ideal R) _ Ideal.uniqueUnits _ _).mp (factors_prod hI)
      )
#align is_dedekind_domain.quotient_equiv_pi_factors IsDedekindDomain.quotientEquivPiFactors

@[simp]
theorem IsDedekindDomain.quotientEquivPiFactors_mk {I : Ideal R} (hI : I ≠ ⊥) (x : R) :
    IsDedekindDomain.quotientEquivPiFactors hI (Ideal.Quotient.mk I x) = fun P =>
      Ideal.Quotient.mk _ x :=
  rfl
#align is_dedekind_domain.quotient_equiv_pi_factors_mk IsDedekindDomain.quotientEquivPiFactors_mk

/-- **Chinese remainder theorem**, specialized to two ideals. -/
noncomputable def Ideal.quotientMulEquivQuotientProd (I J : Ideal R) (coprime : I ⊔ J = ⊤) :
    R ⧸ I * J ≃+* (R ⧸ I) × R ⧸ J :=
  RingEquiv.trans (Ideal.quotEquivOfEq (inf_eq_mul_of_coprime coprime).symm)
    (Ideal.quotientInfEquivQuotientProd I J coprime)
#align ideal.quotient_mul_equiv_quotient_prod Ideal.quotientMulEquivQuotientProd

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i j «expr ∈ » s) -/
/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i in s, P i ^ e i`, then `R ⧸ I` factors as `Π (i : s), R ⧸ (P i ^ e i)`.

This is a version of `is_dedekind_domain.quotient_equiv_pi_of_prod_eq` where we restrict
the product to a finite subset `s` of a potentially infinite indexing type `ι`.
-/
noncomputable def IsDedekindDomain.quotientEquivPiOfFinsetProdEq {ι : Type _} {s : Finset ι}
    (I : Ideal R) (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), i ≠ j → P i ≠ P j)
    (prod_eq : (∏ i in s, P i ^ e i) = I) : R ⧸ I ≃+* ∀ i : s, R ⧸ P i ^ e i :=
  IsDedekindDomain.quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => Prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.Ne h))
    (trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)
#align is_dedekind_domain.quotient_equiv_pi_of_finset_prod_eq IsDedekindDomain.quotientEquivPiOfFinsetProdEq

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i j «expr ∈ » s) -/
/-- Corollary of the Chinese remainder theorem: given elements `x i : R / P i ^ e i`,
we can choose a representative `y : R` such that `y ≡ x i (mod P i ^ e i)`.-/
theorem IsDedekindDomain.exists_representative_mod_finset {ι : Type _} {s : Finset ι}
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), i ≠ j → P i ≠ P j) (x : ∀ i : s, R ⧸ P i ^ e i) :
    ∃ y, ∀ (i) (hi : i ∈ s), Ideal.Quotient.mk (P i ^ e i) y = x ⟨i, hi⟩ :=
  by
  let f := IsDedekindDomain.quotientEquivPiOfFinsetProdEq _ P e Prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i hi => rfl⟩
#align is_dedekind_domain.exists_representative_mod_finset IsDedekindDomain.exists_representative_mod_finset

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i j «expr ∈ » s) -/
/-- Corollary of the Chinese remainder theorem: given elements `x i : R`,
we can choose a representative `y : R` such that `y - x i ∈ P i ^ e i`.-/
theorem IsDedekindDomain.exists_forall_sub_mem_ideal {ι : Type _} {s : Finset ι} (P : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), i ≠ j → P i ≠ P j) (x : s → R) :
    ∃ y, ∀ (i) (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ P i ^ e i :=
  by
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.exists_representative_mod_finset P e Prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => ideal.quotient.eq.mp (hy i hi)⟩
#align is_dedekind_domain.exists_forall_sub_mem_ideal IsDedekindDomain.exists_forall_sub_mem_ideal

end DedekindDomain

end ChineseRemainder

section PID

open multiplicity UniqueFactorizationMonoid Ideal

variable {R} [IsDomain R] [IsPrincipalIdealRing R]

theorem span_singleton_dvd_span_singleton_iff_dvd {a b : R} :
    Ideal.span {a} ∣ Ideal.span ({b} : Set R) ↔ a ∣ b :=
  ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩
#align span_singleton_dvd_span_singleton_iff_dvd span_singleton_dvd_span_singleton_iff_dvd

theorem singleton_span_mem_normalizedFactors_of_mem_normalizedFactors [NormalizationMonoid R]
    [DecidableEq R] [DecidableEq (Ideal R)] {a b : R} (ha : a ∈ normalizedFactors b) :
    Ideal.span ({a} : Set R) ∈ normalizedFactors (Ideal.span ({b} : Set R)) :=
  by
  by_cases hb : b = 0
  · rw [ideal.span_singleton_eq_bot.mpr hb, bot_eq_zero, normalized_factors_zero]
    rw [hb, normalized_factors_zero] at ha 
    simpa only [Multiset.not_mem_zero]
  · suffices Prime (Ideal.span ({a} : Set R))
      by
      obtain ⟨c, hc, hc'⟩ :=
        exists_mem_normalized_factors_of_dvd _ this.irreducible
          (dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr (dvd_of_mem_normalized_factors ha)))
      rwa [associated_iff_eq.mp hc']
      · by_contra
        exact hb (span_singleton_eq_bot.mp h)
    rw [prime_iff_is_prime]
    exact
      (span_singleton_prime (prime_of_normalized_factor a ha).NeZero).mpr
        (prime_of_normalized_factor a ha)
    by_contra
    exact (prime_of_normalized_factor a ha).NeZero (span_singleton_eq_bot.mp h)
#align singleton_span_mem_normalized_factors_of_mem_normalized_factors singleton_span_mem_normalizedFactors_of_mem_normalizedFactors

theorem multiplicity_eq_multiplicity_span [DecidableRel ((· ∣ ·) : R → R → Prop)]
    [DecidableRel ((· ∣ ·) : Ideal R → Ideal R → Prop)] {a b : R} :
    multiplicity (Ideal.span {a}) (Ideal.span ({b} : Set R)) = multiplicity a b :=
  by
  by_cases h : Finite a b
  · rw [← PartENat.natCast_get (finite_iff_dom.mp h)]
    refine'
        (multiplicity.unique
            (show Ideal.span {a} ^ (multiplicity a b).get h ∣ Ideal.span {b} from _) _).symm <;>
      rw [Ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
    exact pow_multiplicity_dvd h
    ·
      exact
        multiplicity.is_greatest
          ((PartENat.lt_coe_iff _ _).mpr (Exists.intro (finite_iff_dom.mp h) (Nat.lt_succ_self _)))
  · suffices ¬Finite (Ideal.span ({a} : Set R)) (Ideal.span ({b} : Set R))
      by
      rw [finite_iff_dom, PartENat.not_dom_iff_eq_top] at h this 
      rw [h, this]
    refine'
      not_finite_iff_forall.mpr fun n =>
        by
        rw [Ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
        exact not_finite_iff_forall.mp h n
#align multiplicity_eq_multiplicity_span multiplicity_eq_multiplicity_span

variable [DecidableEq R] [DecidableEq (Ideal R)] [NormalizationMonoid R]

/-- The bijection between the (normalized) prime factors of `r` and the (normalized) prime factors
    of `span {r}` -/
@[simps]
noncomputable def normalizedFactorsEquivSpanNormalizedFactors {r : R} (hr : r ≠ 0) :
    { d : R | d ∈ normalizedFactors r } ≃
      { I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R)) } :=
  Equiv.ofBijective
    (fun d =>
      ⟨Ideal.span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.Prop⟩)
    (by
      constructor
      · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
        rw [Subtype.mk_eq_mk, Ideal.span_singleton_eq_span_singleton, Subtype.coe_mk,
          Subtype.coe_mk] at h 
        exact subtype.mk_eq_mk.mpr (mem_normalized_factors_eq_of_associated ha hb h)
      · rintro ⟨i, hi⟩
        letI : i.is_principal := inferInstance
        letI : i.is_prime := is_prime_of_prime (prime_of_normalized_factor i hi)
        obtain ⟨a, ha, ha'⟩ :=
          exists_mem_normalized_factors_of_dvd hr
            (Submodule.IsPrincipal.prime_generator_of_isPrime i
                (prime_of_normalized_factor i hi).NeZero).Irreducible
            _
        · use ⟨a, ha⟩
          simp only [Subtype.coe_mk, Subtype.mk_eq_mk, ← span_singleton_eq_span_singleton.mpr ha',
            Ideal.span_singleton_generator]
        ·
          exact
            (Submodule.IsPrincipal.mem_iff_generator_dvd i).mp
              ((show Ideal.span {r} ≤ i from dvd_iff_le.mp (dvd_of_mem_normalized_factors hi))
                (mem_span_singleton.mpr (dvd_refl r))))
#align normalized_factors_equiv_span_normalized_factors normalizedFactorsEquivSpanNormalizedFactors

variable [DecidableRel ((· ∣ ·) : R → R → Prop)] [DecidableRel ((· ∣ ·) : Ideal R → Ideal R → Prop)]

/-- The bijection `normalized_factors_equiv_span_normalized_factors` between the set of prime
    factors of `r` and the set of prime factors of the ideal `⟨r⟩` preserves multiplicities. -/
theorem multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity {r d : R}
    (hr : r ≠ 0) (hd : d ∈ normalizedFactors r) :
    multiplicity d r =
      multiplicity (normalizedFactorsEquivSpanNormalizedFactors hr ⟨d, hd⟩ : Ideal R)
        (Ideal.span {r}) :=
  by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, multiplicity_eq_multiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]
#align multiplicity_normalized_factors_equiv_span_normalized_factors_eq_multiplicity multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity

/-- The bijection `normalized_factors_equiv_span_normalized_factors.symm` between the set of prime
    factors of the ideal `⟨r⟩` and the set of prime factors of `r` preserves multiplicities. -/
theorem multiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_multiplicity {r : R}
    (hr : r ≠ 0) (I : { I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R)) }) :
    multiplicity ((normalizedFactorsEquivSpanNormalizedFactors hr).symm I : R) r =
      multiplicity (I : Ideal R) (Ideal.span {r}) :=
  by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).Surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm, Equiv.symm_apply_apply, Subtype.coe_mk,
    multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity hr ha, hx]
#align multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity multiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_multiplicity

end PID

