/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Algebra.Subalgebra.Pointwise
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.RingTheory.ChainOfDivisors
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations

#align_import ring_theory.dedekind_domain.ideal from "leanprover-community/mathlib"@"2bbc7e3884ba234309d2a43b19144105a753292e"

/-!
# Dedekind domains and ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible.
Then we prove some results on the unique factorization monoid structure of the ideals.

## Main definitions

 - `IsDedekindDomainInv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `isDedekindDomainInv_iff` shows that this does note depend on the choice of field of
   fractions.
 - `IsDedekindDomain.HeightOneSpectrum` defines the type of nonzero prime ideals of `R`.

## Main results:
 - `isDedekindDomain_iff_isDedekindDomainInv`
 - `Ideal.uniqueFactorizationMonoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

section Inverse

namespace FractionalIdeal

variable {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]
variable {I J : FractionalIdeal R₁⁰ K}

noncomputable instance : Inv (FractionalIdeal R₁⁰ K) := ⟨fun I => 1 / I⟩

theorem inv_eq : I⁻¹ = 1 / I := rfl
#align fractional_ideal.inv_eq FractionalIdeal.inv_eq

theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 := div_zero
#align fractional_ideal.inv_zero' FractionalIdeal.inv_zero'

theorem inv_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, fractional_div_of_nonzero h⟩ := div_nonzero h
#align fractional_ideal.inv_nonzero FractionalIdeal.inv_nonzero

theorem coe_inv_of_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / (J : Submodule R₁ K) := by
  simp_rw [inv_nonzero _ h, coe_one, coe_mk, IsLocalization.coeSubmodule_top]
#align fractional_ideal.coe_inv_of_nonzero FractionalIdeal.coe_inv_of_nonzero

variable {K}

theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : FractionalIdeal R₁⁰ K) :=
  mem_div_iff_of_nonzero hI
#align fractional_ideal.mem_inv_iff FractionalIdeal.mem_inv_iff

theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ := by
  -- Porting note: in Lean3, introducing `x` would just give `x ∈ J⁻¹ → x ∈ I⁻¹`, but
  --  in Lean4, it goes all the way down to the subtypes
  intro x
  simp only [val_eq_coe, mem_coe, mem_inv_iff hJ, mem_inv_iff hI]
  exact fun h y hy => h y (hIJ hy)
#align fractional_ideal.inv_anti_mono FractionalIdeal.inv_anti_mono

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * I⁻¹ :=
  le_self_mul_one_div hI
#align fractional_ideal.le_self_mul_inv FractionalIdeal.le_self_mul_inv

variable (K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) :
    (I : FractionalIdeal R₁⁰ K) ≤ I * (I : FractionalIdeal R₁⁰ K)⁻¹ :=
  le_self_mul_inv coeIdeal_le_one
#align fractional_ideal.coe_ideal_le_self_mul_inv FractionalIdeal.coe_ideal_le_self_mul_inv

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ := by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1 from
    congr_arg Units.inv <| @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
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

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    I⁻¹.map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ := by rw [inv_eq, map_div, map_one, inv_eq]
#align fractional_ideal.map_inv FractionalIdeal.map_inv

open Submodule Submodule.IsPrincipal

@[simp]
theorem spanSingleton_inv (x : K) : (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹ :=
  one_div_spanSingleton x
#align fractional_ideal.span_singleton_inv FractionalIdeal.spanSingleton_inv

-- @[simp] -- Porting note: not in simpNF form
theorem spanSingleton_div_spanSingleton (x y : K) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R₁⁰ (x / y) := by
  rw [div_spanSingleton, mul_comm, spanSingleton_mul_spanSingleton, div_eq_mul_inv]
#align fractional_ideal.span_singleton_div_span_singleton FractionalIdeal.spanSingleton_div_spanSingleton

theorem spanSingleton_div_self {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ x = 1 := by
  rw [spanSingleton_div_spanSingleton, div_self hx, spanSingleton_one]
#align fractional_ideal.span_singleton_div_self FractionalIdeal.spanSingleton_div_self

theorem coe_ideal_span_singleton_div_self {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) / Ideal.span ({x} : Set R₁) = 1 := by
  rw [coeIdeal_span_singleton,
    spanSingleton_div_self K <|
      (map_ne_zero_iff _ <| NoZeroSMulDivisors.algebraMap_injective R₁ K).mpr hx]
#align fractional_ideal.coe_ideal_span_singleton_div_self FractionalIdeal.coe_ideal_span_singleton_div_self

theorem spanSingleton_mul_inv {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1 := by
  rw [spanSingleton_inv, spanSingleton_mul_spanSingleton, mul_inv_cancel hx, spanSingleton_one]
#align fractional_ideal.span_singleton_mul_inv FractionalIdeal.spanSingleton_mul_inv

theorem coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) *
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ = 1 := by
  rw [coeIdeal_span_singleton,
    spanSingleton_mul_inv K <|
      (map_ne_zero_iff _ <| NoZeroSMulDivisors.algebraMap_injective R₁ K).mpr hx]
#align fractional_ideal.coe_ideal_span_singleton_mul_inv FractionalIdeal.coe_ideal_span_singleton_mul_inv

theorem spanSingleton_inv_mul {x : K} (hx : x ≠ 0) :
    (spanSingleton R₁⁰ x)⁻¹ * spanSingleton R₁⁰ x = 1 := by
  rw [mul_comm, spanSingleton_mul_inv K hx]
#align fractional_ideal.span_singleton_inv_mul FractionalIdeal.spanSingleton_inv_mul

theorem coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ * Ideal.span ({x} : Set R₁) = 1 := by
  rw [mul_comm, coe_ideal_span_singleton_mul_inv K hx]
#align fractional_ideal.coe_ideal_span_singleton_inv_mul FractionalIdeal.coe_ideal_span_singleton_inv_mul

theorem mul_generator_self_inv {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 := by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton, mul_inv_cancel, spanSingleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I, generator_I_eq_zero, spanSingleton_zero]
#align fractional_ideal.mul_generator_self_inv FractionalIdeal.mul_generator_self_inv

theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) : I * I⁻¹ = 1 :=
  mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩
#align fractional_ideal.invertible_of_principal FractionalIdeal.invertible_of_principal

theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) ≠ 0 := by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_spanSingleton_of_principal I, hg, spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I : Submodule R₁ K))
    rw [hI, mem_zero_iff] at this
    contradiction
#align fractional_ideal.invertible_iff_generator_nonzero FractionalIdeal.invertible_iff_generator_nonzero

theorem isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
    (h : I ≠ 0) : Submodule.IsPrincipal I⁻¹.1 := by
  rw [val_eq_coe, isPrincipal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
    mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm
#align fractional_ideal.is_principal_inv FractionalIdeal.isPrincipal_inv


noncomputable instance : InvOneClass (FractionalIdeal R₁⁰ K) := { inv_one := div_one }

end FractionalIdeal

section IsDedekindDomainInv

variable [IsDomain A]
/-- A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `IsDedekindDomain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `IsDedekindDomain A`, which implies `IsDedekindDomainInv`. For **integral** ideals,
`IsDedekindDomain`(`_inv`) implies only `Ideal.cancelCommMonoidWithZero`.
-/
def IsDedekindDomainInv : Prop :=
  ∀ I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1
#align is_dedekind_domain_inv IsDedekindDomainInv

open FractionalIdeal

variable {R A K}

theorem isDedekindDomainInv_iff [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomainInv A ↔ ∀ I ≠ (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 := by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h, IsDedekindDomainInv]
#align is_dedekind_domain_inv_iff isDedekindDomainInv_iff

theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 := by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : I * I = I := by apply coeToSubmodule_injective; simp [I]
  convert congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_iff_isUnit K).mpr hI, mul_assoc, mul_one]
#align fractional_ideal.adjoin_integral_eq_one_of_is_unit FractionalIdeal.adjoinIntegral_eq_one_of_isUnit

namespace IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K] (h : IsDedekindDomainInv A)

theorem mul_inv_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : I * I⁻¹ = 1 :=
  isDedekindDomainInv_iff.mp h I hI
#align is_dedekind_domain_inv.mul_inv_eq_one IsDedekindDomainInv.mul_inv_eq_one

theorem inv_mul_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : I⁻¹ * I = 1 :=
  (mul_comm _ _).trans (h.mul_inv_eq_one hI)
#align is_dedekind_domain_inv.inv_mul_eq_one IsDedekindDomainInv.inv_mul_eq_one

protected theorem isUnit {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : IsUnit I :=
  isUnit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)
#align is_dedekind_domain_inv.is_unit IsDedekindDomainInv.isUnit

theorem isNoetherianRing : IsNoetherianRing A := by
  refine isNoetherianRing_iff.mpr ⟨fun I : Ideal A => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
  exact I.fg_of_isUnit (IsFractionRing.injective A (FractionRing A)) (h.isUnit hI)
#align is_dedekind_domain_inv.is_noetherian_ring IsDedekindDomainInv.isNoetherianRing

theorem integrallyClosed : IsIntegrallyClosed A := by
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr (fun {x hx} => ?_)
  rw [← Set.mem_range, ← Algebra.mem_bot, ← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot,
    Submodule.one_eq_span, ← coe_spanSingleton A⁰ (1 : FractionRing A), spanSingleton_one, ←
    FractionalIdeal.adjoinIntegral_eq_one_of_isUnit x hx (h.isUnit _)]
  · exact mem_adjoinIntegral_self A⁰ x hx
  · exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Algebra.adjoin A {x}).one_mem)
#align is_dedekind_domain_inv.integrally_closed IsDedekindDomainInv.integrallyClosed

open Ring

theorem dimensionLEOne : DimensionLEOne A := ⟨by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  rintro P P_ne hP
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun M hM => ?_⟩
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hM.ne_bot
  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P ≤ P by
    rw [eq_top_iff, ← coeIdeal_le_coeIdeal (FractionRing A), coeIdeal_top]
    calc
      (1 : FractionalIdeal A⁰ (FractionRing A)) = _ * _ * _ := ?_
      _ ≤ _ * _ := mul_right_mono
        ((P : FractionalIdeal A⁰ (FractionRing A))⁻¹ * M : FractionalIdeal A⁰ (FractionRing A)) this
      _ = M := ?_
    · rw [mul_assoc, ← mul_assoc (P : FractionalIdeal A⁰ (FractionRing A)), h.mul_inv_eq_one P'_ne,
      one_mul, h.inv_mul_eq_one M'_ne]
    · rw [← mul_assoc (P : FractionalIdeal A⁰ (FractionRing A)), h.mul_inv_eq_one P'_ne, one_mul]
  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebraMap _ _ y` for some `y`.
  intro x hx
  have le_one : (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P ≤ 1 := by
    rw [← h.inv_mul_eq_one M'_ne]
    exact mul_left_mono _ ((coeIdeal_le_coeIdeal (FractionRing A)).mpr hM.le)
  obtain ⟨y, _hy, rfl⟩ := (mem_coeIdeal _).mp (le_one hx)
  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := mul_mem_mul (mem_coeIdeal_of_mem A⁰ hzM) hx
  rw [← RingHom.map_mul, ← mul_assoc, h.mul_inv_eq_one M'_ne, one_mul] at zy_mem
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coeIdeal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coeIdeal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)⟩
#align is_dedekind_domain_inv.dimension_le_one IsDedekindDomainInv.dimensionLEOne

/-- Showing one side of the equivalence between the definitions
`IsDedekindDomainInv` and `IsDedekindDomain` of Dedekind domains. -/
theorem isDedekindDomain : IsDedekindDomain A :=
  { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }
#align is_dedekind_domain_inv.is_dedekind_domain IsDedekindDomainInv.isDedekindDomain

end IsDedekindDomainInv

end IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

theorem one_mem_inv_coe_ideal [IsDomain A] {I : Ideal A} (hI : I ≠ ⊥) :
    (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy
-- #align fractional_ideal.one_mem_inv_coe_ideal FractionalIdeal.one_mem_inv_coe_ideal

/-- Specialization of `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : Ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
theorem exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsField A)
    {I M : Ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧
        ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I := by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).prod ≠ ⊥}
      ⟨Z₀, hZ₀.1, hZ₀.2⟩
  obtain ⟨_, hPZ', hPM⟩ := hM.isPrime.multiset_prod_le.mp (hZI.trans hIM)
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := Multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase PrimeSpectrum.asIdeal PrimeSpectrum.ext P Z
    obtain ⟨hP0, hZP0⟩ : P.asIdeal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).prod ≠ ⊥ := by
      rwa [Ne, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ
    -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
    have hPM' := (P.isPrime.isMaximal hP0).eq_of_le hM.ne_top hPM
    subst hPM'
    -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
    refine ⟨Z.erase P, ?_, ?_⟩
    · convert hZI
      rw [this, Multiset.cons_erase hPZ']
    · refine fun h => h_eraseZ (Z.erase P) ⟨h, ?_⟩ (Multiset.erase_lt.mpr hPZ)
      exact hZP0
#align exists_multiset_prod_cons_le_and_prod_not_le exists_multiset_prod_cons_le_and_prod_not_le
namespace FractionalIdeal

open Ideal

lemma not_inv_le_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A}
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) : ¬(I⁻¹ : FractionalIdeal A⁰ K) ≤ 1 := by
  have hNF : ¬IsField A := fun h ↦ letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M ≠ ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_ ?_) (this hMbot hmax.ne_top hmax) <;>
      simpa only [coeIdeal_ne_zero, coeIdeal_le_coeIdeal]
  have hI0 : ⊥ < I := I.bot_lt_of_maximal hNF
  obtain ⟨⟨a, haI⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt hI0
  replace ha0 : a ≠ 0 := Subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
  have hJI : J ≤ I := I.span_singleton_le_iff_mem.2 haI
  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJI
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := SetLike.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine Set.not_subset.2 ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff ?_).mpr ?_, ?_⟩
  · exact coeIdeal_ne_zero.mpr hI0.ne'
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coeIdeal _).mp hy₀
    rw [mul_comm, ← mul_assoc, ← RingHom.map_mul]
    have h_yb : y * b ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, RingHom.map_mul, mul_assoc, mul_inv_cancel hnz_fa, mul_one]
    apply coe_mem_one
  · refine mt (mem_one_iff _).mp ?_
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← RingHom.map_mul] at h₂_abs
    have := Ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction

theorem exists_not_mem_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI1 : I ≠ ⊤) : ∃ x ∈ (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : FractionalIdeal A⁰ K) :=
  Set.not_subset.1 <| not_inv_le_one_of_ne_bot hI0 hI1
#align fractional_ideal.exists_not_mem_one_of_ne_bot FractionalIdeal.exists_not_mem_one_of_ne_bot

theorem mul_inv_cancel_of_le_one [h : IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ ≤ 1) : I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show a contradiction with `exists_not_mem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_le_one
  by_cases hJ0 : J = ⊥
  · subst hJ0
    refine absurd ?_ hI0
    rw [eq_bot_iff, ← coeIdeal_le_coeIdeal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
  by_cases hJ1 : J = ⊤
  · rw [← hJ, hJ1, coeIdeal_top]
  exact (not_inv_le_one_of_ne_bot (K := K) hJ0 hJ1 (hJ ▸ hI)).elim
#align fractional_ideal.mul_inv_cancel_of_le_one FractionalIdeal.mul_inv_cancel_of_le_one

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
theorem coe_ideal_mul_inv [h : IsDedekindDomain A] (I : Ideal A) (hI0 : I ≠ ⊥) :
    I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot, Set.mem_range,
      ← mem_one_iff] at this
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integralClosure_iff_mem_fg]
  have x_mul_mem : ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), x * b ∈ (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI0)]
    dsimp only at hx
    rw [val_eq_coe, mem_coe, mem_inv_iff hJ0] at hx
    simp only [mul_assoc, mul_comm b] at hx ⊢
    intro y hy
    exact hx _ (mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine ⟨AlgHom.range (Polynomial.aeval x : A[X] →ₐ[A] K),
    isNoetherian_submodule.mp (isNoetherian (I : FractionalIdeal A⁰ K)⁻¹) _ fun y hy => ?_,
    ⟨Polynomial.X, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  clear hi
  induction' i with i ih
  · rw [pow_zero]; exact one_mem_inv_coe_ideal hI0
  · show x ^ i.succ ∈ (I⁻¹ : FractionalIdeal A⁰ K)
    rw [pow_succ']; exact x_mul_mem _ ih
#align fractional_ideal.coe_ideal_mul_inv FractionalIdeal.coe_ideal_mul_inv

/-- Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`Semifield` instance defined below.
-/
protected theorem mul_inv_cancel [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hne : I ≠ 0) :
    I * I⁻¹ = 1 := by
  obtain ⟨a, J, ha, hJ⟩ :
    ∃ (a : A) (aI : Ideal A), a ≠ 0 ∧ I = spanSingleton A⁰ (algebraMap A K a)⁻¹ * aI :=
    exists_eq_spanSingleton_mul I
  suffices h₂ : I * (spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ K)⁻¹) = 1 by
    rw [mul_inv_cancel_iff]
    exact ⟨spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ K)⁻¹, h₂⟩
  subst hJ
  rw [mul_assoc, mul_left_comm (J : FractionalIdeal A⁰ K), coe_ideal_mul_inv, mul_one,
    spanSingleton_mul_spanSingleton, inv_mul_cancel, spanSingleton_one]
  · exact mt ((injective_iff_map_eq_zero (algebraMap A K)).mp (IsFractionRing.injective A K) _) ha
  · exact coeIdeal_ne_zero.mp (right_ne_zero_of_mul hne)
#align fractional_ideal.mul_inv_cancel FractionalIdeal.mul_inv_cancel

theorem mul_right_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) :
    ∀ {I I'}, I * J ≤ I' * J ↔ I ≤ I' := by
  intro I I'
  constructor
  · intro h
    convert mul_right_mono J⁻¹ h <;> dsimp only <;>
    rw [mul_assoc, FractionalIdeal.mul_inv_cancel hJ, mul_one]
  · exact fun h => mul_right_mono J h
#align fractional_ideal.mul_right_le_iff FractionalIdeal.mul_right_le_iff

theorem mul_left_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) {I I'} :
    J * I ≤ J * I' ↔ I ≤ I' := by convert mul_right_le_iff hJ using 1; simp only [mul_comm]
#align fractional_ideal.mul_left_le_iff FractionalIdeal.mul_left_le_iff

theorem mul_right_strictMono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    StrictMono (· * I) :=
  strictMono_of_le_iff_le fun _ _ => (mul_right_le_iff hI).symm
#align fractional_ideal.mul_right_strict_mono FractionalIdeal.mul_right_strictMono

theorem mul_left_strictMono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    StrictMono (I * ·) :=
  strictMono_of_le_iff_le fun _ _ => (mul_left_le_iff hI).symm
#align fractional_ideal.mul_left_strict_mono FractionalIdeal.mul_left_strictMono

/-- This is also available as `_root_.div_eq_mul_inv`, using the
`Semifield` instance defined below.
-/
protected theorem div_eq_mul_inv [IsDedekindDomain A] (I J : FractionalIdeal A⁰ K) :
    I / J = I * J⁻¹ := by
  by_cases hJ : J = 0
  · rw [hJ, div_zero, inv_zero', mul_zero]
  refine le_antisymm ((mul_right_le_iff hJ).mp ?_) ((le_div_iff_mul_le hJ).mpr ?_)
  · rw [mul_assoc, mul_comm J⁻¹, FractionalIdeal.mul_inv_cancel hJ, mul_one, mul_le]
    intro x hx y hy
    rw [mem_div_iff_of_nonzero hJ] at hx
    exact hx y hy
  rw [mul_assoc, mul_comm J⁻¹, FractionalIdeal.mul_inv_cancel hJ, mul_one]
#align fractional_ideal.div_eq_mul_inv FractionalIdeal.div_eq_mul_inv

end FractionalIdeal

/-- `IsDedekindDomain` and `IsDedekindDomainInv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem isDedekindDomain_iff_isDedekindDomainInv [IsDomain A] :
    IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun _h _I hI => FractionalIdeal.mul_inv_cancel hI, fun h => h.isDedekindDomain⟩
#align is_dedekind_domain_iff_is_dedekind_domain_inv isDedekindDomain_iff_isDedekindDomainInv

end Inverse

section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

open Ideal

noncomputable instance FractionalIdeal.semifield : Semifield (FractionalIdeal A⁰ K) where
  __ := coeIdeal_injective.nontrivial
  inv_zero := inv_zero' _
  div_eq_mul_inv := FractionalIdeal.div_eq_mul_inv
  mul_inv_cancel _ := FractionalIdeal.mul_inv_cancel
  nnqsmul := _
#align fractional_ideal.semifield FractionalIdeal.semifield

/-- Fractional ideals have cancellative multiplication in a Dedekind domain.

Although this instance is a direct consequence of the instance
`FractionalIdeal.semifield`, we define this instance to provide
a computable alternative.
-/
instance FractionalIdeal.cancelCommMonoidWithZero :
    CancelCommMonoidWithZero (FractionalIdeal A⁰ K) where
  __ : CommSemiring (FractionalIdeal A⁰ K) := inferInstance
#align fractional_ideal.cancel_comm_monoid_with_zero FractionalIdeal.cancelCommMonoidWithZero

instance Ideal.cancelCommMonoidWithZero : CancelCommMonoidWithZero (Ideal A) :=
  { Function.Injective.cancelCommMonoidWithZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
    (RingHom.map_zero _) (RingHom.map_one _) (RingHom.map_mul _) (RingHom.map_pow _) with }
#align ideal.cancel_comm_monoid_with_zero Ideal.cancelCommMonoidWithZero

-- Porting note: Lean can infer all it needs by itself
instance Ideal.isDomain : IsDomain (Ideal A) := { }
#align ideal.is_domain Ideal.isDomain

/-- For ideals in a Dedekind domain, to divide is to contain. -/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI, hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J ≤ 1 :=
      le_trans (mul_left_mono (↑I)⁻¹ ((coeIdeal_le_coeIdeal _).mpr h))
        (le_of_eq (inv_mul_cancel hI'))
    obtain ⟨H, hH⟩ := le_one_iff_exists_coeIdeal.mp this
    use H
    refine coeIdeal_injective (show (J : FractionalIdeal A⁰ (FractionRing A)) = ↑(I * H) from ?_)
    rw [coeIdeal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]⟩
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

instance : WfDvdMonoid (Ideal A) where
  wellFounded_dvdNotUnit := by
    have : WellFounded ((· > ·) : Ideal A → Ideal A → Prop) :=
      isNoetherian_iff_wellFounded.mp (isNoetherianRing_iff.mp IsDedekindRing.toIsNoetherian)
    convert this
    ext
    rw [Ideal.dvdNotUnit_iff_lt]

instance Ideal.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Ideal A) :=
  { irreducible_iff_prime := by
      intro P
      exact ⟨fun hirr => ⟨hirr.ne_zero, hirr.not_unit, fun I J => by
        have : P.IsMaximal := by
          refine ⟨⟨mt Ideal.isUnit_iff.mpr hirr.not_unit, ?_⟩⟩
          intro J hJ
          obtain ⟨_J_ne, H, hunit, P_eq⟩ := Ideal.dvdNotUnit_iff_lt.mpr hJ
          exact Ideal.isUnit_iff.mp ((hirr.isUnit_or_isUnit P_eq).resolve_right hunit)
        rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, SetLike.le_def, SetLike.le_def,
          SetLike.le_def]
        contrapose!
        rintro ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩
        exact
          ⟨x * y, Ideal.mul_mem_mul x_mem y_mem,
            mt this.isPrime.mem_or_mem (not_or_of_not x_not_mem y_not_mem)⟩⟩, Prime.irreducible⟩ }
#align ideal.unique_factorization_monoid Ideal.uniqueFactorizationMonoid

instance Ideal.normalizationMonoid : NormalizationMonoid (Ideal A) :=
  normalizationMonoidOfUniqueUnits
#align ideal.normalization_monoid Ideal.normalizationMonoid

@[simp]
theorem Ideal.dvd_span_singleton {I : Ideal A} {x : A} : I ∣ Ideal.span {x} ↔ x ∈ I :=
  Ideal.dvd_iff_le.trans (Ideal.span_le.trans Set.singleton_subset_iff)
#align ideal.dvd_span_singleton Ideal.dvd_span_singleton

theorem Ideal.isPrime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P := by
  refine ⟨?_, fun hxy => ?_⟩
  · rintro rfl
    rw [← Ideal.one_eq_top] at h
    exact h.not_unit isUnit_one
  · simp only [← Ideal.dvd_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy
#align ideal.is_prime_of_prime Ideal.isPrime_of_prime

theorem Ideal.prime_of_isPrime {P : Ideal A} (hP : P ≠ ⊥) (h : IsPrime P) : Prime P := by
  refine ⟨hP, mt Ideal.isUnit_iff.mp h.ne_top, fun I J hIJ => ?_⟩
  simpa only [Ideal.dvd_iff_le] using h.mul_le.mp (Ideal.le_of_dvd hIJ)
#align ideal.prime_of_is_prime Ideal.prime_of_isPrime

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `Ideal A`
are exactly the prime ideals. -/
theorem Ideal.prime_iff_isPrime {P : Ideal A} (hP : P ≠ ⊥) : Prime P ↔ IsPrime P :=
  ⟨Ideal.isPrime_of_prime, Ideal.prime_of_isPrime hP⟩
#align ideal.prime_iff_is_prime Ideal.prime_iff_isPrime

/-- In a Dedekind domain, the prime ideals are the zero ideal together with the prime elements
of the monoid with zero `Ideal A`. -/
theorem Ideal.isPrime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P :=
  ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => Ideal.prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ Ideal.bot_prime) Ideal.isPrime_of_prime⟩
#align ideal.is_prime_iff_bot_or_prime Ideal.isPrime_iff_bot_or_prime

@[simp]
theorem Ideal.prime_span_singleton_iff {a : A} : Prime (Ideal.span {a}) ↔ Prime a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Set.singleton_zero, span_zero, ← Ideal.zero_eq_bot, ← not_iff_not]
    simp only [not_prime_zero, not_false_eq_true]
  · have ha' : span {a} ≠ ⊥ := by simpa only [ne_eq, span_singleton_eq_bot] using ha
    rw [Ideal.prime_iff_isPrime ha', Ideal.span_singleton_prime ha]

open Submodule.IsPrincipal in
theorem Ideal.prime_generator_of_prime {P : Ideal A} (h : Prime P) [P.IsPrincipal] :
    Prime (generator P) :=
  have : Ideal.IsPrime P := Ideal.isPrime_of_prime h
  prime_generator_of_isPrime _ h.ne_zero

open UniqueFactorizationMonoid in
nonrec theorem Ideal.mem_normalizedFactors_iff {p I : Ideal A} (hI : I ≠ ⊥) :
    p ∈ normalizedFactors I ↔ p.IsPrime ∧ I ≤ p := by
  rw [← Ideal.dvd_iff_le]
  by_cases hp : p = 0
  · rw [← zero_eq_bot] at hI
    simp only [hp, zero_not_mem_normalizedFactors, zero_dvd_iff, hI, false_iff, not_and,
      not_false_eq_true, implies_true]
  · rwa [mem_normalizedFactors_iff hI, prime_iff_isPrime]

theorem Ideal.pow_right_strictAnti (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    StrictAnti (I ^ · : ℕ → Ideal A) :=
  strictAnti_nat_of_succ_lt fun e =>
    Ideal.dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ I e⟩
#align ideal.strict_anti_pow Ideal.pow_right_strictAnti

theorem Ideal.pow_lt_self (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) :
    I ^ e < I := by
  convert I.pow_right_strictAnti hI0 hI1 he
  dsimp only
  rw [pow_one]
#align ideal.pow_lt_self Ideal.pow_lt_self

theorem Ideal.exists_mem_pow_not_mem_pow_succ (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
    ∃ x ∈ I ^ e, x ∉ I ^ (e + 1) :=
  SetLike.exists_of_lt (I.pow_right_strictAnti hI0 hI1 e.lt_succ_self)
#align ideal.exists_mem_pow_not_mem_pow_succ Ideal.exists_mem_pow_not_mem_pow_succ

open UniqueFactorizationMonoid

theorem Ideal.eq_prime_pow_of_succ_lt_of_le {P I : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥)
    {i : ℕ} (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) : I = P ^ i := by
  refine le_antisymm hle ?_
  have P_prime' := Ideal.prime_of_isPrime hP P_prime
  have h1 : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have h3 := pow_ne_zero (i + 1) hP
  rw [← Ideal.dvdNotUnit_iff_lt, dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors h1 h3,
    normalizedFactors_pow, normalizedFactors_irreducible P_prime'.irreducible,
    Multiset.nsmul_singleton, Multiset.lt_replicate_succ] at hlt
  rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors, normalizedFactors_pow,
    normalizedFactors_irreducible P_prime'.irreducible, Multiset.nsmul_singleton]
  all_goals assumption
#align ideal.eq_prime_pow_of_succ_lt_of_le Ideal.eq_prime_pow_of_succ_lt_of_le

theorem Ideal.pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥) (i : ℕ) :
    P ^ (i + 1) < P ^ i :=
  lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ _))
    (mt (pow_eq_pow_iff hP (mt Ideal.isUnit_iff.mp P_prime.ne_top)).mp i.succ_ne_self)
#align ideal.pow_succ_lt_pow Ideal.pow_succ_lt_pow

theorem Associates.le_singleton_iff (x : A) (n : ℕ) (I : Ideal A) :
    Associates.mk I ^ n ≤ Associates.mk (Ideal.span {x}) ↔ x ∈ I ^ n := by
  simp_rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk,
    Ideal.dvd_span_singleton]
#align associates.le_singleton_iff Associates.le_singleton_iff

variable {K}

lemma FractionalIdeal.le_inv_comm {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J⁻¹ ↔ J ≤ I⁻¹ := by
  rw [inv_eq, inv_eq, le_div_iff_mul_le hI, le_div_iff_mul_le hJ, mul_comm]

lemma FractionalIdeal.inv_le_comm {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I⁻¹ ≤ J ↔ J⁻¹ ≤ I := by
  simpa using le_inv_comm (A := A) (K := K) (inv_ne_zero hI) (inv_ne_zero hJ)

open FractionalIdeal


/-- Strengthening of `IsLocalization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `A` that is not completely contained in `J`. -/
theorem Ideal.exist_integer_multiples_not_mem {J : Ideal A} (hJ : J ≠ ⊤) {ι : Type*} (s : Finset ι)
    (f : ι → K) {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
    ∃ a : K,
      (∀ i ∈ s, IsLocalization.IsInteger A (a * f i)) ∧
        ∃ i ∈ s, a * f i ∉ (J : FractionalIdeal A⁰ K) := by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := spanFinset A s f
  have hI0 : I ≠ 0 := spanFinset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI⟩ := SetLike.lt_iff_le_and_exists.mp this
    rw [mem_inv_iff hI0] at hI
    refine ⟨a, fun i hi => ?_, ?_⟩
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    · exact (mem_one_iff _).mp (hI (f i) (Submodule.subset_span (Set.mem_image_of_mem f hi)))
    · contrapose! hpI
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine (mem_div_iff_of_nonzero hI0).mpr fun y hy => Submodule.span_induction hy ?_ ?_ ?_ ?_
      · rintro _ ⟨i, hi, rfl⟩; exact hpI i hi
      · rw [mul_zero]; exact Submodule.zero_mem _
      · intro x y hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
      · intro b x hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  calc
    ↑J / I = ↑J * I⁻¹ := div_eq_mul_inv (↑J) I
    _ < 1 * I⁻¹ := mul_right_strictMono (inv_ne_zero hI0) ?_
    _ = I⁻¹ := one_mul _
  rw [← coeIdeal_top]
  -- And multiplying by `I⁻¹` is indeed strictly monotone.
  exact
    strictMono_of_le_iff_le (fun _ _ => (coeIdeal_le_coeIdeal K).symm)
      (lt_top_iff_ne_top.mpr hJ)
#align ideal.exist_integer_multiples_not_mem Ideal.exist_integer_multiples_not_mem

section Gcd

namespace Ideal

/-! ### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `NormalizedGCDMonoid (Ideal A)`.
-/


@[simp]
theorem sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I * J := by
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J := by
    rw [gcd_eq_normalize _ _, normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le, dvd_iff_le]
      simp
  have hlcm : lcm I J = I ⊓ J := by
    rw [lcm_eq_normalize _ _, normalize_eq]
    · rw [lcm_dvd_iff, dvd_iff_le, dvd_iff_le]
      simp
    · rw [dvd_iff_le, le_inf_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩
  rw [← hgcd, ← hlcm, associated_iff_eq.mp (gcd_mul_lcm _ _)]
#align ideal.sup_mul_inf Ideal.sup_mul_inf

/-- Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are compatible with
the normalization operator. -/
instance : NormalizedGCDMonoid (Ideal A) :=
  { Ideal.normalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := by
      simp only [dvd_iff_le]
      exact fun h1 h2 => @sup_le (Ideal A) _ _ _ _ h1 h2
    lcm := (· ⊓ ·)
    lcm_zero_left := fun _ => by simp only [zero_eq_bot, bot_inf_eq]
    lcm_zero_right := fun _ => by simp only [zero_eq_bot, inf_bot_eq]
    gcd_mul_lcm := fun _ _ => by rw [associated_iff_eq, sup_mul_inf]
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

-- In fact, any lawful gcd and lcm would equal sup and inf respectively.
@[simp]
theorem gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J := rfl
#align ideal.gcd_eq_sup Ideal.gcd_eq_sup

@[simp]
theorem lcm_eq_inf (I J : Ideal A) : lcm I J = I ⊓ J := rfl
#align ideal.lcm_eq_inf Ideal.lcm_eq_inf

theorem isCoprime_iff_gcd {I J : Ideal A} : IsCoprime I J ↔ gcd I J = 1 := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff, one_eq_top, gcd_eq_sup]

theorem factors_span_eq {p : K[X]} : factors (span {p}) = (factors p).map (fun q ↦ span {q}) := by
  rcases eq_or_ne p 0 with rfl | hp; · simpa [Set.singleton_zero] using normalizedFactors_zero
  have : ∀ q ∈ (factors p).map (fun q ↦ span {q}), Prime q := fun q hq ↦ by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    exact prime_span_singleton_iff.mpr <| prime_of_factor r hr
  rw [← span_singleton_eq_span_singleton.mpr (factors_prod hp), ← multiset_prod_span_singleton,
    factors_eq_normalizedFactors, normalizedFactors_prod_of_prime this]

end Ideal

end Gcd

end IsDedekindDomain

section IsDedekindDomain

variable {T : Type*} [CommRing T] [IsDedekindDomain T] {I J : Ideal T}

open scoped Classical

open Multiset UniqueFactorizationMonoid Ideal

theorem prod_normalizedFactors_eq_self (hI : I ≠ ⊥) : (normalizedFactors I).prod = I :=
  associated_iff_eq.1 (normalizedFactors_prod hI)
#align prod_normalized_factors_eq_self prod_normalizedFactors_eq_self

theorem count_le_of_ideal_ge {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
    count K (normalizedFactors J) ≤ count K (normalizedFactors I) :=
  le_iff_count.1 ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
    (dvd_iff_le.2 h))
    _
#align count_le_of_ideal_ge count_le_of_ideal_ge

theorem sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊔ J = (normalizedFactors I ∩ normalizedFactors J).prod := by
  have H : normalizedFactors (normalizedFactors I ∩ normalizedFactors J).prod =
      normalizedFactors I ∩ normalizedFactors J := by
    apply normalizedFactors_prod_of_prime
    intro p hp
    rw [mem_inter] at hp
    exact prime_of_normalized_factor p hp.left
  have := Multiset.prod_ne_zero_of_prime (normalizedFactors I ∩ normalizedFactors J) fun _ h =>
      prime_of_normalized_factor _ (Multiset.mem_inter.1 h).1
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor
    · rw [dvd_iff_normalizedFactors_le_normalizedFactors this hI, H]
      exact inf_le_left
    · rw [dvd_iff_normalizedFactors_le_normalizedFactors this hJ, H]
      exact inf_le_right
  · rw [← dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors,
      normalizedFactors_prod_of_prime, le_iff_count]
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
    normalizedFactors_of_irreducible_pow hJ, normalize_eq J, replicate_inter, prod_replicate]
#align irreducible_pow_sup irreducible_pow_sup

theorem irreducible_pow_sup_of_le (hJ : Irreducible J) (n : ℕ) (hn : ↑n ≤ multiplicity J I) :
    J ^ n ⊔ I = J ^ n := by
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ, min_eq_right]
  rwa [multiplicity_eq_count_normalizedFactors hJ hI, PartENat.coe_le_coe, normalize_eq J] at hn
#align irreducible_pow_sup_of_le irreducible_pow_sup_of_le

theorem irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ)
    (hn : multiplicity J I ≤ n) :
    J ^ n ⊔ I = J ^ (multiplicity J I).get (PartENat.dom_of_le_natCast hn) := by
  rw [irreducible_pow_sup hI hJ, min_eq_left]
  · congr
    rw [← PartENat.natCast_inj, PartENat.natCast_get,
      multiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J]
  · rwa [multiplicity_eq_count_normalizedFactors hJ hI, PartENat.coe_le_coe, normalize_eq J] at hn
#align irreducible_pow_sup_of_ge irreducible_pow_sup_of_ge

end IsDedekindDomain

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `HeightOneSpectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible.
-/


namespace IsDedekindDomain

variable [IsDedekindDomain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
-- Porting note(#5171): removed `has_nonempty_instance`, linter doesn't exist yet
@[ext, nolint unusedArguments]
structure HeightOneSpectrum where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  ne_bot : asIdeal ≠ ⊥
#align is_dedekind_domain.height_one_spectrum IsDedekindDomain.HeightOneSpectrum

attribute [instance] HeightOneSpectrum.isPrime

variable (v : HeightOneSpectrum R) {R}

namespace HeightOneSpectrum

instance isMaximal : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
#align is_dedekind_domain.height_one_spectrum.is_maximal IsDedekindDomain.HeightOneSpectrum.isMaximal

theorem prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
#align is_dedekind_domain.height_one_spectrum.prime IsDedekindDomain.HeightOneSpectrum.prime

theorem irreducible : Irreducible v.asIdeal :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.prime
#align is_dedekind_domain.height_one_spectrum.irreducible IsDedekindDomain.HeightOneSpectrum.irreducible

theorem associates_irreducible : Irreducible <| Associates.mk v.asIdeal :=
  Associates.irreducible_mk.mpr v.irreducible
#align is_dedekind_domain.height_one_spectrum.associates_irreducible IsDedekindDomain.HeightOneSpectrum.associates_irreducible

/-- An equivalence between the height one and maximal spectra for rings of Krull dimension 1. -/
def equivMaximalSpectrum (hR : ¬IsField R) : HeightOneSpectrum R ≃ MaximalSpectrum R where
  toFun v := ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot⟩
  invFun v :=
    ⟨v.asIdeal, v.IsMaximal.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.IsMaximal hR⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align is_dedekind_domain.height_one_spectrum.equiv_maximal_spectrum IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum

variable (R)

/-- A Dedekind domain is equal to the intersection of its localizations at all its height one
non-zero prime ideals viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot [Algebra R K] [hK : IsFractionRing R K] :
    (⨅ v : HeightOneSpectrum R,
        Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  on_goal 1 => by_cases hR : IsField R
  · rcases Function.bijective_iff_has_inverse.mp
      (IsField.localization_map_bijective (Rₘ := K) (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exact fun _ => Algebra.mem_bot.mpr ⟨algebra_map_inv x, algebra_map_right_inv x⟩
  all_goals rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
  · exact fun hx ⟨v, hv⟩ => hx ((equivMaximalSpectrum hR).symm ⟨v, hv⟩)
  · exact fun hx ⟨v, hv, hbot⟩ => hx ⟨v, hv.isMaximal hbot⟩
#align is_dedekind_domain.height_one_spectrum.infi_localization_eq_bot IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot

end HeightOneSpectrum

end IsDedekindDomain

section

open Ideal

variable {R A}
variable [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps] -- Porting note: use `Subtype` instead of `Set` to make linter happy
def idealFactorsFunOfQuotHom {f : R ⧸ I →+* A ⧸ J} (hf : Function.Surjective f) :
    {p : Ideal R // p ∣ I} →o {p : Ideal A // p ∣ J} where
  toFun X := ⟨comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)), by
    have : RingHom.ker (Ideal.Quotient.mk J) ≤
        comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)) :=
      ker_le_comap (Ideal.Quotient.mk J)
    rw [mk_ker] at this
    exact dvd_iff_le.mpr this⟩
  monotone' := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    rw [← Subtype.coe_le_coe, Subtype.coe_mk, Subtype.coe_mk] at h ⊢
    rw [Subtype.coe_mk, comap_le_comap_iff_of_surjective (Ideal.Quotient.mk J)
      Quotient.mk_surjective, map_le_iff_le_comap, Subtype.coe_mk, comap_map_of_surjective _ hf
      (map (Ideal.Quotient.mk I) Y)]
    suffices map (Ideal.Quotient.mk I) X ≤ map (Ideal.Quotient.mk I) Y by
      exact le_sup_of_le_left this
    rwa [map_le_iff_le_comap, comap_map_of_surjective (Ideal.Quotient.mk I)
      Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker, sup_eq_left.mpr <| le_of_dvd hY]
#align ideal_factors_fun_of_quot_hom idealFactorsFunOfQuotHom
#align ideal_factors_fun_of_quot_hom_coe_coe idealFactorsFunOfQuotHom_coe_coe

@[simp]
theorem idealFactorsFunOfQuotHom_id :
    idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)).surjective = OrderHom.id :=
  OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_mk, OrderHom.id_coe, id,
        comap_map_of_surjective (Ideal.Quotient.mk J) Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk J), mk_ker,
        sup_eq_left.mpr (dvd_iff_le.mp X.prop), Subtype.coe_eta])
#align ideal_factors_fun_of_quot_hom_id idealFactorsFunOfQuotHom_id

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {L : Ideal B}

theorem idealFactorsFunOfQuotHom_comp {f : R ⧸ I →+* A ⧸ J} {g : A ⧸ J →+* B ⧸ L}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (idealFactorsFunOfQuotHom hg).comp (idealFactorsFunOfQuotHom hf) =
      idealFactorsFunOfQuotHom (show Function.Surjective (g.comp f) from hg.comp hf) := by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  rw [idealFactorsFunOfQuotHom, idealFactorsFunOfQuotHom, OrderHom.comp_coe, OrderHom.coe_mk,
    OrderHom.coe_mk, Function.comp_apply, idealFactorsFunOfQuotHom, OrderHom.coe_mk,
    Subtype.mk_eq_mk, Subtype.coe_mk, map_comap_of_surjective (Ideal.Quotient.mk J)
    Quotient.mk_surjective, map_map]
#align ideal_factors_fun_of_quot_hom_comp idealFactorsFunOfQuotHom_comp

variable [IsDedekindDomain R] (f : R ⧸ I ≃+* A ⧸ J)

/-- The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing `J` induced by
  an isomorphism `f : R/I ≅ A/J`. -/
-- @[simps] -- Porting note: simpNF complains about the lemmas generated by simps
def idealFactorsEquivOfQuotEquiv : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J } := by
  have f_surj : Function.Surjective (f : R ⧸ I →+* A ⧸ J) := f.surjective
  have fsym_surj : Function.Surjective (f.symm : A ⧸ J →+* R ⧸ I) := f.symm.surjective
  refine OrderIso.ofHomInv (idealFactorsFunOfQuotHom f_surj) (idealFactorsFunOfQuotHom fsym_surj)
    ?_ ?_
  · have := idealFactorsFunOfQuotHom_comp fsym_surj f_surj
    simp only [RingEquiv.comp_symm, idealFactorsFunOfQuotHom_id] at this
    rw [← this, OrderHom.coe_eq, OrderHom.coe_eq]
  · have := idealFactorsFunOfQuotHom_comp f_surj fsym_surj
    simp only [RingEquiv.symm_comp, idealFactorsFunOfQuotHom_id] at this
    rw [← this, OrderHom.coe_eq, OrderHom.coe_eq]
#align ideal_factors_equiv_of_quot_equiv idealFactorsEquivOfQuotEquiv

theorem idealFactorsEquivOfQuotEquiv_symm :
    (idealFactorsEquivOfQuotEquiv f).symm = idealFactorsEquivOfQuotEquiv f.symm := rfl
#align ideal_factors_equiv_of_quot_equiv_symm idealFactorsEquivOfQuotEquiv_symm

theorem idealFactorsEquivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) :
    (idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ↔
      L ∣ M := by
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
    ↑(idealFactorsEquivOfQuotEquiv f ⟨L, dvd_of_mem_normalizedFactors hL⟩)
      ∈ normalizedFactors J := by
  have hI : I ≠ ⊥ := by
    intro hI
    rw [hI, bot_eq_zero, normalizedFactors_zero, ← Multiset.empty_eq_zero] at hL
    exact Finset.not_mem_empty _ hL
  refine mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  rintro ⟨l, hl⟩ ⟨l', hl'⟩
  rw [Subtype.coe_mk, Subtype.coe_mk]
  apply idealFactorsEquivOfQuotEquiv_is_dvd_iso f
#align ideal_factors_equiv_of_quot_equiv_mem_normalized_factors_of_mem_normalized_factors idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors

/-- The bijection between the sets of normalized factors of I and J induced by a ring
    isomorphism `f : R/I ≅ A/J`. -/
-- @[simps apply] -- Porting note: simpNF complains about the lemmas generated by simps
def normalizedFactorsEquivOfQuotEquiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    { L : Ideal R | L ∈ normalizedFactors I } ≃ { M : Ideal A | M ∈ normalizedFactors J } where
  toFun j :=
    ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩, by
      rw [idealFactorsEquivOfQuotEquiv_symm]
      exact
        idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f.symm hI
          j.prop⟩
  left_inv := fun ⟨j, hj⟩ => by simp
  right_inv := fun ⟨j, hj⟩ => by
    simp
    -- This used to be the end of the proof before leanprover/lean4#2644
    erw [OrderIso.apply_symm_apply]
#align normalized_factors_equiv_of_quot_equiv normalizedFactorsEquivOfQuotEquiv

@[simp]
theorem normalizedFactorsEquivOfQuotEquiv_symm (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (normalizedFactorsEquivOfQuotEquiv f hI hJ).symm =
      normalizedFactorsEquivOfQuotEquiv f.symm hJ hI := rfl
#align normalized_factors_equiv_of_quot_equiv_symm normalizedFactorsEquivOfQuotEquiv_symm

variable [DecidableRel ((· ∣ ·) : Ideal R → Ideal R → Prop)]
variable [DecidableRel ((· ∣ ·) : Ideal A → Ideal A → Prop)]

/-- The map `normalizedFactorsEquivOfQuotEquiv` preserves multiplicities. -/
theorem normalizedFactorsEquivOfQuotEquiv_multiplicity_eq_multiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (L : Ideal R) (hL : L ∈ normalizedFactors I) :
    multiplicity (↑(normalizedFactorsEquivOfQuotEquiv f hI hJ ⟨L, hL⟩)) J = multiplicity L I := by
  rw [normalizedFactorsEquivOfQuotEquiv, Equiv.coe_fn_mk, Subtype.coe_mk]
  refine multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  exact fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_iso f hl hl'
#align normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity normalizedFactorsEquivOfQuotEquiv_multiplicity_eq_multiplicity

end

section ChineseRemainder

open Ideal UniqueFactorizationMonoid

variable {R}

theorem Ring.DimensionLeOne.prime_le_prime_iff_eq [Ring.DimensionLEOne R] {P Q : Ideal R}
    [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : P ≠ ⊥) : P ≤ Q ↔ P = Q :=
  ⟨(hP.isMaximal hP0).eq_of_le hQ.ne_top, Eq.le⟩
#align ring.dimension_le_one.prime_le_prime_iff_eq Ring.DimensionLeOne.prime_le_prime_iff_eq

theorem Ideal.coprime_of_no_prime_ge {I J : Ideal R} (h : ∀ P, I ≤ P → J ≤ P → ¬IsPrime P) :
    IsCoprime I J := by
  rw [isCoprime_iff_sup_eq]
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.isPrime
#align ideal.coprime_of_no_prime_ge Ideal.coprime_of_no_prime_ge

section DedekindDomain

variable [IsDedekindDomain R]

theorem Ideal.IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ∨ b ∈ I ^ n := by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  simp only [← Submodule.span_singleton_le_iff_mem, Ideal.submodule_span_eq, ← Ideal.dvd_iff_le, ←
    Ideal.span_singleton_mul_span_singleton] at h ⊢
  by_cases ha : I ∣ span {a}
  · exact Or.inl ha
  rw [mul_comm] at h
  exact Or.inr (Prime.pow_dvd_of_dvd_mul_right ((Ideal.prime_iff_isPrime hI0).mpr hI) _ ha h)
#align ideal.is_prime.mul_mem_pow Ideal.IsPrime.mul_mem_pow

theorem Ideal.IsPrime.mem_pow_mul (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ^ n ∨ b ∈ I := by
  rw [mul_comm] at h
  rw [or_comm]
  exact Ideal.IsPrime.mul_mem_pow _ h

section

theorem Ideal.count_normalizedFactors_eq {p x : Ideal R} [hp : p.IsPrime] {n : ℕ} (hle : x ≤ p ^ n)
    [DecidableEq (Ideal R)] (hlt : ¬x ≤ p ^ (n + 1)) : (normalizedFactors x).count p = n :=
  count_normalizedFactors_eq' ((Ideal.isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (normalize_eq _) (Ideal.dvd_iff_le.mpr hle) (mt Ideal.le_of_dvd hlt)
  #align ideal.count_normalized_factors_eq Ideal.count_normalizedFactors_eq

end

theorem Ideal.le_mul_of_no_prime_factors {I J K : Ideal R}
    (coprime : ∀ P, J ≤ P → K ≤ P → ¬IsPrime P) (hJ : I ≤ J) (hK : I ≤ K) : I ≤ J * K := by
  simp only [← Ideal.dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  refine mul_dvd_mul_left K
    (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (b := K) hJ0 ?_ hJ)
  exact fun hPJ hPK => mt Ideal.isPrime_of_prime (coprime _ hPJ hPK)
#align ideal.le_mul_of_no_prime_factors Ideal.le_mul_of_no_prime_factors

theorem Ideal.le_of_pow_le_prime {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (h : I ^ n ≤ P) :
    I ≤ P := by
  by_cases hP0 : P = ⊥
  · simp only [hP0, le_bot_iff] at h ⊢
    exact pow_eq_zero h
  rw [← Ideal.dvd_iff_le] at h ⊢
  exact ((Ideal.prime_iff_isPrime hP0).mpr hP).dvd_of_dvd_pow h
#align ideal.le_of_pow_le_prime Ideal.le_of_pow_le_prime

theorem Ideal.pow_le_prime_iff {I P : Ideal R} [_hP : P.IsPrime] {n : ℕ} (hn : n ≠ 0) :
    I ^ n ≤ P ↔ I ≤ P :=
  ⟨Ideal.le_of_pow_le_prime, fun h => _root_.trans (Ideal.pow_le_self hn) h⟩
#align ideal.pow_le_prime_iff Ideal.pow_le_prime_iff

theorem Ideal.prod_le_prime {ι : Type*} {s : Finset ι} {f : ι → Ideal R} {P : Ideal R}
    [hP : P.IsPrime] : ∏ i ∈ s, f i ≤ P ↔ ∃ i ∈ s, f i ≤ P := by
  by_cases hP0 : P = ⊥
  · simp only [hP0, le_bot_iff]
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
  simp only [← Ideal.dvd_iff_le]
  exact ((Ideal.prime_iff_isPrime hP0).mpr hP).dvd_finset_prod_iff _
#align ideal.prod_le_prime Ideal.prod_le_prime

/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers. -/
theorem IsDedekindDomain.inf_prime_pow_eq_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (f i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → f i ≠ f j) :
    (s.inf fun i => f i ^ e i) = ∏ i ∈ s, f i ^ e i := by
  letI := Classical.decEq ι
  revert prime coprime
  refine s.induction ?_ ?_
  · simp
  intro a s ha ih prime coprime
  specialize
    ih (fun i hi => prime i (Finset.mem_insert_of_mem hi)) fun i hi j hj =>
      coprime i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
  rw [Finset.inf_insert, Finset.prod_insert ha, ih]
  refine le_antisymm (Ideal.le_mul_of_no_prime_factors ?_ inf_le_left inf_le_right) Ideal.mul_le_inf
  intro P hPa hPs hPp
  obtain ⟨b, hb, hPb⟩ := Ideal.prod_le_prime.mp hPs
  haveI := Ideal.isPrime_of_prime (prime a (Finset.mem_insert_self a s))
  haveI := Ideal.isPrime_of_prime (prime b (Finset.mem_insert_of_mem hb))
  refine coprime a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) ?_ ?_
  · exact (ne_of_mem_of_not_mem hb ha).symm
  · refine ((Ring.DimensionLeOne.prime_le_prime_iff_eq ?_).mp
      (Ideal.le_of_pow_le_prime hPa)).trans
      ((Ring.DimensionLeOne.prime_le_prime_iff_eq ?_).mp
      (Ideal.le_of_pow_le_prime hPb)).symm
    · exact (prime a (Finset.mem_insert_self a s)).ne_zero
    · exact (prime b (Finset.mem_insert_of_mem hb)).ne_zero
#align is_dedekind_domain.inf_prime_pow_eq_prod IsDedekindDomain.inf_prime_pow_eq_prod

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def IsDedekindDomain.quotientEquivPiOfProdEq {ι : Type*} [Fintype ι] (I : Ideal R)
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i, Prime (P i))
    (coprime : Pairwise fun i j => P i ≠ P j)
    (prod_eq : ∏ i, P i ^ e i = I) : R ⧸ I ≃+* ∀ i, R ⧸ P i ^ e i :=
  (Ideal.quotEquivOfEq
    (by
      simp only [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ, ciInf_pos,
        ← IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun i _ => prime i)
        (coprime.set_pairwise _)])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij => Ideal.coprime_of_no_prime_ge (by
      intro P hPi hPj hPp
      haveI := Ideal.isPrime_of_prime (prime i)
      haveI := Ideal.isPrime_of_prime (prime j)
      refine coprime hij ?_
      refine ((Ring.DimensionLeOne.prime_le_prime_iff_eq ?_).mp
        (Ideal.le_of_pow_le_prime hPi)).trans
        ((Ring.DimensionLeOne.prime_le_prime_iff_eq ?_).mp
          (Ideal.le_of_pow_le_prime hPj)).symm
      · exact (prime i).ne_zero
      · exact (prime j).ne_zero)
#align is_dedekind_domain.quotient_equiv_pi_of_prod_eq IsDedekindDomain.quotientEquivPiOfProdEq

open scoped Classical

/-- **Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multiplicities. -/
noncomputable def IsDedekindDomain.quotientEquivPiFactors {I : Ideal R} (hI : I ≠ ⊥) :
    R ⧸ I ≃+* ∀ P : (factors I).toFinset, R ⧸ (P : Ideal R) ^ (Multiset.count ↑P (factors I)) :=
  IsDedekindDomain.quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.prop))
    (fun i j hij => Subtype.coe_injective.ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P :=
        (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
      _ = ((factors I).map fun P => P).prod := (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := (@associated_iff_eq (Ideal R) _ Ideal.uniqueUnits _ _).mp (factors_prod hI)
      )
#align is_dedekind_domain.quotient_equiv_pi_factors IsDedekindDomain.quotientEquivPiFactors

@[simp]
theorem IsDedekindDomain.quotientEquivPiFactors_mk {I : Ideal R} (hI : I ≠ ⊥) (x : R) :
    IsDedekindDomain.quotientEquivPiFactors hI (Ideal.Quotient.mk I x) = fun _P =>
      Ideal.Quotient.mk _ x := rfl
#align is_dedekind_domain.quotient_equiv_pi_factors_mk IsDedekindDomain.quotientEquivPiFactors_mk

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i ∈ s, P i ^ e i`, then `R ⧸ I` factors as `Π (i : s), R ⧸ (P i ^ e i)`.

This is a version of `IsDedekindDomain.quotientEquivPiOfProdEq` where we restrict
the product to a finite subset `s` of a potentially infinite indexing type `ι`.
-/
noncomputable def IsDedekindDomain.quotientEquivPiOfFinsetProdEq {ι : Type*} {s : Finset ι}
    (I : Ideal R) (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j)
    (prod_eq : ∏ i ∈ s, P i ^ e i = I) : R ⧸ I ≃+* ∀ i : s, R ⧸ P i ^ e i :=
  IsDedekindDomain.quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.ne h))
    (_root_.trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)
#align is_dedekind_domain.quotient_equiv_pi_of_finset_prod_eq IsDedekindDomain.quotientEquivPiOfFinsetProdEq

/-- Corollary of the Chinese remainder theorem: given elements `x i : R / P i ^ e i`,
we can choose a representative `y : R` such that `y ≡ x i (mod P i ^ e i)`. -/
theorem IsDedekindDomain.exists_representative_mod_finset {ι : Type*} {s : Finset ι}
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) (x : ∀ i : s, R ⧸ P i ^ e i) :
    ∃ y, ∀ (i) (hi : i ∈ s), Ideal.Quotient.mk (P i ^ e i) y = x ⟨i, hi⟩ := by
  let f := IsDedekindDomain.quotientEquivPiOfFinsetProdEq _ P e prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i _hi => rfl⟩
#align is_dedekind_domain.exists_representative_mod_finset IsDedekindDomain.exists_representative_mod_finset

/-- Corollary of the Chinese remainder theorem: given elements `x i : R`,
we can choose a representative `y : R` such that `y - x i ∈ P i ^ e i`. -/
theorem IsDedekindDomain.exists_forall_sub_mem_ideal {ι : Type*} {s : Finset ι} (P : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) (x : s → R) :
    ∃ y, ∀ (i) (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ P i ^ e i := by
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.exists_representative_mod_finset P e prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => Ideal.Quotient.eq.mp (hy i hi)⟩
#align is_dedekind_domain.exists_forall_sub_mem_ideal IsDedekindDomain.exists_forall_sub_mem_ideal

end DedekindDomain

end ChineseRemainder

section PID

open multiplicity UniqueFactorizationMonoid Ideal

variable {R}
variable [IsDomain R] [IsPrincipalIdealRing R]

theorem span_singleton_dvd_span_singleton_iff_dvd {a b : R} :
    Ideal.span {a} ∣ Ideal.span ({b} : Set R) ↔ a ∣ b :=
  ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun _d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩
#align span_singleton_dvd_span_singleton_iff_dvd span_singleton_dvd_span_singleton_iff_dvd

@[simp]
theorem Ideal.squarefree_span_singleton {a : R} :
    Squarefree (span {a}) ↔ Squarefree a := by
  refine ⟨fun h x hx ↦ ?_, fun h I hI ↦ ?_⟩
  · rw [← span_singleton_dvd_span_singleton_iff_dvd, ← span_singleton_mul_span_singleton] at hx
    simpa using h _ hx
  · rw [← span_singleton_generator I, span_singleton_mul_span_singleton,
      span_singleton_dvd_span_singleton_iff_dvd] at hI
    exact isUnit_iff.mpr <| eq_top_of_isUnit_mem _ (Submodule.IsPrincipal.generator_mem I) (h _ hI)

theorem singleton_span_mem_normalizedFactors_of_mem_normalizedFactors [NormalizationMonoid R]
    {a b : R} (ha : a ∈ normalizedFactors b) :
    Ideal.span ({a} : Set R) ∈ normalizedFactors (Ideal.span ({b} : Set R)) := by
  by_cases hb : b = 0
  · rw [Ideal.span_singleton_eq_bot.mpr hb, bot_eq_zero, normalizedFactors_zero]
    rw [hb, normalizedFactors_zero] at ha
    exact absurd ha (Multiset.not_mem_zero a)
  · suffices Prime (Ideal.span ({a} : Set R)) by
      obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd ?_ this.irreducible
          (dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr (dvd_of_mem_normalizedFactors ha)))
      rwa [associated_iff_eq.mp hc']
    · by_contra h
      exact hb (span_singleton_eq_bot.mp h)
    rw [prime_iff_isPrime]
    · exact (span_singleton_prime (prime_of_normalized_factor a ha).ne_zero).mpr
        (prime_of_normalized_factor a ha)
    · by_contra h
      exact (prime_of_normalized_factor a ha).ne_zero (span_singleton_eq_bot.mp h)
#align singleton_span_mem_normalized_factors_of_mem_normalized_factors singleton_span_mem_normalizedFactors_of_mem_normalizedFactors

theorem multiplicity_eq_multiplicity_span [DecidableRel ((· ∣ ·) : R → R → Prop)]
    [DecidableRel ((· ∣ ·) : Ideal R → Ideal R → Prop)] {a b : R} :
    multiplicity (Ideal.span {a}) (Ideal.span ({b} : Set R)) = multiplicity a b := by
  by_cases h : Finite a b
  · rw [← PartENat.natCast_get (finite_iff_dom.mp h)]
    refine (multiplicity.unique
      (show Ideal.span {a} ^ (multiplicity a b).get h ∣ Ideal.span {b} from ?_) ?_).symm <;>
      rw [Ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
    · exact pow_multiplicity_dvd h
    · exact multiplicity.is_greatest
        ((PartENat.lt_coe_iff _ _).mpr (Exists.intro (finite_iff_dom.mp h) (Nat.lt_succ_self _)))
  · suffices ¬Finite (Ideal.span ({a} : Set R)) (Ideal.span ({b} : Set R)) by
      rw [finite_iff_dom, PartENat.not_dom_iff_eq_top] at h this
      rw [h, this]
    exact not_finite_iff_forall.mpr fun n => by
      rw [Ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
      exact not_finite_iff_forall.mp h n
#align multiplicity_eq_multiplicity_span multiplicity_eq_multiplicity_span

variable [DecidableEq R] [DecidableEq (Ideal R)] [NormalizationMonoid R]

/-- The bijection between the (normalized) prime factors of `r` and the (normalized) prime factors
    of `span {r}` -/
-- @[simps] -- Porting note: simpNF complains about the lemmas generated by simps
noncomputable def normalizedFactorsEquivSpanNormalizedFactors {r : R} (hr : r ≠ 0) :
    { d : R | d ∈ normalizedFactors r } ≃
      { I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R)) } := by
  refine Equiv.ofBijective ?_ ?_
  · exact fun d =>
      ⟨Ideal.span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.prop⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      rw [Subtype.mk_eq_mk, Ideal.span_singleton_eq_span_singleton, Subtype.coe_mk,
          Subtype.coe_mk] at h
      exact Subtype.mk_eq_mk.mpr (mem_normalizedFactors_eq_of_associated ha hb h)
    · rintro ⟨i, hi⟩
      have : i.IsPrime := isPrime_of_prime (prime_of_normalized_factor i hi)
      have := exists_mem_normalizedFactors_of_dvd hr
        (Submodule.IsPrincipal.prime_generator_of_isPrime i
        (prime_of_normalized_factor i hi).ne_zero).irreducible ?_
      · obtain ⟨a, ha, ha'⟩ := this
        use ⟨a, ha⟩
        simp only [Subtype.coe_mk, Subtype.mk_eq_mk, ← span_singleton_eq_span_singleton.mpr ha',
            Ideal.span_singleton_generator]
      · exact (Submodule.IsPrincipal.mem_iff_generator_dvd i).mp
          ((show Ideal.span {r} ≤ i from dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi))
            (mem_span_singleton.mpr (dvd_refl r)))
#align normalized_factors_equiv_span_normalized_factors normalizedFactorsEquivSpanNormalizedFactors

variable [DecidableRel ((· ∣ ·) : R → R → Prop)] [DecidableRel ((· ∣ ·) : Ideal R → Ideal R → Prop)]

/-- The bijection `normalizedFactorsEquivSpanNormalizedFactors` between the set of prime
    factors of `r` and the set of prime factors of the ideal `⟨r⟩` preserves multiplicities. See
    `count_normalizedFactorsSpan_eq_count` for the version stated in terms of multisets `count`.-/
theorem multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity {r d : R}
    (hr : r ≠ 0) (hd : d ∈ normalizedFactors r) :
    multiplicity d r =
      multiplicity (normalizedFactorsEquivSpanNormalizedFactors hr ⟨d, hd⟩ : Ideal R)
        (Ideal.span {r}) := by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, multiplicity_eq_multiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]
#align multiplicity_normalized_factors_equiv_span_normalized_factors_eq_multiplicity multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity

/-- The bijection `normalized_factors_equiv_span_normalized_factors.symm` between the set of prime
    factors of the ideal `⟨r⟩` and the set of prime factors of `r` preserves multiplicities. -/
theorem multiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_multiplicity {r : R}
    (hr : r ≠ 0) (I : { I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R)) }) :
    multiplicity ((normalizedFactorsEquivSpanNormalizedFactors hr).symm I : R) r =
      multiplicity (I : Ideal R) (Ideal.span {r}) := by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm, Equiv.symm_apply_apply, Subtype.coe_mk,
    multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity hr ha]
#align multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity multiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_multiplicity

/-- The bijection between the set of prime factors of the ideal `⟨r⟩` and the set of prime factors
  of `r` preserves `count` of the corresponding multisets. See
  `multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity` for the version
  stated in terms of multiplicity. -/
theorem count_span_normalizedFactors_eq {r X : R} (hr : r ≠ 0) (hX : Prime X) :
    Multiset.count (Ideal.span {X} : Ideal R) (normalizedFactors (Ideal.span {r}))  =
        Multiset.count (normalize X) (normalizedFactors r) := by
  have := multiplicity_eq_multiplicity_span (R := R) (a := X) (b := r)
  rw [multiplicity_eq_count_normalizedFactors (Prime.irreducible hX) hr,
    multiplicity_eq_count_normalizedFactors (Prime.irreducible ?_), normalize_apply,
    normUnit_eq_one, Units.val_one, one_eq_top, mul_top, Nat.cast_inj] at this
  simp only [normalize_apply, this]
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, hr, not_false_eq_true]
  · simpa only [prime_span_singleton_iff]

theorem count_span_normalizedFactors_eq_of_normUnit {r X : R}
    (hr : r ≠ 0) (hX₁ : normUnit X = 1) (hX : Prime X) :
      Multiset.count (Ideal.span {X} : Ideal R) (normalizedFactors (Ideal.span {r})) =
        Multiset.count X (normalizedFactors r) := by
  simpa [hX₁] using count_span_normalizedFactors_eq hr hX

/-- The number of times an ideal `I` occurs as normalized factor of another ideal `J` is stable
  when regarding at these ideals as associated elements of the monoid of ideals.-/
theorem count_associates_factors_eq [DecidableEq <| Associates (Ideal R)]
    [∀ (p : Associates <| Ideal R), Decidable (Irreducible p)]
    (I J : Ideal R) (hI : I ≠ 0) (hJ : J.IsPrime) (hJ₀ : J ≠ ⊥) :
    (Associates.mk J).count (Associates.mk I).factors = Multiset.count J (normalizedFactors I) := by
  replace hI : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI
  have hJ' : Irreducible (Associates.mk J) := by
    simpa only [Associates.irreducible_mk] using (Ideal.prime_of_isPrime hJ₀ hJ).irreducible
  apply (Ideal.count_normalizedFactors_eq (p := J) (x := I) _ _).symm
  all_goals
    rw [← Ideal.dvd_iff_le, ← Associates.mk_dvd_mk, Associates.mk_pow]
    simp only [Associates.dvd_eq_le]
    rw [Associates.prime_pow_dvd_iff_le hI hJ']
  linarith

end PID
