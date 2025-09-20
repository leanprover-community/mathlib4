/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca, Xavier Roblot
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# Localization at prime in an extension

Let `R ⊆ S` be an extension of rings and `p` be a prime ideal of `R`. Denote by `Rₚ` the
localization of `R` at the complement of `p` and by `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the extension of `Rₚ ⊆ Sₚ` and the relation between the (nonzero) prime
ideals of `Sₚ` and the prime ideals of `S` above `p`. In particular, we prove that (under suitable
conditions) they are in bijection and that the residual degree and ramification index are
preserved by this bijection.

# Main definitions and results

- `IsLocalization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `IsLocalization.AtPrime.quotMapEquivQuotMapOfIsMaximal`: `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ` where
  `P` is a maximal ideal of `S` above `p`.

- `IsLocalization.AtPrime.quotMapEquivQuotMapMaximalIdeal`: `S ⧸ pS ≃+* Sₚ ⧸ p·Sₚ`.

- `IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply_eq`: the map
  `equivQuotMaximalIdeal` and `quotMapEquivQuotMapOfIsMaximal` satisfy the obvious
  commutative diagram.

- `IsLocalization.AtPrime.primesOverEquivPrimesOver`: the bijection between the primes over
  `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

- `IsLocalization.AtPrime.primesOverEquivPrimesOver_inertiagDeg_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the inertia degree.

- `IsLocalization.AtPrime.primesOverEquivPrimesOver_ramificationIdx_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the ramification index.

-/

namespace IsLocalization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S) [hPp : P.LiesOver p]
variable (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
open Ideal Algebra IsLocalRing

section misc

theorem isPrime_algebraMap_of_liesOver [p.IsPrime] [P.IsPrime]
  [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] : (P.map (algebraMap S Sₚ)).IsPrime :=
  isPrime_of_isPrime_disjoint (algebraMapSubmonoid S p.primeCompl) _ _ inferInstance
    (disjoint_primeCompl_of_liesOver P p)

variable (S) in
theorem algebraMapSubmonoid_primeCompl_le_nonZeroDivisors [IsDomain R] [IsDomain S]
    [FaithfulSMul R S] [p.IsPrime] :
    algebraMapSubmonoid S p.primeCompl ≤ nonZeroDivisors S := by
  apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
  exact fun _ h ↦  mem_nonZeroDivisors_of_ne_zero <| ne_of_mem_of_not_mem h <| by simp

theorem noZeroSMulDivisors_localization [IsDomain R] [IsDomain S] [FaithfulSMul R S] [p.IsPrime]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    NoZeroSMulDivisors S Sₚ := by
  have : IsDomain Sₚ :=
    isDomain_of_le_nonZeroDivisors _ (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors S p)
  rw [NoZeroSMulDivisors.iff_algebraMap_injective,
    injective_iff_isRegular (algebraMapSubmonoid S p.primeCompl)]
  exact fun ⟨x, hx⟩ ↦ isRegular_iff_ne_zero'.mpr <|
    ne_of_mem_of_not_mem hx <| by simp [Algebra.algebraMapSubmonoid]

variable (S) [Algebra R Sₚ] [IsScalarTower R Rₚ Sₚ] [IsScalarTower R S Sₚ]

theorem noZeroSMulDivisors_localization_localization [IsDomain R] [IsDomain S] [FaithfulSMul R S]
    [p.IsPrime] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    NoZeroSMulDivisors Rₚ Sₚ :=
  NoZeroSMulDivisors_of_isLocalization R S Rₚ Sₚ (primeCompl_le_nonZeroDivisors p)

theorem algebra_isIntegral [p.IsPrime] [Algebra.IsIntegral R S] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    Algebra.IsIntegral Rₚ Sₚ :=
  Algebra.isIntegral_def.mpr <|
    (algebraMap_eq_map_map_submonoid p.primeCompl S Rₚ Sₚ ▸
      isIntegral_localization : (algebraMap Rₚ Sₚ).IsIntegral)

variable {S} [IsLocalRing Rₚ]

lemma map_eq_maximalIdeal [p.IsPrime] [IsLocalization.AtPrime Rₚ p] :
    p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert congr_arg (Ideal.map (algebraMap R Rₚ)) (comap_maximalIdeal Rₚ p).symm
  rw [map_comap p.primeCompl]

lemma map_isMaximal [p.IsPrime] [IsLocalization.AtPrime Rₚ p] :
    (p.map (algebraMap R Rₚ)).IsMaximal := by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ

theorem liesOver_map_of_liesOver [p.IsPrime] [IsLocalization.AtPrime Rₚ p] [P.IsPrime]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← map_eq_maximalIdeal p Rₚ]
  exact under_map _ _ ((liesOver_iff _ _).mp hPp) (map_isMaximal p Rₚ)
    (isPrime_algebraMap_of_liesOver p P Sₚ).ne_top

/--
The nonzero prime ideals of `Sₚ` are primes over the maximal ideal of `Rₚ`.
See `IsLocalization.AtPrime.primesOverEquivPrimesOver` for the bijection between the prime ideals
of `Sₚ` over the maximal ideal of `Rₚ` and the primes ideals of `S` above `p`.
-/
theorem mem_primesOver_of_isPrime [p.IsPrime] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
    {Q : Ideal Sₚ} [Q.IsPrime] [Algebra.IsIntegral R S]
    [IsDedekindRing Sₚ] (hQ : Q ≠ ⊥) : Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := by
  have := algebra_isIntegral S p Rₚ Sₚ
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← eq_maximalIdeal]
  have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ inferInstance
  exact IsMaximal.under Rₚ Q

end misc

section isomorphisms

variable [IsLocalRing Rₚ]

attribute [local instance] Ideal.Quotient.field

theorem exists_algebraMap_quot_eq_of_mem_quot [p.IsPrime] [P.IsMaximal]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] (x : Sₚ ⧸ P.map (algebraMap S Sₚ)) :
    ∃ a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S Sₚ))) a = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.algebraMap_eq, RingHom.comp_apply]
  use x * s'
  rw [← sub_eq_zero, ← map_sub, Quotient.eq_zero_iff_mem]
  have h₀ : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_algebraMap_of_liesOver p P Sₚ
  have h₁ : s.1 ∉ P := (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
    rwa [← mem_comap, comap_map_eq_self_of_isMaximal _ h₀.ne_top]
  refine (h₀.mem_or_mem ?_).resolve_left h₂
  rw [mul_sub, mul_mk'_eq_mk'_of_mul, mk'_mul_cancel_left, ← map_mul, ← map_sub, ← mem_comap,
    comap_map_eq_self_of_isMaximal _ IsPrime.ne_top', ← Ideal.Quotient.eq, map_mul, map_mul, hs,
    mul_comm, inv_mul_cancel_right₀ (Quotient.eq_zero_iff_mem.not.mpr h₁)]

/--
The isomorphism `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ`, where `Sₚ` is the localization of `S` at the (image) of
the complement of `p` and `P` is a maximal ideal of `S` above `p`.
Note that this isomorphism makes the obvious diagram involving `R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ`
commute, see `IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply_eq`.
-/
noncomputable def quotMapEquivQuotMapOfIsMaximal [p.IsPrime] [P.IsMaximal]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    S ⧸ P ≃+* Sₚ ⧸ P.map (algebraMap S Sₚ) :=
  (Ideal.quotEquivOfEq (by
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), ← RingHom.comap_ker, Quotient.algebraMap_eq,
      mk_ker,
        comap_map_eq_self_of_isMaximal _ (isPrime_algebraMap_of_liesOver p P Sₚ).ne_top])).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _))
      fun x ↦ exists_algebraMap_quot_eq_of_mem_quot p P Sₚ x)

@[simp]
theorem quotMapEquivQuotMapOfIsMaximal_apply_mk [p.IsPrime] [P.IsMaximal]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] (x : S) :
    quotMapEquivQuotMapOfIsMaximal p P Sₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[simp]
theorem quotMapEquivQuotMapOfIsMaximal_symm_apply_mk [p.IsPrime] [P.IsMaximal]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] (x : S)
    (s : algebraMapSubmonoid S p.primeCompl) :
    (quotMapEquivQuotMapOfIsMaximal p P Sₚ).symm
      (Ideal.Quotient.mk _ (mk' _ x s)) =
        (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ s.val)⁻¹ := by
  have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := isPrime_algebraMap_of_liesOver p P Sₚ
  have h₁ : Ideal.Quotient.mk P ↑s ≠ 0 :=
    Quotient.eq_zero_iff_mem.not.mpr <|
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : quotMapEquivQuotMapOfIsMaximal p P Sₚ (Ideal.Quotient.mk P ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, quotMapEquivQuotMapOfIsMaximal_apply_mk,
    ← map_mul, mk'_spec, Quotient.mk_algebraMap, quotMapEquivQuotMapOfIsMaximal_apply_mk,
    Quotient.mk_algebraMap]

variable [Algebra R Sₚ] [IsScalarTower R Rₚ Sₚ] [IsScalarTower R S Sₚ]

/--
The following diagram where the vertical maps are the algebra maps and the horizontal maps are
`IsLocalization.AtPrime.equivQuotMaximalIdeal.symm` and
`IsLocalization.AtPrime.quotMapEquivQuotMapOfIsMaximal.symm` commutes:
```
Rₚ ⧸ 𝓂 ──▶ R ⧸ p
  │         │
Sₚ ⧸ 𝒫 ──▶ S ⧸ P
```
Here, `𝓂` denotes the maximal ideal of `Rₚ` and `𝒫` the image of `P` in `Sₚ`.
Note that result is stated in that direction since this is the formulation needed for the proof
of `IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg`.
-/
theorem algebraMap_equivQuotMaximalIdeal_symm_apply_eq [p.IsMaximal] [IsLocalization.AtPrime Rₚ p]
    [P.IsMaximal] [(P.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ)]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
    (x : Rₚ ⧸ maximalIdeal Rₚ) :
    algebraMap (R ⧸ p) (S ⧸ P) ((equivQuotMaximalIdeal p Rₚ).symm x) =
    (quotMapEquivQuotMapOfIsMaximal p P Sₚ).symm
      (algebraMap (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ P.map (algebraMap S Sₚ)) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective p.primeCompl x
  simp [equivQuotMaximalIdeal_symm_apply_mk, map_mul,
    Quotient.algebraMap_mk_of_liesOver, Quotient.mk_algebraMap, map_inv₀,
    IsLocalization.algebraMap_mk' S, quotMapEquivQuotMapOfIsMaximal_symm_apply_mk]

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

lemma comap_map_eq_map [p.IsMaximal] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    (Ideal.map (algebraMap R Sₚ) p).comap (algebraMap S Sₚ) = pS := by
  rw [IsScalarTower.algebraMap_eq R S Sₚ, ← Ideal.map_map, eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : ∃ α ∉ p, α • x ∈ pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).mp hx
    rw [← map_mul,
      IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S p.primeCompl)] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨α, hα, e⟩ := (c * s).prop
    refine ⟨α, hα, ?_⟩
    rw [Algebra.smul_def, e, Submonoid.coe_mul, mul_assoc, mul_comm _ x, hc]
    exact Ideal.mul_mem_left _ _ y.prop
  obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ β * α = 1 + γ := by
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
    refine ⟨β, β * α - 1, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
        map_mul, hβ, inv_mul_cancel₀, sub_self]
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [add_sub_cancel]
  have := Ideal.mul_mem_left _ (algebraMap _ _ β) hαx
  rw [← Algebra.smul_def, smul_smul, hβ, add_smul, one_smul] at this
  refine (Submodule.add_mem_iff_left _ ?_).mp this
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ hγ

@[deprecated (since := "2025-07-31")] alias comap_map_eq_map_of_isLocalization_algebraMapSubmonoid
  := comap_map_eq_map

variable (S) in
/--
The isomorphism `S ⧸ pS ≃+* Sₚ ⧸ p·Sₚ`, where `Sₚ` is the localization of `S` at the (image) of
the complement of `p`
-/
noncomputable def quotMapEquivQuotMapMaximalIdeal [p.IsMaximal] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] :
    S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rₚ, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq, comap_map_eq_map]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid S p.primeCompl) x
    obtain ⟨α, hα : α ∉ p, e⟩ := s.prop
    obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ α * β = 1 + γ := by
      obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
      refine ⟨β, α * β - 1, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
          map_mul, hβ, mul_inv_cancel₀, sub_self]
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [add_sub_cancel]
    use β • x
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ pSₚ), Ideal.Quotient.algebraMap_eq,
      RingHom.comp_apply, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [h, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    refine ⟨⟨⟨γ • x, ?_⟩, s⟩, ?_⟩
    · rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ hγ
    simp only
    rw [mul_comm, mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_mul_cancel_left, ← map_mul, ← e, ← Algebra.smul_def, smul_smul,
      hβ, ← map_sub, add_smul, one_smul, add_comm x, add_sub_cancel_right]

@[simp]
theorem quotMapEquivQuotMapMaximalIdeal_apply_mk [p.IsMaximal] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] (x : S) :
    quotMapEquivQuotMapMaximalIdeal S p Rₚ Sₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[deprecated (since := "2025-07-31")] alias quotMapEquivQuotMapMaximalIdealOfIsLocalization :=
  quotMapEquivQuotMapMaximalIdeal

end isomorphisms

noncomputable section primesOver

variable [IsLocalRing Rₚ] [Algebra R Sₚ] [IsScalarTower R Rₚ Sₚ] [IsScalarTower R S Sₚ]

theorem inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [IsLocalization.AtPrime Rₚ p] [P.IsMaximal]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
    [(Ideal.map (algebraMap S Sₚ) P).LiesOver (maximalIdeal Rₚ)] :
    (maximalIdeal Rₚ).inertiaDeg (P.map (algebraMap S Sₚ)) = p.inertiaDeg P := by
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).symm
    (quotMapEquivQuotMapOfIsMaximal p P Sₚ).symm ?_
  ext x
  exact algebraMap_equivQuotMaximalIdeal_symm_apply_eq p P Rₚ Sₚ x

theorem ramificationIdx_map_eq_ramificationIdx [Module.Finite R S] [NoZeroSMulDivisors R S]
    [IsDedekindDomain R] [IsDedekindDomain S] [p.IsPrime] [NeZero p] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] [IsDedekindDomain Rₚ]
    [IsDedekindDomain Sₚ] [P.IsPrime] :
    (maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ) (P.map (algebraMap S Sₚ)) =
      p.ramificationIdx (algebraMap R S) P := by
  have : FaithfulSMul R Rₚ := faithfulSMul Rₚ _ p
  have h₁ : maximalIdeal Rₚ ≠ ⊥ := by
    rw [← map_eq_maximalIdeal p Rₚ]
    exact map_ne_bot_of_ne_bot (NeZero.ne p)
  have : NoZeroSMulDivisors S Sₚ := noZeroSMulDivisors_localization p Sₚ
  have : NoZeroSMulDivisors R Sₚ := NoZeroSMulDivisors.trans_faithfulSMul R S Sₚ
  have : NoZeroSMulDivisors Rₚ Sₚ := noZeroSMulDivisors_localization_localization S p Rₚ Sₚ
  have : IsPrincipalIdealRing Sₚ :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S p (NeZero.ne _)
  have : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_algebraMap_of_liesOver p P Sₚ
  by_cases hP : P = ⊥
  · simp_rw [hP, Ideal.map_bot, ramificationIdx_bot' (NeZero.ne p)
      (FaithfulSMul.algebraMap_injective _ _),
      ramificationIdx_bot' h₁ (FaithfulSMul.algebraMap_injective _ _)]
  have h₂ : Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ) ≤ P.map (algebraMap S Sₚ) := by
    rw [map_le_iff_le_comap]
    exact le_of_eq <| (liesOver_iff _ _).mp <| liesOver_map_of_liesOver p P Rₚ Sₚ
  have main := (ramificationIdx_algebra_tower
      (map_ne_bot_of_ne_bot h₁) (map_ne_bot_of_ne_bot (NeZero.ne p)) h₂).symm.trans
      (ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hP)
      (map_ne_bot_of_ne_bot (NeZero.ne p)) le_rfl)
  rwa [show ramificationIdx (algebraMap R Rₚ) p (maximalIdeal Rₚ) = 1 by
      rw [← map_eq_maximalIdeal p Rₚ, ramificationIdx_map_self_eq_one_of_isPrincipal
        (map_ne_bot_of_ne_bot (NeZero.ne p))]
      rw [map_eq_maximalIdeal p Rₚ]
      exact IsPrime.ne_top',
    ramificationIdx_map_self_eq_one_of_isPrincipal (map_ne_bot_of_ne_bot hP)
    IsPrime.ne_top', one_mul, mul_one] at main

theorem exists_primesOver_map_eq_of_primesOver [p.IsPrime] [IsLocalization.AtPrime Rₚ p]
    [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ] (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ∃ q : p.primesOver S, q.val.map (algebraMap S Sₚ) = Q := by
  refine ⟨⟨comap (algebraMap S Sₚ) Q, ⟨IsPrime.under _ _, ?_⟩⟩, ?_⟩
  · have : Q.1.LiesOver p := by
      have : (maximalIdeal Rₚ).LiesOver p :=
        (liesOver_iff _ _).mpr (comap_maximalIdeal Rₚ p inferInstance).symm
      exact LiesOver.trans Q.1 (IsLocalRing.maximalIdeal Rₚ) p
    exact comap_liesOver Q.1 p <| IsScalarTower.toAlgHom R S Sₚ
  · refine le_antisymm  map_comap_le fun x hx ↦ ?_
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := mk'_surjective (algebraMapSubmonoid S p.primeCompl) x
    refine (mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ⟨s, hs, ?_⟩
    exact Ideal.mul_mem_left _ _ <| mk'_mem_iff.mp hx

variable [IsDedekindDomain S] [NoZeroSMulDivisors R S] [p.IsPrime] [NeZero p]
  [IsLocalization.AtPrime Rₚ p] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]

/--
The bijection between the primes over `p` in `S` and the primes over the maximal ideal of `Rₚ` in
`Sₚ`. This bijection preserves the residual degree and the ramificiation index, see
`IsLocalization.AtPrime.primesOverEquivPrimesOver_inertiagDeg_eq` and
`IsLocalization.AtPrime.primesOverEquivPrimesOver_ramificationIdx_eq`.
-/
def primesOverEquivPrimesOver : p.primesOver S ≃ (maximalIdeal Rₚ).primesOver Sₚ :=
  Equiv.ofBijective (fun Q ↦ ⟨Q.1.map (algebraMap S Sₚ), isPrime_algebraMap_of_liesOver p _ _,
    liesOver_map_of_liesOver p _ Rₚ _⟩)
    ⟨fun P₁ P₂ h ↦ by
      have : P₁.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver (NeZero.ne _) P₁.prop) (primesOver.isPrime p P₁)
      have : P₂.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver (NeZero.ne _) P₂.prop) (primesOver.isPrime p P₂)
      have : (Ideal.map (algebraMap S Sₚ) P₁).IsPrime := isPrime_algebraMap_of_liesOver p _ _
      have : (Ideal.map (algebraMap S Sₚ) P₂).IsPrime := isPrime_algebraMap_of_liesOver p _ _
      simpa [comap_map_eq_self_of_isMaximal _ IsPrime.ne_top', SetCoe.ext_iff]
        using congr_arg (comap (algebraMap S Sₚ) ·) <| Subtype.mk_eq_mk.mp h,
    fun Q ↦ by simpa [Subtype.ext_iff] using exists_primesOver_map_eq_of_primesOver p Rₚ Sₚ Q⟩

@[simp]
theorem primesOverEquivPrimesOver_apply (P : p.primesOver S) :
    primesOverEquivPrimesOver p Rₚ Sₚ P = Ideal.map (algebraMap S Sₚ) P := rfl

theorem primesOverEquivPrimesOver_inertiagDeg_eq [p.IsMaximal] (P : p.primesOver S) :
    (maximalIdeal Rₚ).inertiaDeg (primesOverEquivPrimesOver p Rₚ Sₚ P).val =
      p.inertiaDeg P.val := by
  have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver (NeZero.ne _) P.prop) inferInstance
  have : (P.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := liesOver_map_of_liesOver p _ _ _
  exact inertiaDeg_map_eq_inertiaDeg p P.val Rₚ Sₚ

theorem primesOverEquivPrimesOver_ramificationIdx_eq [IsDedekindDomain R] [IsDedekindDomain Rₚ]
    [IsDedekindDomain Sₚ] [Module.Finite R S] (P : p.primesOver S) :
    (maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ) (primesOverEquivPrimesOver p Rₚ Sₚ P).val =
      p.ramificationIdx (algebraMap R S) P.val :=
  ramificationIdx_map_eq_ramificationIdx p P.val Rₚ Sₚ

end primesOver

end IsLocalization.AtPrime
