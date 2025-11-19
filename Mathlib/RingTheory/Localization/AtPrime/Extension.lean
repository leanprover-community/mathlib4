/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca, Xavier Roblot
-/
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Primes in an extension of localization at prime

Let `R ⊆ S` be an extension of Dedekind domains and `p` be a prime ideal of `R`. Let `Rₚ` be the
localization of `R` at the complement of `p` and `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the relation between the (nonzero) prime ideals of `Sₚ` and the prime
ideals of `S` above `p`. In particular, we prove that (under suitable conditions) they are in
bijection and that the residual degree and ramification index are preserved by this bijection.

## Main definitions and results

- `Localization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `Localization.AtPrime.quotMapEquivQuotMapOfIsMaximal`: `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ` where
  `P` is a maximal ideal of `S` above `p`.

- `Localization.AtPrime.quotMapEquivQuotMapMaximalIdeal`: `S ⧸ pS ≃+* Sₚ ⧸ p·Sₚ`.

- `Localization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply_eq`: the map
  `equivQuotMaximalIdeal` and `quotMapEquivQuotMapOfIsMaximal` satisfy the obvious
  commutative diagram.

- `IsDedekindDomain.primesOverEquivPrimesOver`: the bijection between the primes over
  `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

- `IsDedekindDomain.primesOverEquivPrimesOver_inertiagDeg_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the inertia degree.

- `IsDedekindDomain.primesOverEquivPrimesOver_ramificationIdx_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the ramification index.

-/

open Algebra IsLocalRing Ideal Localization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

namespace IsLocalization.AtPrime

lemma map_isMaximal :
    (p.map (algebraMap R Rₚ)).IsMaximal := by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ

/--
The nonzero prime ideals of `Sₚ` are prime ideals over the maximal ideal of `Rₚ`.
See `Localization.AtPrime.primesOverEquivPrimesOver` for the bijection between the prime ideals
of `Sₚ` over the maximal ideal of `Rₚ` and the primes ideals of `S` above `p`.
-/
theorem mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral Rₚ Sₚ] :
    Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q

theorem liesOver_comap_of_liesOver {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T]
    [Algebra S T] [IsScalarTower R S T] [IsScalarTower R Rₚ T] (Q : Ideal T)
    [Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p := by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
  exact comap_liesOver Q p <| IsScalarTower.toAlgHom R S T

include p in
theorem liesOver_map_of_liesOver [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← map_eq_maximalIdeal p, over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

attribute [local instance] Ideal.Quotient.field

include p in
theorem exists_algebraMap_quot_eq_of_mem_quot [P.IsMaximal]
    (x : Sₚ ⧸ P.map (algebraMap S Sₚ)) :
    ∃ a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S Sₚ))) a = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.algebraMap_eq, RingHom.comp_apply]
  use x * s'
  rw [← sub_eq_zero, ← map_sub, Quotient.eq_zero_iff_mem]
  have h₀ : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_map_of_liesOver S p Sₚ P
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
noncomputable def quotMapEquivQuotMapOfIsMaximal [p.IsPrime] [P.IsMaximal] :
    S ⧸ P ≃+* Sₚ ⧸ P.map (algebraMap S Sₚ) :=
  (Ideal.quotEquivOfEq (by
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), ← RingHom.comap_ker, Quotient.algebraMap_eq,
      mk_ker,
        comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top])).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _))
      fun x ↦ exists_algebraMap_quot_eq_of_mem_quot p Sₚ P x)

@[simp]
theorem quotMapEquivQuotMapOfIsMaximal_apply_mk [P.IsMaximal] (x : S) :
    quotMapEquivQuotMapOfIsMaximal p Sₚ P (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[simp]
theorem quotMapEquivQuotMapOfIsMaximal_symm_apply_mk [P.IsMaximal] (x : S)
    (s : algebraMapSubmonoid S p.primeCompl) :
    (quotMapEquivQuotMapOfIsMaximal p Sₚ P).symm (Ideal.Quotient.mk _ (mk' _ x s)) =
        (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ s.val)⁻¹ := by
  have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : Ideal.Quotient.mk P ↑s ≠ 0 :=
    Quotient.eq_zero_iff_mem.not.mpr <|
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : quotMapEquivQuotMapOfIsMaximal p Sₚ P (Ideal.Quotient.mk P ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, quotMapEquivQuotMapOfIsMaximal_apply_mk,
    ← map_mul, mk'_spec, Quotient.mk_algebraMap, quotMapEquivQuotMapOfIsMaximal_apply_mk,
    Quotient.mk_algebraMap]

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

/--
The following diagram where the vertical maps are the algebra maps and the horizontal maps are
`Localization.AtPrime.equivQuotMaximalIdeal.symm` and
`Localization.AtPrime.quotMapEquivQuotMapOfIsMaximal.symm` commutes:
```
Rₚ ⧸ 𝓂 ──▶ R ⧸ p
  │         │
Sₚ ⧸ 𝒫 ──▶ S ⧸ P
```
Here, `𝓂` denotes the maximal ideal of `Rₚ` and `𝒫` the image of `P` in `Sₚ`.
Note that result is stated in that direction since this is the formulation needed for the proof
of `Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg`.
-/
theorem algebraMap_equivQuotMaximalIdeal_symm_apply_eq [p.IsMaximal] [P.IsMaximal]
    [(P.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ)] (x : Rₚ ⧸ maximalIdeal Rₚ) :
    algebraMap (R ⧸ p) (S ⧸ P) ((equivQuotMaximalIdeal p Rₚ).symm x) =
    (quotMapEquivQuotMapOfIsMaximal p Sₚ P).symm
      (algebraMap (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ P.map (algebraMap S Sₚ)) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective p.primeCompl x
  dsimp only
  simp [equivQuotMaximalIdeal_symm_apply_mk, map_mul, Quotient.algebraMap_mk_of_liesOver,
    IsLocalization.algebraMap_mk' S Rₚ Sₚ]

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

lemma comap_map_eq_map [p.IsMaximal] :
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
noncomputable def quotMapEquivQuotMapMaximalIdeal [p.IsMaximal] :
    S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← map_eq_maximalIdeal p, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq, comap_map_eq_map]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
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
theorem quotMapEquivQuotMapMaximalIdeal_apply_mk [p.IsMaximal] (x : S) :
    quotMapEquivQuotMapMaximalIdeal S p Rₚ Sₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[deprecated (since := "2025-07-31")] alias quotMapEquivQuotMapMaximalIdealOfIsLocalization :=
  quotMapEquivQuotMapMaximalIdeal

theorem inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [P.IsMaximal]
    [(Ideal.map (algebraMap S Sₚ) P).LiesOver (maximalIdeal Rₚ)] :
    (maximalIdeal Rₚ).inertiaDeg (P.map (algebraMap S Sₚ)) = p.inertiaDeg P := by
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).symm
    (quotMapEquivQuotMapOfIsMaximal p Sₚ P).symm ?_
  ext x
  exact algebraMap_equivQuotMaximalIdeal_symm_apply_eq p Rₚ Sₚ P x

theorem ramificationIdx_map_eq_ramificationIdx [NoZeroSMulDivisors R S]
    [NoZeroSMulDivisors R Rₚ] [NoZeroSMulDivisors R Sₚ] [NoZeroSMulDivisors S Sₚ]
    [NoZeroSMulDivisors Rₚ Sₚ] [IsDedekindDomain S] [IsDedekindDomain Rₚ]
    [IsDedekindDomain Sₚ] [IsPrincipalIdealRing Sₚ] (hp : p ≠ ⊥) [P.IsPrime] :
    (maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ) (P.map (algebraMap S Sₚ)) =
      p.ramificationIdx (algebraMap R S) P := by
  have h₁ : maximalIdeal Rₚ ≠ ⊥ := by
    rw [← map_eq_maximalIdeal p]
    exact map_ne_bot_of_ne_bot hp
  have : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  by_cases hP : P = ⊥
  · simp_rw [hP, Ideal.map_bot, ramificationIdx_bot' hp
      (FaithfulSMul.algebraMap_injective _ _),
      ramificationIdx_bot' h₁ (FaithfulSMul.algebraMap_injective Rₚ Sₚ)]
  have h₂ : Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ) ≤ P.map (algebraMap S Sₚ) := by
    rw [map_le_iff_le_comap]
    exact le_of_eq <| (liesOver_iff _ _).mp <| liesOver_map_of_liesOver p Rₚ Sₚ P
  have main := (ramificationIdx_algebra_tower
      (map_ne_bot_of_ne_bot h₁) (map_ne_bot_of_ne_bot hp) h₂).symm.trans
      (ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hP)
      (map_ne_bot_of_ne_bot hp) le_rfl)
  rwa [show ramificationIdx (algebraMap R Rₚ) p (maximalIdeal Rₚ) = 1 by
      rw [← map_eq_maximalIdeal p, ramificationIdx_map_self_eq_one_of_isPrincipal
        (map_ne_bot_of_ne_bot hp)]
      rw [map_eq_maximalIdeal]
      exact IsPrime.ne_top',
    ramificationIdx_map_self_eq_one_of_isPrincipal (map_ne_bot_of_ne_bot hP)
    IsPrime.ne_top', one_mul, mul_one] at main

theorem exists_primesOver_map_eq_of_primesOver (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ∃ q : p.primesOver S, q.val.map (algebraMap S Sₚ) = Q := by
  refine ⟨⟨comap (algebraMap S Sₚ) Q, ⟨IsPrime.under _ _, ?_⟩⟩, ?_⟩
  · have : Q.1.LiesOver p := by
      have := liesOver_maximalIdeal Rₚ p inferInstance
      exact LiesOver.trans Q.1 (IsLocalRing.maximalIdeal Rₚ) p
    exact comap_liesOver Q.1 p <| IsScalarTower.toAlgHom R S Sₚ
  · refine le_antisymm  map_comap_le fun x hx ↦ ?_
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
    refine (mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ⟨s, hs, ?_⟩
    exact Ideal.mul_mem_left _ _ <| mk'_mem_iff.mp hx

end IsLocalization.AtPrime

namespace IsDedekindDomain

open IsLocalization AtPrime

variable [IsDedekindDomain S] [NoZeroSMulDivisors R S] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
  [IsScalarTower R Rₚ Sₚ]

/--
For `R ⊆ S` an extension of Dedekind domains and `p` a prime ideal of `R`, the bijection
between the primes of `S` over `p` and the primes over the maximal ideal of `Rₚ` in `Sₚ` where
`Rₚ` and `Sₚ` are resp. the localizations of `R` and `S` at the complement of `p`.
-/
noncomputable def primesOverEquivPrimesOver (hp : p ≠ ⊥) :
    p.primesOver S ≃o (maximalIdeal Rₚ).primesOver Sₚ where
  toFun P := ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver S p Sₚ P.1,
    liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  map_rel_iff' {Q Q'} := by
    refine ⟨fun h ↦ ?_, fun h ↦ map_mono h⟩
    have : Q'.1.IsMaximal :=
      (primesOver.isPrime p Q').isMaximal (ne_bot_of_mem_primesOver hp Q'.prop)
    simpa [comap_map_of_isMaximal S p] using le_comap_of_map_le h
  invFun Q := ⟨comap (algebraMap S Sₚ) Q.1, IsPrime.under S Q.1,
    liesOver_comap_of_liesOver p Rₚ Q.1⟩
  left_inv P := by
    have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver hp P.prop) (primesOver.isPrime p P)
    exact SetCoe.ext <| IsLocalization.AtPrime.comap_map_of_isMaximal S p Sₚ P.1
  right_inv Q := SetCoe.ext <| map_comap (algebraMapSubmonoid S p.primeCompl) Sₚ Q

@[simp]
theorem primesOverEquivPrimesOver_apply (hp : p ≠ ⊥) (P : p.primesOver S) :
    primesOverEquivPrimesOver p Rₚ Sₚ hp P = Ideal.map (algebraMap S Sₚ) P := rfl

@[simp]
theorem primesOverEquivPrimesOver_symm_apply (hp : p ≠ ⊥) (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ((primesOverEquivPrimesOver p Rₚ Sₚ hp).symm Q).1 = Ideal.comap (algebraMap S Sₚ) Q := rfl

theorem primesOverEquivPrimesOver_inertiagDeg_eq [p.IsMaximal] (hp : p ≠ ⊥) (P : p.primesOver S) :
    (maximalIdeal Rₚ).inertiaDeg (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ) =
      p.inertiaDeg P.val := by
  have : NeZero p := ⟨hp⟩
  have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver (NeZero.ne _) P.prop) inferInstance
  have : (P.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := liesOver_map_of_liesOver p _ _ _
  exact inertiaDeg_map_eq_inertiaDeg p _ _ _

theorem primesOverEquivPrimesOver_ramificationIdx_eq (hp : p ≠ ⊥) [NoZeroSMulDivisors R Rₚ]
    [NoZeroSMulDivisors R Sₚ] [NoZeroSMulDivisors S Sₚ] [NoZeroSMulDivisors Rₚ Sₚ]
    [IsDedekindDomain Rₚ] [IsDedekindDomain Sₚ] [IsPrincipalIdealRing Sₚ] (P : p.primesOver S) :
    (maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ)
      (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ) =
        p.ramificationIdx (algebraMap R S) P.val :=
  ramificationIdx_map_eq_ramificationIdx p _ _ _ hp

end IsDedekindDomain
