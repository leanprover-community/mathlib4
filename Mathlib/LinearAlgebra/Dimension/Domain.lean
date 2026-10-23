/-
Copyright (c) 2026 Albert Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Albert Smith
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Basic

import Mathlib.RingTheory.Algebraic.Integral

/-!
# Rank theorems over domains

This file proves some `Module.rank` and `Module.finrank` theorems for modules over domains.

## Main results

Let `M/S/R` be a tower where `R`, `S` are domains.

We obtain the following tower laws:
- `Module.rank_mul_rank_of_isFractionRing_isLocalization` & variants: when `(R⁰)⁻¹ S = (S⁰)⁻¹ S`.
- `Module.rank_mul_rank_of_field_isLocalization` & variants:
  wrapper for the above that only asks `(R⁰)⁻¹ S` to be a field.
- `Module.IsTorsionFree.erank_mul_erank`, `Module.IsTorsionFree.finrank_mul_finrank`:
  when `M` is torsion-free over `S`. We only get truncated cardinalities.
- `Algebra.IsAlgebraic.rank_mul_rank` & variants: when `S/R` is algebraic.
-/

public section

universe v w

open Algebra Cardinal Module
open Module (rank)
open scoped nonZeroDivisors

variable (R : Type*) (S : Type v) [CommRing R] [CommRing S] [NoZeroDivisors S] [Algebra R S]

namespace Module

private lemma lift_rank_mul_lift_rank_of_isFractionRing_localization
    [IsFractionRing S (Localization (algebraMapSubmonoid S R⁰))]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [rank_eq_zero_of_not_faithfulSMul, h, this]
  nontriviality R using subsingleton R S
  have : NoZeroDivisors R := .of_faithfulSMul R S
  have : Nontrivial S := FaithfulSMul.algebraMap_injective R S |>.nontrivial
  have : IsDomain S := {}
  let FR := FractionRing R
  let mS := algebraMapSubmonoid S R⁰
  let FS := Localization mS
  let M' := LocalizedModule mS M
  let : Field FS := IsFractionRing.toField S
  let f : M →ₗ[S] M' := LocalizedModule.mkLinearMap ..
  let : Module FR M' := .restrictScalars _ FS M'
  have : IsScalarTower FR FS M' := .restrictScalars ..
  have : IsScalarTower R FR M' := .to₁₂₄ (P := FS) ..
  have h₀ := IsLocalizedModule.isBaseChange R⁰ FR (IsScalarTower.toAlgHom R S FS).toLinearMap
    |>.rank_eq
  have h₁ := IsLocalizedModule.isBaseChange mS FS f |>.lift_rank_eq
  have h₂ := IsLocalizedModule.restrictScalars R⁰ f |>.isBaseChange R⁰ FR |>.lift_rank_eq
  rw [lift_id'.{w, v}, lift_umax] at h₁ h₂
  have := lift_rank_mul_lift_rank FR FS M'
  rw [lift_id'.{v, w}, lift_id'.{v, w}, lift_umax] at this
  rw [← h₀, ← h₁, ← h₂, this]

section isFractionRing_isLocalization

variable
  (FS : Type*) [CommRing FS] [Algebra S FS] [IsFractionRing S FS]
  [h : IsLocalization (algebraMapSubmonoid S R⁰) FS]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (M₁ : Type v) [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]
include h

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S = (S⁰)⁻¹ S`,
we obtain a tower law.

See `_root.lift_rank_mul_lift_rank` for when your modules are free.
-/
theorem lift_rank_mul_lift_rank_of_isFractionRing_isLocalization :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) :=
  have : IsFractionRing S (Localization (algebraMapSubmonoid S R⁰)) :=
    .of_algEquiv <| IsLocalization.algEquiv (algebraMapSubmonoid S R⁰) FS _
  lift_rank_mul_lift_rank_of_isFractionRing_localization ..

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S = (S⁰)⁻¹ S`,
we obtain a tower law.

See `_root.rank_mul_rank` for when your modules are free.
-/
theorem rank_mul_rank_of_isFractionRing_isLocalization :
    rank R S * rank S M₁ = rank R M₁ := by
  simpa using lift_rank_mul_lift_rank_of_isFractionRing_isLocalization R S FS M₁

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S = (S⁰)⁻¹ S`,
we obtain a tower law.

See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem finrank_mul_finrank_of_isFractionRing_isLocalization :
    finrank R S * finrank S M = finrank R M := by
  simpa [finrank] using
    congr(toNat $(lift_rank_mul_lift_rank_of_isFractionRing_isLocalization R S FS M))

end isFractionRing_isLocalization

section field_isLocalization

variable
  (FS : Type*) [Field FS] [Algebra S FS]
  [h : IsLocalization (algebraMapSubmonoid S R⁰) FS]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (M₁ : Type v) [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]
include h

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S` is a field,
we obtain a tower law.

See `_root.lift_rank_mul_lift_rank` for when your modules are free.
-/
theorem lift_rank_mul_lift_rank_of_field_isLocalization :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) :=
  have : IsFractionRing S FS := .of_semifield_isLocalization (algebraMapSubmonoid S R⁰) _
  lift_rank_mul_lift_rank_of_isFractionRing_isLocalization R S FS ..

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S` is a field,
we obtain a tower law.

See `_root.rank_mul_rank` for when your modules are free.
-/
theorem rank_mul_rank_of_field_isLocalization :
    rank R S * rank S M₁ = rank R M₁ :=
  have : IsFractionRing S FS := .of_semifield_isLocalization (algebraMapSubmonoid S R⁰) _
  rank_mul_rank_of_isFractionRing_isLocalization R S FS ..

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S` is a field,
we obtain a tower law.

See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem finrank_mul_finrank_of_field_isLocalization :
    finrank R S * finrank S M = finrank R M :=
  have : IsFractionRing S FS := .of_semifield_isLocalization (algebraMapSubmonoid S R⁰) _
  finrank_mul_finrank_of_isFractionRing_isLocalization R S FS ..

end field_isLocalization

variable (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- **Tower law for torsion-free modules.**
The tower law for ENat `Module.rank` of a `S`-torsion-free module over an algebra `S/R` of domains.
See `Module.IsTorsionFree.finrank_mul_finrank` for a `finrank` version.
-/
theorem IsTorsionFree.erank_mul_erank [IsTorsionFree S M] :
    toENat (rank R S) * toENat (rank S M) = toENat (rank R M) := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [rank_eq_zero_of_not_faithfulSMul, h, this]
  nontriviality R using subsingleton R S
  have : NoZeroDivisors R := .of_faithfulSMul R S
  have : Nontrivial S := FaithfulSMul.algebraMap_injective R S |>.nontrivial
  have : IsDomain S := {}
  nontriviality M using rank_subsingleton'
  let FR := FractionRing R
  let FS := Localization (algebraMapSubmonoid S R⁰)
  have hFS := IsLocalizedModule.isBaseChange R⁰ FR <| IsScalarTower.toAlgHom R S FS |>.toLinearMap
  by_cases! hRS : rank R S < .aleph0
  · have : Module.Finite FR FS := rank_lt_aleph0_iff.mp <| hFS.rank_eq ▸ hRS
    have : IsDomain FS := IsLocalization.isDomain_localization <|
      map_le_nonZeroDivisors_of_injective _ h.algebraMap_injective le_rfl
    let : Field FS := fieldOfFiniteDimensional FR FS
    simpa using congr($(lift_rank_mul_lift_rank_of_field_isLocalization R S FS M).toENat)
  · rw [toENat_eq_top.mpr hRS, ENat.top_mul (by simpa using rank_pos.ne'), eq_comm, toENat_eq_top]
    have ⟨m, hm⟩ := exists_ne (0 : M)
    have hRSM := LinearMap.toSpanSingleton S M m |>.restrictScalars R
      |>.lift_rank_le_of_injective <| smul_left_injective _ hm
    exact aleph0_le_lift.mp <| .trans (aleph0_le_lift.mpr hRS) hRSM

/-- **Tower law for torsion-free modules.**
The tower law for `Module.finrank` of a `S`-torsion-free module over an algebra `S/R` of domains.
See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem IsTorsionFree.finrank_mul_finrank [IsTorsionFree S M] :
    finrank R S * finrank S M = finrank R M := by
  simpa [finrank] using congr($(erank_mul_erank R S M).toNat)

end Module

namespace Algebra.IsAlgebraic

variable [Algebra.IsAlgebraic R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (M₁ : Type v) [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]

/-- **Tower law over algebraic extensions of domains.**
If `S` has no zero divisors, `S` is algebraic over `R`, and `M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Algebra.IsAlgebraic.rank_mul_rank` for a non–universe polymorphic version, and
`_root_.lift_rank_mul_lift_rank` for when your modules are free. -/
theorem lift_rank_mul_lift_rank :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [rank_eq_zero_of_not_faithfulSMul, h, this]
  apply lift_rank_mul_lift_rank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

/-- **Tower law over algebraic extensions of domains.**
If `S` has no zero divisors, `S` is algebraic over `R`, and `M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Algebra.IsAlgebraic.lift_rank_mul_lift_rank` for a universe polymorphic version, and
`_root_.rank_mul_rank` for when your modules are free. -/
theorem rank_mul_rank : rank R S * rank S M₁ = rank R M₁ := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M₁ := mt (·.tower_bot ..) h
    simp [rank_eq_zero_of_not_faithfulSMul, h, this]
  apply rank_mul_rank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

/-- **Tower law over algebraic extensions of domains.**
If `S` has no zero divisors, `S` is algebraic over `R`, and `M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Module.finrank_mul_finrank` for when your modules are free. -/
theorem finrank_mul_finrank : finrank R S * finrank S M = finrank R M := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [finrank_eq_zero_of_not_faithfulSMul, h, this]
  apply finrank_mul_finrank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

end Algebra.IsAlgebraic
