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

universe u v v' w

open Algebra Cardinal Module
open Module (rank)
open scoped nonZeroDivisors

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [NoZeroDivisors S] [Algebra R S]

namespace Module

section isFractionRing_isLocalization

variable
  (FS : Type v') [CommRing FS] [Algebra S FS] [IsFractionRing S FS]
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
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [rank_eq_zero_of_not_faithfulSMul, h, this]
  nontriviality R using subsingleton R S
  have : NoZeroDivisors R := .of_faithfulSMul R S
  have : Nontrivial S := FaithfulSMul.algebraMap_injective R S |>.nontrivial
  have : IsDomain S := {}
  let : Field FS := IsFractionRing.toField S
  let FR := FractionRing R
  let M' := LocalizedModule S⁰ M
  let f : M →ₗ[S] M' := LocalizedModule.mkLinearMap ..
  let : Algebra R FS := .restrictScalars R S FS
  let : Algebra FR FS := localizationAlgebra R⁰ S
  have : IsScalarTower R S FS := .of_algebraMap_eq' rfl
  have : IsScalarTower R FR FS := isScalarTower_localizationAlgebra R⁰ S
  let : Module FS M' := LocalizedModule.moduleOfIsLocalization
  let : Module FR M' := .restrictScalars _ FS M'
  have : IsScalarTower R FS M' := .to₁₃₄ (N := S) ..
  have : IsScalarTower FR FS M' := .restrictScalars ..
  have : IsScalarTower R FR M' := .to₁₂₄ (P := FS) ..
  have h₀ := IsLocalizedModule.isBaseChange R⁰ FR (IsScalarTower.toAlgHom R S FS).toLinearMap
  have h₁ := IsLocalizedModule.isBaseChange S⁰ FS f
  have h₂ : IsBaseChange FR (f : M →ₗ[R] M') :=
    isLocalizedModule_iff_isBaseChange .. |>.mpr h₁ |>.restrictScalars.isBaseChange R⁰ ..
  have a := h₀.lift_rank_eq
  have b := h₁.lift_rank_eq
  have c := h₂.lift_rank_eq
  rw [lift_id', lift_umax] at b c
  rw [← b, ← c, ← lift_inj.{_, v'}, lift_mul, ← lift_rank_mul_lift_rank FR FS M',
    ← lift_lift.{v, w}, a, lift_lift, lift_lift]

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
  (FS : Type v') [Field FS] [Algebra S FS]
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
  let mS := algebraMapSubmonoid S R⁰
  let FS := Localization mS
  let M' := LocalizedModule mS M
  let pS : S →ₗ[R] FS := IsScalarTower.toAlgHom R S FS |>.toLinearMap
  let pM : M →ₗ[R] M' := LocalizedModule.mkLinearMap .. |>.restrictScalars R
  let : Module FR M' := .restrictScalars _ FS _
  have : IsScalarTower FR FS M' := .restrictScalars ..
  have : IsScalarTower R FR M' := .to₁₂₄ (P := FS) ..
  have hFS := IsLocalizedModule.isBaseChange R⁰ FR pS
  have : IsLocalizedModule R⁰ pM :=
    localizedModuleIsLocalizedModule mS |>.restrictScalars R⁰
  have hM' := this.isBaseChange R⁰ FR
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

variable
  [h : Algebra.IsAlgebraic R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (M₁ : Type v) [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]

/-- **Tower law over algebraic extensions of domains.**
if `R` and `S` have no zero divisors, `S` is an algebraic `R`-algebra, and
`M` is a `S`-module, then
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
if `R` and `S` have no zero divisors, `S` is an algebraic `R`-algebra, and
`M` is a `S`-module, then
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
if `R` and `S` have no zero divisors, `S` is an algebraic `R`-algebra, and
`M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Module.finrank_mul_finrank` for when your modules are free. -/
theorem finrank_mul_finrank : finrank R S * finrank S M = finrank R M := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [finrank_eq_zero_of_not_faithfulSMul, h, this]
  apply finrank_mul_finrank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

end Algebra.IsAlgebraic
