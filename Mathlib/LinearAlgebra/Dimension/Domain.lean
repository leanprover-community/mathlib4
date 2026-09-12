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
- `Module.rank_mul_rank_of_isFractionRing_isLocalization` & variants:
  when `(R⁰)⁻¹ S = (S⁰)⁻¹ S`.
- `Module.rank_mul_rank_of_field_isLocalization` & variants:
  wrapper for the above that only asks `(R⁰)⁻¹ S` to be a field.
- `Module.IsTorsionFree.erank_mul_erank`, `Module.IsTorsionFree.finrank_mul_finrank`:
  when `M` is torsion-free over `S`. We only get truncated cardinalities.
- `Module.finrank_mul_finrank'`:
  alias for the above.
- `Algebra.IsAlgebraic.rank_mul_rank` & variants:
  when `S/R` is algebraic.
-/

public section

universe u u' v v' w w'

open Algebra Cardinal Module
open Module (rank)
open scoped nonZeroDivisors

variable
  (R : Type u) (S : Type v) [CommRing R] [CommRing S] [NoZeroDivisors S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (M₁ : Type v) [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]

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
    simp [rank_eq_zero_of_not_faithfulSMul h, rank_eq_zero_of_not_faithfulSMul this]
  nontriviality R using subsingleton R S
  have _ : NoZeroDivisors R := .of_faithfulSMul R S
  have _ : Nontrivial S := FaithfulSMul.algebraMap_injective R S |>.nontrivial
  have _ : IsDomain S := {}
  let _ : Field FS := IsFractionRing.toField S
  let FR := FractionRing R
  let M' := LocalizedModule S⁰ M
  let f : M →ₗ[S] M' := LocalizedModule.mkLinearMap ..
  let _ : Algebra R FS := .restrictScalars R S FS
  let _ : Algebra FR FS := localizationAlgebra R⁰ S
  have _ : IsScalarTower R S FS := .of_algebraMap_eq' rfl
  have _ : IsScalarTower R FR FS := isScalarTower_localizationAlgebra R⁰ S
  let _ : Module FS M' := LocalizedModule.moduleOfIsLocalization
  let _ : Module FR M' := .restrictScalars _ FS M'
  have _ : IsScalarTower R FS M' := .to₁₃₄ (N := S) ..
  have _ : IsScalarTower FR FS M' := .restrictScalars ..
  have _ : IsScalarTower R FR M' := .to₁₂₄ (P := FS) ..
  have h₀ := IsLocalizedModule.isBaseChange R⁰ FR (IsScalarTower.toAlgHom R S FS).toLinearMap
  have h₁ := IsLocalizedModule.isBaseChange S⁰ FS f
  have h₂ : IsBaseChange FR (f : M →ₗ[R] M') :=
    isLocalizedModule_iff_isBaseChange .. |>.mpr h₁ |>.restrictScalars.isBaseChange R⁰ ..
  have a := h₀.lift_rank_eq
  have b := h₁.lift_rank_eq
  have c := h₂.lift_rank_eq
  clear * - a b c
  rw [lift_id', lift_umax] at b c
  rw [← b, ← c, ← lift_inj.{_, v'}, lift_mul]
  convert ← lift_rank_mul_lift_rank FR FS M'
  rw [← lift_lift.{v, w}, a, lift_lift, lift_lift]

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S = (S⁰)⁻¹ S`,
we obtain a tower law.

See `_root.rank_mul_rank` for when your modules are free.
-/
theorem rank_mul_rank_of_isFractionRing_isLocalization :
    rank R S * rank S M₁ = rank R M₁ := by
  convert lift_rank_mul_lift_rank_of_isFractionRing_isLocalization R S FS M₁ <;> rw [lift_id]

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S = (S⁰)⁻¹ S`,
we obtain a tower law.

See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem finrank_mul_finrank_of_isFractionRing_isLocalization :
    finrank R S * finrank S M = finrank R M := by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (rank R S), ← toNat_lift.{v} (rank S M), ← toNat_mul,
    lift_rank_mul_lift_rank_of_isFractionRing_isLocalization R S FS, toNat_lift]

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

See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem lift_rank_mul_lift_rank_of_field_isLocalization :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) :=
  have _ : IsFractionRing S FS := .of_semifield_isLocalization (algebraMapSubmonoid S R⁰) _
  lift_rank_mul_lift_rank_of_isFractionRing_isLocalization R S FS ..

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S` is a field,
we obtain a tower law.

See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem rank_mul_rank_of_field_isLocalization :
    rank R S * rank S M₁ = rank R M₁ :=
  have _ : IsFractionRing S FS := .of_semifield_isLocalization (algebraMapSubmonoid S R⁰) _
  rank_mul_rank_of_isFractionRing_isLocalization R S FS ..

/-- **Tower law over domains.**
When `M` is a module over an algebra `S/R` of domains such that `(R⁰)⁻¹ S` is a field,
we obtain a tower law.

See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem finrank_mul_finrank_of_field_isLocalization :
    finrank R S * finrank S M = finrank R M :=
  have _ : IsFractionRing S FS := .of_semifield_isLocalization (algebraMapSubmonoid S R⁰) _
  finrank_mul_finrank_of_isFractionRing_isLocalization R S FS ..

end field_isLocalization

/-- **Tower law for torsion-free modules.**
The tower law for ENat `Module.rank` of a `S`-torsion-free module over an algebra `S/R` of domains.
See `Module.IsTorsionFree.finrank_mul_finrank` for a `finrank` version.
-/
theorem IsTorsionFree.erank_mul_erank [hM : IsTorsionFree S M] :
    toENat (rank R S) * toENat (rank S M) = toENat (rank R M) := by
  by_cases h : FaithfulSMul R S
  case neg =>
    have : ¬ FaithfulSMul R M := mt (·.tower_bot ..) h
    simp [rank_eq_zero_of_not_faithfulSMul h, rank_eq_zero_of_not_faithfulSMul this]
  nontriviality R using subsingleton R S
  have _ : NoZeroDivisors R := .of_faithfulSMul R S
  have _ : Nontrivial S := FaithfulSMul.algebraMap_injective R S |>.nontrivial
  have _ : IsDomain S := {}
  nontriviality M using rank_subsingleton'
  let R' := FractionRing R
  let mS := algebraMapSubmonoid S R⁰
  let S' := Localization mS
  let M' := LocalizedModule mS M
  let fS : S →ₗ[R] S' := IsScalarTower.toAlgHom R S S' |>.toLinearMap
  let fM : M →ₗ[S] M' := LocalizedModule.mkLinearMap ..
  let _ : Module R' M' := .restrictScalars _ S' _
  have _ : IsScalarTower R' S' M' := .restrictScalars ..
  have _ : IsScalarTower R R' M' := .to₁₂₄ (P := S') ..
  have hS' := IsLocalizedModule.isBaseChange R⁰ R' fS
  have : IsLocalizedModule R⁰ (fM : M →ₗ[R] M') :=
    localizedModuleIsLocalizedModule mS |>.restrictScalars R⁰
  have hM' := this.isBaseChange R⁰ R'
  by_cases! hRS : rank R S < .aleph0
  · have _ : Module.Finite R' S' := rank_lt_aleph0_iff.mp <| hS'.rank_eq ▸ hRS
    have _ : IsDomain S' := IsLocalization.isDomain_localization <| by
      rintro _ ⟨r, hr, rfl⟩
      simpa using hr
    let _ : Field S' := fieldOfFiniteDimensional R' S'
    simpa using congr($(lift_rank_mul_lift_rank_of_field_isLocalization R S S' M).toENat)
  · have hm : 0 < rank S M := rank_pos_iff_exists_ne_zero.mpr <| exists_ne 0
    rw [toENat_eq_top.mpr hRS, ENat.top_mul (by simpa using hm.ne'), eq_comm, toENat_eq_top]
    by_contra! hRM : rank R M < .aleph0
    have _ : Module.Finite R' M' := by
      rwa [← rank_lt_aleph0_iff, ← lift_id'.{w, v} (rank R' M'), hM'.lift_rank_eq, lift_lt_aleph0]
    -- it would also suffice to have FaithfulSMul S' M' (and Nontrivial M') at this point
    have ⟨m, hm⟩ := exists_ne (0 : M)
    let f : S →ₗ[R] M := LinearMap.lsmul S M |>.flip m
    have : Module.Finite R' S' :=
      .of_injective (IsLocalizedModule.mapExtendScalars R⁰ fS (fM : M →ₗ[R] M') R' f) <|
        IsLocalizedModule.map_injective (h_inj := smul_left_injective _ hm) ..
    exact hRS.not_gt <| hS'.rank_eq ▸ rank_lt_aleph0 ..

/-- **Tower law for torsion-free modules.**
The tower law for `Module.finrank` of a `S`-torsion-free module over an algebra `S/R` of domains.
See `Module.finrank_mul_finrank` for when your modules are free.
-/
theorem IsTorsionFree.finrank_mul_finrank [h : IsTorsionFree S M] :
    finrank R S * finrank S M = finrank R M := by
  simpa [finrank] using congr($(h.erank_mul_erank R S M).toNat)

alias finrank_mul_finrank' := IsTorsionFree.finrank_mul_finrank

end Module

namespace Algebra.IsAlgebraic

variable [FaithfulSMul R S] [h : Algebra.IsAlgebraic R S]

/-- **Tower law over algebraic extensions of domains.**
if `R` and `S` have no zero divisors, `S` is a faithful algebraic `R`-algebra, and
`M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Algebra.IsAlgebraic.rank_mul_rank` for a non–universe polymorphic version, and
`_root_.lift_rank_mul_lift_rank` for when your modules are free. -/
theorem lift_rank_mul_lift_rank :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) :=
  lift_rank_mul_lift_rank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

/-- **Tower law over algebraic extensions of domains.**
if `R` and `S` have no zero divisors, `S` is a faithful algebraic `R`-algebra, and
`M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Algebra.IsAlgebraic.lift_rank_mul_lift_rank` for a universe polymorphic version, and
`_root_.rank_mul_rank` for when your modules are free. -/
theorem rank_mul_rank :
    rank R S * rank S M₁ = rank R M₁ :=
  rank_mul_rank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

/-- **Tower law over algebraic extensions of domains.**
if `R` and `S` have no zero divisors, `S` is a faithful algebraic `R`-algebra, and
`M` is a `S`-module, then
$$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$$.

See `Module.finrank_mul_finrank` for when your modules are free. -/
theorem finrank_mul_finrank :
    finrank R S * finrank S M = finrank R M :=
  finrank_mul_finrank_of_isFractionRing_isLocalization (FS := FractionRing S) ..

end Algebra.IsAlgebraic
