/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!

# Unramified and ramification index

We connect `Ideal.ramificationIdx` to the commutative algebra notion predicate of `IsUnramifiedAt`.

## Main result
- `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`:
  Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S ⊇ R` be a Dedekind domain
  that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`.

-/

public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation3 "e(" P "|" R ")" =>
  Ideal.ramificationIdx (Ideal.under R P) P

open IsLocalRing Algebra

lemma Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    {p : Ideal S} [p.IsPrime] [IsNoetherianRing S] [IsUnramifiedAt R p]
    (hp : p ≠ ⊥) [IsDomain S] [EssFiniteType R S] :
    e(p|R) = 1 :=
  let := Localization.AtPrime.algebraOfLiesOver (p.under R) p
  (Ideal.ramificationIdx_eq_one_of_map_localization Ideal.map_comap_le hp
    p.primeCompl_le_nonZeroDivisors
    ((isUnramifiedAt_iff_map_eq R (p.under R) p).mp ‹_›).2)

variable (R) in
lemma IsUnramifiedAt.of_liesOver_of_ne_bot
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] (hP₁ : P.primeCompl ≤ nonZeroDivisors T) (hP₂ : p ≠ ⊥ → P ≠ ⊥) :
    IsUnramifiedAt R p := by
  let p₀ : Ideal R := p.under R
  have : P.LiesOver p₀ := .trans P p p₀
  let := Localization.AtPrime.algebraOfLiesOver p₀ p
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver p₀ P
  have hp₀ : p₀ = P.under R := Ideal.LiesOver.over
  have : EssFiniteType S T := .of_comp R S T
  have := Algebra.EssFiniteType.isNoetherianRing S T
  rw [isUnramifiedAt_iff_map_eq R p₀ p]
  have ⟨h₁, h₂⟩ := (isUnramifiedAt_iff_map_eq R p₀ P).mp ‹_›
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField, ?_⟩
  by_cases hp : p = ⊥
  · have : p₀.map (algebraMap R S) = p := by
      subst hp
      exact le_bot_iff.mp (Ideal.map_comap_le)
    rw [IsScalarTower.algebraMap_eq _ S, ← Ideal.map_map, this,
      Localization.AtPrime.map_eq_maximalIdeal]
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hp Ideal.map_comap_le,
    ← not_ne_iff, Ideal.ramificationIdx_ne_one_iff Ideal.map_comap_le]
  intro H
  have := Ideal.ramificationIdx_eq_one_of_map_localization
    (hp₀ ▸ Ideal.map_comap_le) (hP₂ hp) hP₁ h₂
  rw [← not_ne_iff, Ideal.ramificationIdx_ne_one_iff (hp₀ ▸ Ideal.map_comap_le)] at this
  replace H := Ideal.map_mono (f := algebraMap S T) H
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_pow] at H
  refine this (H.trans (Ideal.pow_right_mono ?_ _))
  exact Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le

section IsUnramifiedIn

namespace Algebra

variable (R) in
/--
Up to technical conditions, If `T/S/R` is a tower of algebras, `P` is a prime of `T` unramified
in `R`, then `P ∩ S` (as a prime of `S`) is also unramified in `R`.
-/
lemma IsUnramifiedAt.of_liesOver
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] [IsDomain T] [Module.IsTorsionFree S T] : IsUnramifiedAt R p :=
  IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)

/-- Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S` be a Dedekind domain
that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`. -/
lemma isUnramifiedAt_iff_of_isDedekindDomain
    {p : Ideal S} [p.IsPrime] [IsDedekindDomain S] [EssFiniteType R S] [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    (hp : p ≠ ⊥) :
    Algebra.IsUnramifiedAt R p ↔ e(p|R) = 1 := by
  let := Localization.AtPrime.algebraOfLiesOver (p.under R) p
  rw [isUnramifiedAt_iff_map_eq R (p.under R) p, and_iff_right,
    Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hp Ideal.map_comap_le]
  have : Finite (R ⧸ p.under R) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (mt Ideal.eq_bot_of_comap_eq_bot hp)
  have : Finite ((p.under R).ResidueField) := IsLocalization.finite _
    (nonZeroDivisors (R ⧸ p.under R))
  infer_instance

/-- In characteristic zero the generic point is unramified: if `S` is a domain that is integral
over a characteristic-zero domain `R` and `R → S` is injective, then `S` is unramified at the zero
ideal. -/
theorem isUnramifiedAt_bot [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedAt R (⊥ : Ideal S) := by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  let : Field (Localization.AtPrime (⊥ : Ideal S)) := IsFractionRing.toField S
  have : FaithfulSMul R (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective R S)
  let := FractionRing.liftAlgebra R (Localization.AtPrime (⊥ : Ideal S))
  have : Algebra.IsAlgebraic (FractionRing R) (Localization.AtPrime ⊥) :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) (Localization.AtPrime (⊥ : Ideal S))
  have : FormallyUnramified (FractionRing R) (Localization.AtPrime (⊥ : Ideal S)) :=
    FormallyUnramified.of_isSeparable _ _
  exact FormallyUnramified.comp R (FractionRing R) (Localization.AtPrime ⊥)

/-- In characteristic zero, the zero ideal is unramified in an integral domain extension. -/
theorem isUnramifiedIn_bot [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedIn S (⊥ : Ideal R) := by
  intro P _ hP
  simpa [Ideal.eq_bot_of_liesOver_bot R P] using isUnramifiedAt_bot

/-- Let `S` be a Dedekind domain that is torsion-free over a domain `R`, and let `p ≠ ⊥` be an
ideal of `R`. Then `p` is unramified in `S` if and only if `S` is unramified at every maximal
ideal `P` of `S` lying over `p`.

See `Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain` if `R` is of characteristic zero. -/
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain' [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] {p : Ideal R} (hp : p ≠ ⊥) :
    IsUnramifiedIn S p ↔
      ∀ (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p → IsUnramifiedAt R P :=
  ⟨fun h P hP hlo ↦ h P hP.isPrime hlo,
    fun h P hP hlo ↦ h P (hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)) hlo⟩

/-- Let `S` be a Dedekind domain that is integral and torsion-free over a characteristic-zero
domain `R`. Then an ideal `p` of `R` is unramified in `S` if and only if `S` is unramified at every
maximal ideal `P` of `S` lying over `p`. -/
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [CharZero R] [Algebra.IsIntegral R S] {p : Ideal R} :
    IsUnramifiedIn S p ↔
      ∀ (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p → IsUnramifiedAt R P := by
  refine ⟨fun h P hP hlo ↦ h P hP.isPrime hlo, fun h P hP hlo ↦ ?_⟩
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · exact isUnramifiedAt_bot
  · exact h P (hP.isMaximal hPbot) hlo

/-- For a prime `𝔓` of `S` lying over an unramified prime `𝔭` of `R`, the ramification index
`e(𝔓 ∣ 𝔭)` equals `1`. -/
theorem IsUnramifiedIn.ramificationIdx_eq_one [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [Module.Finite ℤ R] [CharZero R] [EssFiniteType R S]
    [Algebra.IsIntegral R S] {𝔭 : Ideal R} (hunr : IsUnramifiedIn S 𝔭) (h𝔭 : 𝔭 ≠ ⊥) {𝔓 : Ideal S}
    [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx 𝔭 𝔓 = 1 := by
  rw [(Ideal.liesOver_iff 𝔓 𝔭).mp hP]
  exact (isUnramifiedAt_iff_of_isDedekindDomain (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓)).mp
    (hunr 𝔓 inferInstance hP)

/-- A nonzero ideal of `R` is unramified in `S` if and only if every prime ideal of `S` lying
over it has ramification index `1`. -/
theorem isUnramifiedIn_iff_forall_ramificationIdx_eq_one [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [Module.Finite ℤ R] [CharZero R] [EssFiniteType R S]
    [Algebra.IsIntegral R S] {𝔭 : Ideal R} (h𝔭 : 𝔭 ≠ ⊥) :
    IsUnramifiedIn S 𝔭 ↔
      ∀ (𝔓 : Ideal S) [𝔓.IsPrime], 𝔓.LiesOver 𝔭 → Ideal.ramificationIdx 𝔭 𝔓 = 1 := by
  refine ⟨fun hunr 𝔓 _ hP ↦ hunr.ramificationIdx_eq_one h𝔭 hP, fun h 𝔓 _ hP ↦ ?_⟩
  apply (isUnramifiedAt_iff_of_isDedekindDomain
    (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓)).mpr
  rw [← (Ideal.liesOver_iff 𝔓 𝔭).mp hP]
  exact h 𝔓 hP

end Algebra

end IsUnramifiedIn
