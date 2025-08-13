/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Algebraic

/-!

# Unramified and ramification index

We connect `Ideal.ramificationIdx` to the commutative algebra notion predicate of `IsUnramifiedAt`.

## Main result
- `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`:
  Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S ⊇ R` be a dedekind domain
  that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`.

-/

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation3 "e(" P "|" R ")" =>
  Ideal.ramificationIdx (algebraMap _ _) (Ideal.under R P) P

open IsLocalRing Algebra

lemma Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    {p : Ideal S} [p.IsPrime] [IsNoetherianRing S] [IsUnramifiedAt R p]
    (hp : p ≠ ⊥) [IsDomain S] [EssFiniteType R S] :
    e(p|R) = 1 :=
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

variable (R) in
/--
Up to technical conditions, If `T/S/R` is a tower of algebras, `P` is a prime of `T` unramified
in `R`, then `P ∩ S` (as a prime of `S`) is also unramified in `R`.
-/
lemma Algebra.IsUnramifiedAt.of_liesOver
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] [IsDomain T] [NoZeroSMulDivisors S T] : IsUnramifiedAt R p :=
  IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)

set_option synthInstance.maxHeartbeats 25000 in -- infer_instance timeout
/-- Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S` be a dedekind domain
that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`. -/
lemma Algebra.isUnramifiedAt_iff_of_isDedekindDomain
    {p : Ideal S} [p.IsPrime] [IsDedekindDomain S] [EssFiniteType R S] [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    (hp : p ≠ ⊥) :
    Algebra.IsUnramifiedAt R p ↔ e(p|R) = 1 := by
  rw [isUnramifiedAt_iff_map_eq R (p.under R) p, and_iff_right,
    Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hp Ideal.map_comap_le]
  have : Finite (R ⧸ p.under R) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (mt Ideal.eq_bot_of_comap_eq_bot hp)
  have : Finite ((p.under R).ResidueField) := IsLocalization.finite _
    (nonZeroDivisors (R ⧸ p.under R))
  infer_instance
