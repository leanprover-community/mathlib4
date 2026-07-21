/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# SANDBOX: missing general API for `IsDedekindDomain.HeightOneSpectrum.under`

Temporary file collecting the general lemmas about the extension map
`IsDedekindDomain.HeightOneSpectrum.under` that are missing from Mathlib. All results are `sorry`ed
for now; they are used to complete `Mathlib.NumberTheory.NumberField.DirichletDensity` (which is
then sorry-free). To be proved and upstreamed later.
-/

@[expose] public section

open Ideal Module

/-!
### Ideal-level general facts

`card_under_le` and `absNorm_under_dvd_absNorm` below are `HeightOneSpectrum` wrappers around these
ideal-level statements.
-/

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The number of primes of `B` over a prime `p` of `A` is at most `finrank A B`. -/
theorem ncard_primesOver_le [IsDomain A] [Module.Finite A B] [Module.Flat A B] {p : Ideal A}
    [p.IsPrime] [Finite (p.primesOver B)] :
    (p.primesOver B).ncard ≤ finrank A B := by
  have : Fintype (p.primesOver B) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones,
    ← sum_ramification_inertia_eq_finrank p B]
  exact Finset.sum_le_sum fun q _ ↦
    one_le_mul_of_one_le_of_one_le (ramificationIdx_pos q.1 A) (inertiaDeg_pos q.1 A)

/-- The norm of `I.under A` divides the norm of `I`. -/
theorem absNorm_under_dvd_absNorm [IsDedekindDomain A] [IsDedekindDomain B] [Module.Free ℤ A]
    [Module.Free ℤ B] (I : Ideal B) : absNorm (I.under A) ∣ absNorm I := by
  rw [absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.card_dvd_of_injective (quotientMap I (algebraMap A B) le_rfl)
    quotientMap_injective

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.IsIntegral A B]

/-- The prime `w` of `B` lies over `v` iff `w.under A = v`. -/
theorem under_eq_iff [IsDomain A] [IsDomain B] {w : HeightOneSpectrum B} {v : HeightOneSpectrum A} :
    w.under A = v ↔ w.asIdeal ∈ v.asIdeal.primesOver B := by
  refine ⟨fun h ↦ ⟨w.isPrime, ?_⟩, fun h ↦ HeightOneSpectrum.ext ?_⟩
  · rw [Ideal.liesOver_iff, ← under_asIdeal, h]
  · rw [under_asIdeal, ← h.2.over]

/-- The fiber of `under A` over `v` is equivalent, via `asIdeal`, to the prime ideals of `B`
above `v`. -/
def primesOverEquiv [IsDomain A] [IsDomain B] [IsTorsionFree A B] (v : HeightOneSpectrum A) :
    {w : HeightOneSpectrum B // w.under A = v} ≃ v.asIdeal.primesOver B where
  toFun w := ⟨w.1.asIdeal, under_eq_iff.mp w.2⟩
  invFun I := ⟨⟨I.1, I.2.1, fun h ↦ v.ne_bot <| by
    have hb := I.2.2.over; rwa [h, Ideal.under_bot] at hb⟩, under_eq_iff.mpr I.2⟩

/-- The fiber of `under A` over `v` is finite (it is the set of primes above `v`). -/
instance [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    (v : HeightOneSpectrum A) : Finite {w : HeightOneSpectrum B // w.under A = v} :=
  Finite.of_equiv _ (primesOverEquiv v).symm

end IsDedekindDomain.HeightOneSpectrum
