/-
Copyright (c) 2026 Robert Shlyakhtenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Shlyakhtenko
-/

module

public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Going up

In this file we define a predicate `Algebra.HasGoingUp`: An `R`-algebra `S` satisfies
`Algebra.HasGoingUp R S` if for every pair of prime ideals `p ≤ q` of `R` with
`P` a prime of `S` lying above `p`, there exists a prime `P ≤ Q` of `S` lying above `q`.

This file closely mirrors `Mathlib.RingTheory.Ideal.GoingDown`.

## Main results

- `Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap`: going up is equivalent
  to specializations lifting along `Spec S → Spec R`.
- `Algebra.HasGoingUp.of_isIntegral`: integral algebras satisfy going up.
-/

@[expose] public section

/--
An `R`-algebra `S` satisfies `Algebra.HasGoingUp R S` if for every pair of
prime ideals `p ≤ q` of `R` with `P` a prime of `S` lying above `p`, there exists a
prime `P ≤ Q` of `S` lying above `q`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_ge_liesOver_of_le` for applying it. -/
@[stacks 00HV "(1)"]
class Algebra.HasGoingUp
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_ideal_ge_liesOver_of_lt {q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] :
    P.under R < q → ∃ P ≤ Q, Q.IsPrime ∧ Q.LiesOver q

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma Ideal.exists_ideal_ge_liesOver_of_le [Algebra.HasGoingUp R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hle : p ≤ q) :
    ∃ Q ≥ P, Q.IsPrime ∧ Q.LiesOver q := by
  rcases eq_or_ne p q with rfl | h
  · use P
  · rw [P.over_def p] at hle h
    exact Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt P (lt_of_le_of_ne hle h)

lemma Ideal.exists_ideal_gt_liesOver_of_lt [Algebra.HasGoingUp R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hpq : p < q) :
    ∃ Q > P, Q.IsPrime ∧ Q.LiesOver q := by
  obtain ⟨Q, hPQ, hQ, hQq⟩ := P.exists_ideal_ge_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨Q, lt_of_le_of_ne hPQ fun h ↦ ?_, hQ, hQq⟩
  subst Q
  simp [P.over_def p, P.over_def q] at hpq

/-- This generalizes `exists_ideal_over_prime_of_isIntegral_of_isPrime`
to arbitrary length chains. -/
lemma Ideal.exists_ltSeries_of_hasGoingUp [Algebra.HasGoingUp R S]
    (l : LTSeries (PrimeSpectrum R))
    (P : Ideal S) [P.IsPrime]
    [lo : P.LiesOver (RelSeries.head l).asIdeal] :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧
      L.head = (⟨P, inferInstance⟩ : PrimeSpectrum S) ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) (L.toList) = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    refine ⟨RelSeries.singleton _ ⟨P, inferInstance⟩, rfl, rfl, ?_⟩
    simpa [PrimeSpectrum.ext_iff] using lo.over.symm
  | cons l q lt ih =>
    refine ⟨L.cons ⟨P, inferInstance⟩ (by
      simp_all only [Set.mem_setOf_eq, gt_iff_lt]
      exact PQlt), by simpa using len, rfl, ?_⟩
    simpa [spec, PrimeSpectrum.ext_iff] using lo.over.symm

namespace Algebra.HasGoingUp

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has the going up property if and only if specializations lift
along `Spec S → Spec R`. -/
@[stacks 00HW "(2)"]
lemma iff_specializingMap_primeSpectrumComap :
    Algebra.HasGoingUp R S ↔
      SpecializingMap (PrimeSpectrum.comap (algebraMap R S)) := by
  refine ⟨?_, fun h ↦ ⟨fun {q} hq P hP hlt ↦ ?_⟩⟩
  · intro h P q hq
    simp only [flip] at hq
    rw [← PrimeSpectrum.le_iff_specializes] at hq
    obtain ⟨Q, hle, hQ, h⟩ := P.asIdeal.exists_ideal_ge_liesOver_of_le (q := q.asIdeal)
      (p := P.asIdeal.under R) hq
    refine ⟨⟨Q, hQ⟩, (PrimeSpectrum.le_iff_specializes P _).mp hle, ?_⟩
    ext : 1
    exact h.over.symm
  · have : PrimeSpectrum.comap (algebraMap R S) ⟨P, hP⟩ ⤳ (⟨q, hq⟩ : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hlt.le
    obtain ⟨Q, hs, heq⟩ := h this
    refine ⟨Q.asIdeal, (PrimeSpectrum.le_iff_specializes _ _).mpr hs, Q.2, ⟨?_⟩⟩
    simpa [PrimeSpectrum.ext_iff] using heq.symm

variable (R S) in
@[stacks 00HX]
lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.HasGoingUp R S] [Algebra.HasGoingUp S T] :
    Algebra.HasGoingUp R T := by
  rw [iff_specializingMap_primeSpectrumComap, IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply SpecializingMap.comp
  · rwa [← iff_specializingMap_primeSpectrumComap]
  · rwa [← iff_specializingMap_primeSpectrumComap]

/-- Integral algebras satisfy the going up property. -/
@[stacks 00GU]
instance of_isIntegral [Algebra.IsIntegral R S] : Algebra.HasGoingUp R S where
  exists_ideal_ge_liesOver_of_lt {q} _ P _ hPq :=
    let ⟨Q, hPQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q P hPq.le
    ⟨Q, hPQ, hQ, ⟨hQq.symm⟩⟩

end Algebra.HasGoingUp
