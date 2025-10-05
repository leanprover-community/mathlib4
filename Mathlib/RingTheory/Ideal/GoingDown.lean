/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Going down

In this file we define a predicate `Algebra.HasGoingDown`: An `R`-algebra `S` satisfies
`Algebra.HasGoingDown R S` if for every pair of prime ideals `p ≤ q` of `R` with `Q` a prime
of `S` lying above `q`, there exists a prime `P ≤ Q` of `S` lying above `p`.

## Main results

- `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`: going down is equivalent
  to generalizations lifting along `Spec S → Spec R`.
- `Algebra.HasGoingDown.of_flat`: flat algebras satisfy going down.

## TODOs

- An integral extension of domains with normal base satisfies going down.

-/

/--
An `R`-algebra `S` satisfies `Algebra.HasGoingDown R S` if for every pair of
prime ideals `p ≤ q` of `R` with `Q` a prime of `S` lying above `q`, there exists a
prime `P ≤ Q` of `S` lying above `p`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_le_liesOver_of_le` for applying it.
-/
@[stacks 00HV "(2)"]
class Algebra.HasGoingDown (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_ideal_le_liesOver_of_lt {p : Ideal R} [p.IsPrime] (Q : Ideal S) [Q.IsPrime] :
    p < Q.under R → ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma Ideal.exists_ideal_le_liesOver_of_le [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hle : p ≤ q) :
    ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p := by
  by_cases h : p = q
  · subst h
    use Q
  · have := Q.over_def q
    subst this
    exact Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q (lt_of_le_of_ne hle h)

lemma Ideal.exists_ideal_lt_liesOver_of_lt [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hpq : p < q) : ∃ P < Q, P.IsPrime ∧ P.LiesOver p := by
  obtain ⟨P, hPQ, _, _⟩ := Q.exists_ideal_le_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨P, ?_, inferInstance, inferInstance⟩
  by_contra hc
  have : P = Q := eq_of_le_of_not_lt hPQ hc
  subst this
  simp [P.over_def p, P.over_def q] at hpq

lemma Ideal.exists_ltSeries_of_hasGoingDown [Algebra.HasGoingDown R S]
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime] [lo : P.LiesOver l.last.asIdeal] :
    ∃ (L : LTSeries (PrimeSpectrum S)),
      L.length = l.length ∧
      L.last = ⟨P, inferInstance⟩ ∧
      List.map (algebraMap R S).specComap L.toList = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    use RelSeries.singleton _ ⟨P, inferInstance⟩
    simp only [RelSeries.singleton_length, RelSeries.last_singleton, RelSeries.toList_singleton,
      List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
    ext : 1
    simpa using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.last_cons] at lo
    obtain ⟨L, len, last, spec⟩ := ih P
    have : L.head.asIdeal.LiesOver l.head.asIdeal := by
      constructor
      rw [← L.toList_getElem_zero_eq_head, ← l.toList_getElem_zero_eq_head, Ideal.under_def]
      have : l.toList[0] = (algebraMap R S).specComap L.toList[0] := by
        rw [List.getElem_map_rev (algebraMap R S).specComap, List.getElem_of_eq spec.symm _]
      rwa [RingHom.specComap, PrimeSpectrum.ext_iff] at this
    obtain ⟨Q, Qlt, hQ, Qlo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt L.head.asIdeal lt
    use L.cons ⟨Q, hQ⟩ Qlt
    simp only [RelSeries.cons_length, add_left_inj, RelSeries.last_cons]
    exact ⟨len, last, by simpa [spec] using PrimeSpectrum.ext_iff.mpr Qlo.over.symm⟩

namespace Algebra.HasGoingDown

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has the going down property if and only if generalizations lift
along `Spec S → Spec R`. -/
@[stacks 00HW "(1)"]
lemma iff_generalizingMap_primeSpectrumComap :
    Algebra.HasGoingDown R S ↔
      GeneralizingMap (PrimeSpectrum.comap (algebraMap R S)) := by
  refine ⟨?_, fun h ↦ ⟨fun {p} hp Q hQ hlt ↦ ?_⟩⟩
  · intro h Q p hp
    rw [← PrimeSpectrum.le_iff_specializes] at hp
    obtain ⟨P, hle, hP, h⟩ := Q.asIdeal.exists_ideal_le_liesOver_of_le (p := p.asIdeal)
      (q := Q.asIdeal.under R) hp
    refine ⟨⟨P, hP⟩, (PrimeSpectrum.le_iff_specializes _ Q).mp hle, ?_⟩
    ext : 1
    exact h.over.symm
  · have : (⟨p, hp⟩ : PrimeSpectrum R) ⤳ (PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQ⟩) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hlt.le
    obtain ⟨P, hs, heq⟩ := h this
    refine ⟨P.asIdeal, (PrimeSpectrum.le_iff_specializes _ _).mpr hs, P.2, ⟨?_⟩⟩
    simpa [PrimeSpectrum.ext_iff] using heq.symm

variable (R S) in
@[stacks 00HX]
lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.HasGoingDown R S] [Algebra.HasGoingDown S T] :
    Algebra.HasGoingDown R T := by
  rw [iff_generalizingMap_primeSpectrumComap, IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp, ContinuousMap.coe_comp]
  apply GeneralizingMap.comp
  · rwa [← iff_generalizingMap_primeSpectrumComap]
  · rwa [← iff_generalizingMap_primeSpectrumComap]

/-- If for every prime of `S`, the map `Spec Sₚ → Spec Rₚ` is surjective,
the algebra satisfies going down. -/
lemma of_specComap_localRingHom_surjective
    (H : ∀ (P : Ideal S) [P.IsPrime], Function.Surjective
      (Localization.localRingHom (P.under R) P (algebraMap R S) rfl).specComap) :
    Algebra.HasGoingDown R S where
  exists_ideal_le_liesOver_of_lt {p} _ Q _ hlt := by
    let pl : Ideal (Localization.AtPrime <| Q.under R) := p.map (algebraMap R _)
    have : pl.IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime (Q.under R) hlt.le
    obtain ⟨⟨Pl, _⟩, hl⟩ := H Q ⟨pl, inferInstance⟩
    refine ⟨Pl.under S, ?_, Ideal.IsPrime.under S Pl, ⟨?_⟩⟩
    · exact (IsLocalization.AtPrime.orderIsoOfPrime _ Q ⟨Pl, inferInstance⟩).2.2
    · replace hl : Pl.under _ = pl := by simpa using hl
      rw [Ideal.under_under, ← Ideal.under_under (B := (Localization.AtPrime <| Q.under R)) Pl, hl,
        Ideal.under_map_of_isLocalizationAtPrime (Q.under R) hlt.le]

/-- Flat algebras satisfy the going down property. -/
@[stacks 00HS]
instance of_flat [Module.Flat R S] : Algebra.HasGoingDown R S := by
  apply of_specComap_localRingHom_surjective
  intro P hP
  have : IsLocalHom (algebraMap (Localization.AtPrime <| P.under R) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom (P.under R) P (algebraMap R S) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime (P.under R)) (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply PrimeSpectrum.specComap_surjective_of_faithfullyFlat

end Algebra.HasGoingDown
