/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Lemmas about `LTSeries` in the prime spectrum

## Main results

* `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last`: Let $R$ be a Noetherian ring,
  $\mathfrak{p}_0 < \dots < \mathfrak{p}_n$ be a chain of primes, $x \in \mathfrak{p}_n$.
  Then we can find another chain of primes $\mathfrak{q}_0 < \dots < \mathfrak{q}_n$ such that
  $x \in \mathfrak{q}_1$, $\mathfrak{p}_0 = \mathfrak{q}_0$ and $\mathfrak{p}_n = \mathfrak{q}_n$.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R

open Ideal IsLocalRing

namespace PrimeSpectrum

theorem exist_mem_one_of_mem_maximal_ideal [IsLocalRing R] {p₁ p₀ : PrimeSpectrum R}
    (h₀ : p₀ < p₁) (h₁ : p₁ < closedPoint R) {x : R} (hx : x ∈ 𝔪) :
    ∃ q : PrimeSpectrum R, x ∈ q.asIdeal ∧ p₀ < q ∧ q.asIdeal < 𝔪 := by
  by_cases hn : x ∈ p₀.1
  · exact ⟨p₁, h₀.le hn, h₀, h₁⟩
  let e := p₀.1.primeSpectrumQuotientOrderIsoZeroLocus.symm
  obtain ⟨q, hq⟩ := (p₀.1 + span {x}).nonempty_minimalPrimes <|
    sup_le (IsLocalRing.le_maximalIdeal_of_isPrime p₀.1) ((span_singleton_le_iff_mem 𝔪).mpr hx)
      |>.trans_lt (IsMaximal.isPrime' 𝔪).1.lt_top |>.ne
  let q : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have : q.1.IsPrime := q.2
  have hxq : x ∈ q.1 := le_sup_right.trans hq.1.2 (mem_span_singleton_self x)
  refine ⟨q, hxq, lt_of_le_not_ge (le_sup_left.trans hq.1.2) fun h ↦ hn (h hxq), ?_⟩
  refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q.1) fun hqm ↦ ?_
  have h : (e ⟨q, le_sup_left.trans hq.1.2⟩).1.height ≤ 1 :=
    map_height_le_one_of_mem_minimalPrimes hq
  simp_rw [show q = closedPoint R from PrimeSpectrum.ext hqm] at h
  have hph : (e ⟨p₁, h₀.le⟩).1.height ≤ 0 :=
    Order.lt_one_iff_nonpos.mp (height_le_iff.mp h _ inferInstance (by simpa using h₁))
  refine ENat.not_lt_zero (e ⟨p₀, le_refl p₀⟩).1.height (height_le_iff.mp hph _ inferInstance ?_)
  simpa using h₀

theorem exist_mem_one_of_mem_two {p₁ p₀ p₂ : PrimeSpectrum R}
    (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) {x : R} (hx : x ∈ p₂.asIdeal) :
    ∃ q : (PrimeSpectrum R), x ∈ q.asIdeal ∧ p₀ < q ∧ q < p₂ := by
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime p₂.1) p₂.1
  have hm : closedPoint (Localization.AtPrime p₂.1) =
    e.symm ⟨p₂, le_refl p₂⟩ := (PrimeSpectrum.ext Localization.AtPrime.map_eq_maximalIdeal).symm
  obtain ⟨q, hxq, h₀, h₁⟩ :=
    @exist_mem_one_of_mem_maximal_ideal (Localization.AtPrime p₂.1) _ _ _
      (e.symm ⟨p₁, h₁.le⟩) (e.symm ⟨p₀, (h₀.trans h₁).le⟩) (e.symm.lt_iff_lt.mpr h₀)
        (by simp [hm, h₁]) (algebraMap R (Localization.AtPrime p₂.1) x) <| by
          rw [← Localization.AtPrime.map_eq_maximalIdeal]
          exact mem_map_of_mem (algebraMap R (Localization.AtPrime p₂.1)) hx
  rw [← e.symm_apply_apply q] at h₀ h₁ hxq
  have hq : (e q).1 < p₂ := by
    have h : e.symm (e q) < e.symm ⟨p₂, le_refl p₂⟩ :=
      h₁.trans_eq Localization.AtPrime.map_eq_maximalIdeal.symm
    rwa [OrderIso.lt_iff_lt, Subtype.mk_lt_mk] at h
  exact Exists.intro (e q).1
    ⟨(p₂.1.under_map_of_isLocalizationAtPrime hq.le).le hxq, e.symm.lt_iff_lt.mp h₀, hq⟩

/-- Let $R$ be a Noetherian ring, $\mathfrak{p}_0 < \dots < \mathfrak{p}_n$ be a
  chain of primes, $x \in \mathfrak{p}_n$. Then we can find another chain of primes
  $\mathfrak{q}_0 < \dots < \mathfrak{q}_n$ such that $x \in \mathfrak{q}_1$,
  $\mathfrak{p}_0 = \mathfrak{q}_0$ and $\mathfrak{p}_n = \mathfrak{q}_n$. -/
theorem exist_ltSeries_mem_one_of_mem_last (p : LTSeries (PrimeSpectrum R))
    {x : R} (hx : x ∈ p.last.asIdeal) : ∃ q : LTSeries (PrimeSpectrum R),
    x ∈ (q 1).asIdeal ∧ p.length = q.length ∧ p.head = q.head ∧ p.last = q.last := by
  generalize hp : p.length = n
  induction n generalizing p with
  | zero =>
    use RelSeries.singleton _ p.last
    simp only [RelSeries.singleton_toFun, hx, RelSeries.singleton_length, RelSeries.head,
      RelSeries.last_singleton, and_true, true_and]
    rw [show 0 = Fin.last p.length from Fin.zero_eq_mk.mpr hp, RelSeries.last]
  | succ n hn => ?_
  by_cases h0 : n = 0
  · use p
    have h1 : 1 = Fin.last p.length := by
      rw [Fin.last, hp, h0, zero_add]
      exact Fin.natCast_eq_mk (Nat.one_lt_succ_succ 0)
    simpa [h1, hp] using hx
  obtain ⟨q, hxq, h2, hq⟩ : ∃ q : PrimeSpectrum R, x ∈ q.1 ∧ p ⟨p.length - 2, _⟩ < q ∧ q < p.last :=
    (p ⟨p.length - 1, p.length.sub_lt_succ 1⟩).exist_mem_one_of_mem_two
      (p.strictMono (Nat.pred_lt (by simpa [hp]))) (p.strictMono (Nat.pred_lt (by simp [hp]))) hx
  obtain ⟨Q, hx, hQ, hh, hl⟩ := hn (p.eraseLast.eraseLast.snoc q h2) (by simpa using hxq) <| by
    simpa [hp] using Nat.succ_pred_eq_of_ne_zero h0
  have h1 : 1 < Q.length + 1 := Nat.lt_of_sub_ne_zero (hQ.symm.trans_ne h0)
  have h : 1 = (1 : Fin (Q.length + 1)).castSucc := by simp [Fin.one_eq_mk_of_lt h1]
  exact ⟨Q.snoc p.last (by simpa [← hl] using hq), by simpa [h], by simpa, by simp [← hh], by simp⟩

end PrimeSpectrum
