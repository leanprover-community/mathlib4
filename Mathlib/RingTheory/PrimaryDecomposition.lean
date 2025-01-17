/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Decomposition of Noetherian rings into direct sums of integral domains and valuation ring

A Noetherian ring where every maximal ideal is principal is a principal ideal ring, and can be
decomposed by primary ideals, leading to a direct sum of integral domains and valuation rings.

## Main results

* `IsPrincipalIdealRing.of_isNoetherian_of_isPrincipal_maximal_of_zero_divisors_mem_jacobson`

## References

* [Irving Kaplansky, *Elementary Divisors and Modules*][kaplansky1949]

-/

variable {R : Type*} [CommRing R]

local notation "JR" => (Ideal.jacobson ⊥ : Ideal R)
local notation "JB" X => (Ideal.jacobson ⊥ : Ideal X)

namespace Ideal

lemma noZeroDivisors_or_valuationRing_of_zero_divisors_mem_jacobson [IsPrincipalIdealRing R]
    (h0 : {x : R | ∃ y ≠ 0, y * x = 0} ⊆ (JR : Set R)) :
    NoZeroDivisors R ∨ (PreValuationRing R ∧ (JR).IsMaximal ∧ ∀ I : Ideal R, ∃ k, I = JR ^ k) := by
  classical
  rcases subsingleton_or_nontrivial R with _|_
  · exact Or.inl (Subsingleton.to_noZeroDivisors R)
  obtain ⟨s, hs⟩ := IsPrincipalIdealRing.principal JR
  rcases eq_or_ne s 0 with rfl|hsn
  · refine Or.inl ⟨fun h ↦ (em _).imp_right fun ha ↦ ?_⟩
    simpa [Set.singleton_zero, hs] using h0 ⟨_, ha, h⟩
  rw [submodule_span_eq] at hs
  by_cases hsu : IsUnit s
  · simp only [span_singleton_eq_top.mpr hsu, jacobson_eq_top_iff] at hs
    suffices ∀ x : R, x = 0 by simpa using this 1
    intro x
    rw [← mem_bot]
    simp [hs]
  have hs0 : ∀ x ∉ span {s}, ∀ y, y * x = 0 → y = 0 := by
    intro x hx y hy
    by_contra H
    exact hx (hs.le (h0 ⟨y, H, hy⟩))
  have : ∀ x ≠ 0, ∃ (n : ℕ) (y : R) (_ : y ∉ span {s}), x = s ^ n * y := by
    intro x hx
    by_cases hx' : x ∈ span {s}
    · replace hx' : ∃ n, x ∉ span {s ^ n} := by
        contrapose! hx
        rw [← mem_bot, ← iInf_pow_eq_bot_of_isPrincipal_of_ne_top_of_zero_divisors_le ⟨s, rfl⟩
            _ (mt span_singleton_eq_top.mp hsu)]
        · simpa [span_singleton_pow] using hx
        · simpa [hs] using h0
        · exact IsPrincipalIdealRing.principal _
      have := Nat.find_min (m := Nat.find hx' - 1) hx' (by simp)
      rw [Decidable.not_not, mem_span_singleton] at this
      obtain ⟨y, this⟩ := this
      refine ⟨_, _, ?_, this⟩
      simp only [mem_span_singleton]
      rintro ⟨z, rfl⟩
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by simp)] at this
      refine Nat.find_spec hx' ?_
      rw [mem_span_singleton]
      exact ⟨z, this⟩
    · exact ⟨0, x, hx', by simp⟩
  by_cases hN : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0
  · refine Or.inl ⟨fun h ↦ hN _ _ h⟩
  refine Or.inr ?_
  suffices ∀ (I : Ideal R), ∃ k, I = (Ideal.jacobson ⊥) ^ k by
    refine ⟨?_, ?_, this⟩
    · rw [PreValuationRing.iff_ideal_total]
      constructor
      intro I J
      obtain ⟨k, rfl⟩ := this I
      obtain ⟨l, rfl⟩ := this J
      refine (le_total k l).symm.imp ?_ ?_ <;> exact pow_le_pow_right
    · rw [isMaximal_def, isCoatom_iff_ge_of_le]
      refine ⟨by simp, fun I hI hI' ↦ ?_⟩
      obtain ⟨_|k, rfl⟩ := this I
      · simp at hI
      · exact pow_le_self (by simp)
  push_neg at hN
  have hsk : ∃ k, s ^ k = 0 := by
    obtain ⟨a, b, hab, ha0, hb0⟩ := hN
    obtain ⟨m, a', ha', rfl⟩ := this _ ha0
    obtain ⟨n, b', hb', rfl⟩ := this _ hb0
    have hab' : b' * a' ≠ 0 := by
      intro H
      refine absurd (hs0 _ ha' _ H) ?_
      rintro rfl
      simp at hb'
    obtain ⟨p, c, hc, hc'⟩ := this (b' * a') hab'
    rw [mul_right_comm, ← mul_assoc, ← pow_add, mul_assoc, hc', ← mul_assoc, ← pow_add] at hab
    exact ⟨_, hs0 _ hc _ hab⟩
  clear hN
  have hu : ∀ {a}, a ∉ span {s} → IsUnit a := by
    intro a ha
    obtain ⟨b, hb⟩ := IsPrincipalIdealRing.principal (span {a} ⊔ span {s})
    simp only [submodule_span_eq] at hb
    have hb' : b ∣ s := by
      simpa [← mem_span_singleton, ← hb] using mem_sup_right (mem_span_singleton_self _)
    rcases isUnit_or_mem_jacobson_bot_of_dvd_isNilpotent_of_zero_divisors_mem_jacobson_bot
      hsn hsk hb' hs.le h0 with hb'|hb'
    · rw [span_singleton_eq_top.mpr hb', sup_eq_top_iff_isCoprime] at hb
      obtain ⟨x, y, hb⟩ := hb
      have := mem_jacobson_bot.mp (hs ▸ mem_span_singleton_self s) (-y)
      rw [← hb] at this
      ring_nf at this
      exact (IsUnit.mul_iff.mp this).right
    · rw [hs, ← span_singleton_le_iff_mem] at hb'
      have : span {a} ≤ span {s} := by
        rw [← sup_eq_right]
        exact le_antisymm (hb.le.trans hb') le_sup_right
      exact absurd (this (mem_span_singleton_self _)) ha
  replace this : ∀ (x : R), ∃ (n : ℕ) (y : Rˣ), x = s ^ n * y := by
    intro x
    rcases eq_or_ne x 0 with rfl|hx
    · refine hsk.imp fun k hk ↦ ?_
      refine ⟨1, by simp [hk]⟩
    · obtain ⟨n, y, hy, rfl⟩ := this _ hx
      lift y to Rˣ using (hu hy)
      exact ⟨_, _, rfl⟩
  intro I
  rw [hs]
  have hk' : ∃ k, s ^ k ∈ I := by
    refine hsk.imp ?_
    simp (config := {contextual := true}) [span_singleton_pow]
  refine ⟨Nat.find hk', ?_⟩
  ext x
  constructor <;> intro hsy
  · obtain ⟨k, y, hy'⟩ := this x
    rw [hy', span_singleton_pow, mem_span_singleton]
    refine (pow_dvd_pow _ ?_).trans (dvd_mul_right _ _)
    simp only [Nat.find_le_iff]
    refine ⟨_, le_rfl, ?_⟩
    have := congr($hy' * y⁻¹)
    simp only [mul_assoc, Units.mul_inv, mul_one] at this
    rw [← this]
    exact mul_mem_right _ _ hsy
  · have := Nat.find_spec hk'
    rw [span_singleton_pow, mem_span_singleton] at hsy
    obtain ⟨y, rfl⟩ := hsy
    exact mul_mem_right _ _ this

lemma isNilpotent_of_mem_isNilpotent {x : R} {I : Ideal R} (hx : x ∈ I) (hI : IsNilpotent I) :
    IsNilpotent x := by
  refine hI.imp fun n ↦ ?_
  simp only [Submodule.zero_eq_bot, Ideal.ext_iff, mem_bot]
  intro H
  simp [← H, Ideal.pow_mem_pow hx n]

lemma isMaximal_eq_of_isNilpotent {I J : Ideal R} (hN : IsNilpotent I)
    (hI : I.IsMaximal) (hJ : J.IsMaximal) : J = I := by
  refine (hI.eq_of_le hJ.ne_top fun x hx ↦ ?_).symm
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_isNilpotent hx hN
  have hx' : x ^ n ∈ J := by simp [hn]
  exact hJ.isPrime.mem_of_pow_mem _ hx'

lemma _root_.IsNilpotent.eq_zero_of_eq_pow_two_of_ne_one {S : Type*} [Semiring S] {x : S}
    (hx : IsNilpotent x) (h : x ^ 2 = x) (h' : x ≠ 1) :
    x = 0 := by
  nontriviality S
  obtain ⟨_|k, hk⟩ := hx
  · simp at hk
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    refine ih ?_
    rwa [add_assoc, one_add_one_eq_two, pow_add, h, ← pow_succ] at hk

lemma PreValuationRing.of_isMaximal_of_isNilpotent_of_isPrincipal {M : Ideal R}
    (hM : M.IsMaximal) (hN : IsNilpotent M) (hP : M.IsPrincipal) :
    PreValuationRing R := by
  have instLocal : LocalRing R := .of_unique_max_ideal
    ⟨M, hM, fun N ↦ isMaximal_eq_of_isNilpotent hN hM⟩
  have hMu (x : R) (hx : ¬ IsUnit x) : x ∈ M := by
    simp [LocalRing.eq_maximalIdeal hM, LocalRing.mem_maximalIdeal, hx]
  obtain ⟨s, hs⟩ := hP
  rw [submodule_span_eq] at hs
  have hxs : ∀ x, ∃ (k : ℕ) (r : Rˣ), x = r * s ^ k := by
    intro x
    obtain ⟨n, hn⟩ := isNilpotent_of_mem_isNilpotent (hs ▸ mem_span_singleton_self _) hN
    rcases eq_or_ne x 0 with rfl|hx0
    · exact ⟨n, 1, by simp [hn]⟩
    by_cases hxu : IsUnit x
    · exact ⟨0, hxu.unit, by simp⟩
    classical
    have hxM : x ∈ M ^ (Nat.findGreatest (fun n ↦ x ∈ M ^ n) n) := by
      have : 1 ≤ n := by
        contrapose! hn
        simp only [Nat.lt_one_iff] at hn
        simp [hn]
      exact Nat.findGreatest_spec (P := fun n ↦ x ∈ M ^ n) this (by simpa using hMu _ hxu)
    rw [hs, span_singleton_pow] at hxM
    obtain ⟨r, hr⟩ := mem_span_singleton'.mp (hxM)
    have hru : IsUnit r := by
      by_contra H
      replace H : r ∈ span {s} := hs.le (hMu _ H)
      have H' : x ∈ span {s ^ (Nat.findGreatest (fun n ↦ x ∈ span {s} ^ n) n + 1)} := by
        rw [pow_succ', ← span_singleton_mul_span_singleton]
        have := Ideal.mul_mem_mul H
          (mem_span_singleton_self (s ^ Nat.findGreatest (fun n ↦ x ∈ span {s} ^ n) n))
        rwa [hr] at this
      rw [← span_singleton_pow, ← hs] at hxM H'
      refine Nat.findGreatest_is_greatest (P := fun n ↦ x ∈ M ^ n) (n := n) ?_ ?_ H'
      · simp
      · contrapose! H'
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt H'
        simp only [hk, add_assoc, pow_add, pow_one]
        simp [hs, span_singleton_pow, hn, hx0, Set.singleton_zero]
    exact ⟨_, hru.unit, hr.symm⟩
  rw [PreValuationRing.iff_dvd_total]
  constructor
  intro x y
  obtain ⟨k, r, rfl⟩ := hxs x
  obtain ⟨l, r', rfl⟩ := hxs y
  refine (le_total k l).imp ?_ ?_ <;>
  · intro h
    simpa using pow_dvd_pow s h

lemma eq_pow_of_isMaximal_of_isNilpotent_of_isPrincipal {M : Ideal R}
    (hM : M.IsMaximal) (hN : IsNilpotent M) (hP : M.IsPrincipal) (I : Ideal R) :
    ∃ k, I = M ^ k := by
  have instLocal : LocalRing R := .of_unique_max_ideal
    ⟨M, hM, fun N ↦ isMaximal_eq_of_isNilpotent hN hM⟩
  have hMu (x : R) (hx : ¬ IsUnit x) : x ∈ M := by
    simp [LocalRing.eq_maximalIdeal hM, LocalRing.mem_maximalIdeal, hx]
  obtain ⟨s, hs⟩ := hP
  rw [submodule_span_eq] at hs
  have hxs : ∀ x, ∃ (k : ℕ) (r : Rˣ), x = r * s ^ k := by
    intro x
    obtain ⟨n, hn⟩ := isNilpotent_of_mem_isNilpotent (hs ▸ mem_span_singleton_self _) hN
    rcases eq_or_ne x 0 with rfl|hx0
    · exact ⟨n, 1, by simp [hn]⟩
    by_cases hxu : IsUnit x
    · exact ⟨0, hxu.unit, by simp⟩
    classical
    have hxM : x ∈ M ^ (Nat.findGreatest (fun n ↦ x ∈ M ^ n) n) := by
      have : 1 ≤ n := by
        contrapose! hn
        simp only [Nat.lt_one_iff] at hn
        simp [hn]
      exact Nat.findGreatest_spec (P := fun n ↦ x ∈ M ^ n) this (by simpa using hMu _ hxu)
    rw [hs, span_singleton_pow] at hxM
    obtain ⟨r, hr⟩ := mem_span_singleton'.mp (hxM)
    have hru : IsUnit r := by
      by_contra H
      replace H : r ∈ span {s} := hs.le (hMu _ H)
      have H' : x ∈ span {s ^ (Nat.findGreatest (fun n ↦ x ∈ span {s} ^ n) n + 1)} := by
        rw [pow_succ', ← span_singleton_mul_span_singleton]
        have := Ideal.mul_mem_mul H
          (mem_span_singleton_self (s ^ Nat.findGreatest (fun n ↦ x ∈ span {s} ^ n) n))
        rwa [hr] at this
      rw [← span_singleton_pow, ← hs] at hxM H'
      refine Nat.findGreatest_is_greatest (P := fun n ↦ x ∈ M ^ n) (n := n) ?_ ?_ H'
      · simp
      · contrapose! H'
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt H'
        simp only [hk, add_assoc, pow_add, pow_one]
        simp [hs, span_singleton_pow, hn, hx0, Set.singleton_zero]
    exact ⟨_, hru.unit, hr.symm⟩
  obtain ⟨m, hm⟩ := id hN
  rcases eq_or_ne I ⊥ with rfl|hIb
  · exact ⟨m, by simp [hm]⟩
  have hIs : ∃ k, s ^ k ∈ I := by
    obtain ⟨x, hx, -⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIb
    obtain ⟨k, r, rfl⟩ := hxs x
    refine ⟨k, ?_⟩
    simpa using hx
  classical
  simp_rw [hs, span_singleton_pow]
  refine ⟨Nat.find hIs, le_antisymm ?_ ?_⟩ <;> intro x hx <;> obtain ⟨k, r, rfl⟩ := hxs x
  · simp only [Units.isUnit, unit_mul_mem_iff_mem] at hx
    simp [mem_span_singleton, pow_dvd_pow _ (Nat.find_min' hIs hx)]
  · simp only [Units.isUnit, unit_mul_mem_iff_mem, mem_span_singleton'] at hx
    obtain ⟨d, hd⟩ := hx
    simp [← hd, Ideal.mul_mem_left _ _ (Nat.find_spec hIs)]

lemma span_singleton_eq_top_of_isPrincipalIdealRing_quotient_noZeroDivisors_zero_divisors_le_aux
    {c : R} {I J : Ideal R} [IsPrincipalIdealRing (R ⧸ J)] [NoZeroDivisors (R ⧸ I)]
    (h : I ⊔ J ≤ span {c}) (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I)
    (hJ0 : ({x : R ⧸ J | ∃ y ≠ 0, y * x = 0} ⊆ (JB (R ⧸ J) : Set (R ⧸ J)))) :
    span {c} = ⊤ := by
  obtain ⟨a', haJ⟩ := IsPrincipalIdealRing.principal (Ideal.map (Ideal.Quotient.mk J) I)
  have haI' := haJ.ge (Ideal.mem_span_singleton_self _)
  simp only [submodule_span_eq] at haJ
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at haI'
  obtain ⟨a, haI, rfl⟩ := haI'
  obtain ⟨b, hb⟩ := mem_span_singleton.mp ((le_sup_left.trans h) haI)
  have hb' : b ∈ I := by
    have ha' : Quotient.mk I a = Quotient.mk I c * Quotient.mk I b := by simp [hb]
    rw [Quotient.eq_zero_iff_mem.mpr haI, eq_comm, mul_eq_zero, Quotient.eq_zero_iff_mem,
        Quotient.eq_zero_iff_mem] at ha'
    refine ha'.resolve_left fun hc ↦ ?_
    refine absurd ((h.trans ?_).trans' le_sup_right) hJI
    rwa [← span_singleton_le_iff_mem] at hc
  have ha' : Quotient.mk J a = Quotient.mk J c * Quotient.mk J b := by simp [hb]
  obtain ⟨d, hd⟩ : ∃ d, Quotient.mk J b = Quotient.mk J a * Quotient.mk J d := by
    have := haJ.le ((Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mpr
      ⟨b, hb', rfl⟩)
    rw [mem_span_singleton] at this
    obtain ⟨⟨d⟩, hd⟩ := this
    exact ⟨d, hd⟩
  rw [hd, eq_comm, ← sub_eq_zero, mul_left_comm, ← mul_sub_one] at ha'
  by_cases ha0 : Quotient.mk J a = 0
  · refine absurd ?_ hIJ
    simpa [ha0, map_eq_bot_iff_le_ker, Set.singleton_zero] using haJ
  · have := isUnit_of_sub_one_mem_jacobson_bot _ (hJ0 ⟨_, ha0, ha'⟩)
    rw [IsUnit.mul_iff] at this
    have : span {Quotient.mk J c} = ⊤ := eq_top_of_isUnit_mem _ (mem_span_singleton_self _)
      this.left
    rw [← comap_top (f := Quotient.mk J), ← this, ← Set.image_singleton, ← map_span,
      comap_map_mk]
    exact h.trans' le_sup_right

lemma eq_top_of_isPrincipalIdealRing_quotient_of_zero_divisors_le_jacobson_bot_of_disjoint_aux
    {I J M : Ideal R} (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I)
    [IsPrincipalIdealRing (R ⧸ I)] [IsPrincipalIdealRing (R ⧸ J)]
    (hI0 : {x | ∃ y ≠ 0, y * x = 0} ⊆ (JB (R ⧸ I) : Set (R ⧸ I)))
    (hJ0 : {x | ∃ y ≠ 0, y * x = 0} ⊆ (JB (R ⧸ J) : Set (R ⧸ J)))
    (hM : M.IsPrincipal) (hM' : I ⊔ J ≤ M) (hdis : Disjoint I J) :
    M = ⊤ := by
  obtain ⟨c, rfl⟩ := hM
  rw [submodule_span_eq] at hM' ⊢
  by_cases hcu : IsUnit c
  · rwa [span_singleton_eq_top]
  rcases noZeroDivisors_or_valuationRing_of_zero_divisors_mem_jacobson hI0 with _|⟨_, hmI, hvI⟩
  · exact span_singleton_eq_top_of_isPrincipalIdealRing_quotient_noZeroDivisors_zero_divisors_le_aux
      hM' hIJ hJI hJ0
  rcases noZeroDivisors_or_valuationRing_of_zero_divisors_mem_jacobson hJ0 with _|⟨_, hmJ, hvJ⟩
  · exact span_singleton_eq_top_of_isPrincipalIdealRing_quotient_noZeroDivisors_zero_divisors_le_aux
      (sup_comm I J ▸ hM') hJI hIJ hI0
  have hcI : c ∉ I := by
    rw [← span_singleton_le_iff_mem]
    contrapose! hJI
    exact hJI.trans' (hM'.trans' le_sup_right)
  set M := Ideal.comap (Quotient.mk I) (jacobson ⊥ : Ideal _) with hM
  set N := Ideal.comap (Quotient.mk J) (jacobson ⊥ : Ideal _) with hN
  obtain ⟨k, hk⟩ := hvI ⊥
  obtain ⟨l, hl⟩ := hvJ ⊥
  replace hk := congr(comap (Quotient.mk I) $hk)
  replace hl := congr(comap (Quotient.mk J) $hl)
  simp only [comap_mk_bot] at hk hl
  by_cases hMN : M = N
  · have hMn : IsNilpotent M := by
      suffices IsNilpotent (M * N) by
        rw [← hMN, ← pow_two] at this
        obtain ⟨n, hn⟩ := this
        exact ⟨2 * n, by simp [pow_mul, hn]⟩
      refine ⟨k + l, ?_⟩
      simp only [Submodule.zero_eq_bot, eq_bot_iff, hM, hN, pow_add, mul_pow]
      refine mul_le_inf.trans ((inf_le_inf ?_ ?_).trans hdis.le_bot)
      · exact mul_le_inf.trans (inf_le_of_left_le ((le_comap_pow _ _).trans hk.ge))
      · exact mul_le_inf.trans (inf_le_of_right_le ((le_comap_pow _ _).trans hl.ge))
    have hMm : IsMaximal M := by
      rw [hM]
      exact Ideal.comap_isMaximal_of_surjective _ Quotient.mk_surjective
    have instLocal : LocalRing R := .of_unique_max_ideal
      ⟨M, hMm, fun N hN ↦ isMaximal_eq_of_isNilpotent hMn hMm hN⟩
    have hMu (x : R) (hx : ¬ IsUnit x) : x ∈ M := by
      simp [LocalRing.eq_maximalIdeal hMm, LocalRing.mem_maximalIdeal, hx]
    obtain ⟨s, hs, hs'⟩ : ∃ m ∈ M, map (Quotient.mk I) M = span {Quotient.mk I m} := by
      obtain ⟨⟨m⟩, hm⟩ := IsPrincipalIdealRing.principal (Ideal.map (Quotient.mk I) M)
      rw [submodule_span_eq, Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk] at hm
      refine ⟨m, ?_, hm⟩
      · rw [hM] at hm ⊢
        rw [mem_comap]
        exact (hm.ge.trans map_comap_le) (mem_span_singleton_self _)
    have hMs : M ≤ .span {s} ⊔ I := by
      intro x hx
      rw [← Ideal.mem_quotient_iff_mem_sup]
      simp only [map_span, Set.image_singleton, ← hs', mem_quotient_iff_mem_sup]
      exact Submodule.mem_sup_left hx
    obtain ⟨x, i, hi, hc⟩ := Ideal.mem_span_singleton_sup.mp (hMs (hMu _ hcu))
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hM' (Ideal.mem_sup_left hi))
    by_cases hyu : IsUnit y
    · suffices .span {c} ≤ I from absurd ((span_singleton_le_iff_mem _).mp this) hcI
      lift y to Rˣ using hyu
      rw [eq_comm, ← Units.inv_mul_eq_iff_eq_mul] at hy
      rw [span_singleton_le_iff_mem, ← hy]
      exact Ideal.mul_mem_left _ _ hi
    · have hy1 : IsUnit (1 - y) := (isNilpotent_of_mem_isNilpotent (hMu _ hyu) hMn).isUnit_one_sub
      rw [← hy, eq_comm, ← sub_eq_iff_eq_add, mul_comm, ← mul_one_sub, ← hy1.unit_spec, eq_comm,
          ← Units.mul_inv_eq_iff_eq_mul, mul_right_comm, mul_comm] at hc
      replace hc : span {c} ≤ Ideal.span {s} := span_singleton_le_span_singleton.mpr ⟨_, hc.symm⟩
      rw [sup_eq_left.mpr (hc.trans' (hM'.trans' le_sup_left))] at hMs
      replace hMs : M = span {s} := by
        refine hMm.eq_of_le ?_ hMs
        have := hMm.ne_top
        contrapose! this
        rw [span_singleton_eq_top] at this
        rw [eq_top_of_isUnit_mem _ hs this]
      have := PreValuationRing.of_isMaximal_of_isNilpotent_of_isPrincipal hMm hMn ⟨_, hMs⟩
      rw [PreValuationRing.iff_ideal_total] at this
      have key := this.total I J
      simp [hIJ, hJI] at key
  · have : M ⊔ N = ⊤ := by
      rw [hM, hN]
      refine IsMaximal.coprime_of_ne ?_ ?_ hMN <;>
      exact comap_isMaximal_of_surjective (Quotient.mk _) Quotient.mk_surjective
    have ht := Ideal.pow_sup_pow_eq_top (m := k) (n := l) this
    refine le_antisymm le_top (hM'.trans' (ht.ge.trans (sup_le_sup ?_ ?_))) <;>
    simp [M, hk, N, hl, le_comap_pow]

lemma eq_top_of_isPrincipalIdealRing_quotient_of_zero_divisors_le_jacobson_bot_of_isPrincipal_of_le
    {I J M : Ideal R} (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I)
    [IsPrincipalIdealRing (R ⧸ I)] [IsPrincipalIdealRing (R ⧸ J)]
    (hI0 : {x | ∃ y ≠ 0, y * x = 0} ⊆ (JB (R ⧸ I) : Set (R ⧸ I)))
    (hJ0 : {x | ∃ y ≠ 0, y * x = 0} ⊆ (JB (R ⧸ J) : Set (R ⧸ J)))
    (hM : M.IsPrincipal) (hM' : I ⊔ J ≤ M) :
    M = ⊤ := by
  set f := map (Quotient.mk (I ⊓ J)) with hf
  replace hIJ : ¬ f I ≤ f J := by rwa [hf, map_le_iff_le_comap, comap_map_mk inf_le_right]
  replace hJI : ¬ f J ≤ f I := by rwa [hf, map_le_iff_le_comap, comap_map_mk inf_le_left]
  have hI : I ⊓ J ≤ I := inf_le_left
  have hJ : I ⊓ J ≤ J := inf_le_right
  have instI : IsPrincipalIdealRing ((R ⧸ I ⊓ J) ⧸ f I) :=
    IsPrincipalIdealRing.of_surjective (R := R ⧸ I)
      (DoubleQuot.quotQuotEquivQuotOfLE hI).symm (RingEquiv.surjective _)
  have instJ : IsPrincipalIdealRing ((R ⧸ I ⊓ J) ⧸ f J) :=
    IsPrincipalIdealRing.of_surjective (R := R ⧸ J)
      (DoubleQuot.quotQuotEquivQuotOfLE hJ).symm (RingEquiv.surjective _)
  replace hM : (f M).IsPrincipal := hM.map_ringHom _
  have hM'' : f I ⊔ f J ≤ f M := by
    rwa [hf, ← map_sup, map_le_iff_le_comap, comap_map_mk (inf_le_sup.trans hM')]
  replace hI0 : {x | ∃ y ≠ 0, y * x = 0} ⊆ (JB ((R ⧸ I ⊓ J) ⧸ f I) : Set ((R ⧸ I ⊓ J) ⧸ f I)) := by
    let g := (DoubleQuot.quotQuotEquivQuotOfLE hI).symm.toRingHom
    let g' := (DoubleQuot.quotQuotEquivQuotOfLE hI)
    rw [← map_bot (f := g), ← map_jacobson_of_bijective (RingEquiv.bijective _), map]
    rintro x ⟨y, hy0, hy⟩
    refine subset_span (Set.image_mono hI0 ⟨g' x, ⟨g' y, ?_, ?_⟩, ?_⟩) <;>
    simp [g, g', ← _root_.map_mul, hy, hy0]
  replace hJ0 : {x | ∃ y ≠ 0, y * x = 0} ⊆ (JB ((R ⧸ I ⊓ J) ⧸ f J) : Set ((R ⧸ I ⊓ J) ⧸ f J)) := by
    let g := (DoubleQuot.quotQuotEquivQuotOfLE hJ).symm.toRingHom
    let g' := (DoubleQuot.quotQuotEquivQuotOfLE hJ)
    rw [← map_bot (f := g), ← map_jacobson_of_bijective (RingEquiv.bijective _), map]
    rintro x ⟨y, hy0, hy⟩
    refine subset_span (Set.image_mono hJ0 ⟨g' x, ⟨g' y, ?_, ?_⟩, ?_⟩) <;>
    simp [g, g', ← _root_.map_mul, hy, hy0]
  replace hdis : Disjoint (f I) (f J) := by
    rw [hf]
    rintro K hKI hKJ ⟨x⟩ hx
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, mem_bot] at hx ⊢
    specialize hKI hx
    specialize hKJ hx
    rw [mem_quotient_iff_mem] at hKI hKJ <;>
    simp [Quotient.eq_zero_iff_mem, hKI, hKJ]
  have := eq_top_of_isPrincipalIdealRing_quotient_of_zero_divisors_le_jacobson_bot_of_disjoint_aux
      hIJ hJI hI0 hJ0 hM hM'' hdis
  rwa [hf, eq_top_iff_one, ← map_one (Quotient.mk (I ⊓ J)),
    Ideal.mem_quotient_iff_mem (inf_le_sup.trans hM'), ← eq_top_iff_one] at this

end Ideal

open Ideal in
lemma IsPrincipalIdealRing.of_isNoetherian_of_isPrincipal_maximal_of_zero_divisors_mem_jacobson
    [IsNoetherianRing R] (h : ∀ I : Ideal R, I.IsMaximal → I.IsPrincipal)
    (h0 : {x : R | ∃ y ≠ 0, y * x = 0} ⊆ JR) :
    IsPrincipalIdealRing R where
  principal I := by
    suffices ∀ a b : R, Submodule.IsPrincipal (span {a} + span {b}) by
      obtain ⟨s, rfl⟩ := IsNoetherian.noetherian I
      induction s using Finset.cons_induction_on with
      | h₁ => simpa using bot_isPrincipal
      | @h₂ x t hxt IH =>
        simp only [Finset.coe_cons, submodule_span_eq]
        obtain ⟨c, hc⟩ := IH
        simp only [submodule_span_eq] at hc
        rw [span_insert, hc, ← Ideal.add_eq_sup]
        exact this _ _
    intro a b
    suffices (∀ I : Ideal R, I.IsPrincipal → ∀ K, K.IsPrincipal → (I + K).IsPrincipal) from
      this _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
    clear a b
    intro I
    refine IsNoetherian.induction
      (P := fun I : Ideal R ↦ I.IsPrincipal → ∀ K, K.IsPrincipal → (I + K).IsPrincipal) ?_ I
    clear I
    intro I IH hI K hK
    simp only [] at IH
    rcases (le_top (a := I + K)).eq_or_lt with hab|hab
    · rw [hab]
      exact top_isPrincipal
    obtain ⟨a, rfl⟩ := hI
    obtain ⟨b, rfl⟩ := hK
    simp only [submodule_span_eq] at *
    obtain ⟨c, hc, hc'⟩ : ∃ c, IsMaximal (span {c}) ∧ (span {a} + span {b}) ≤ span {c} := by
      obtain ⟨I', hI'⟩ := exists_le_maximal _ hab.ne
      obtain ⟨c, rfl⟩ := h _ hI'.left
      exact ⟨_, hI'⟩
    obtain ⟨a', ha⟩ : ∃ a', a = c * a' := by
      rw [← dvd_def, ← mem_span_singleton]
      exact hc' (mem_sup_left (by simp [mem_span_singleton]))
    obtain ⟨b', hb⟩ : ∃ b', b = c * b' := by
      rw [← dvd_def, ← mem_span_singleton]
      exact hc' (mem_sup_right (by simp [mem_span_singleton]))
    rcases eq_or_ne a 0 with rfl|ha0
    · simpa [Set.singleton_zero] using ⟨b, rfl⟩
    have ha' : span {a} < span {a'} := by
      rw [ha]
      refine ⟨span_singleton_le_span_singleton.mpr (dvd_mul_left _ c), ?_⟩
      simp only [submodule_span_eq, SetLike.coe_subset_coe, span_singleton_le_span_singleton]
      rintro ⟨y, hy⟩
      apply hc.ne_top
      simp only [span_singleton_eq_top]
      rw [eq_comm, ← sub_eq_zero, mul_right_comm, mul_comm, ← mul_sub_one] at hy
      suffices IsUnit (c * y) from isUnit_of_mul_isUnit_left this
      apply isUnit_of_sub_one_mem_jacobson_bot
      refine h0 ⟨_, ?_, hy⟩
      rintro rfl
      exact ha0 (by simpa using ha)
    rw [ha, hb, ← span_singleton_mul_span_singleton, ← span_singleton_mul_span_singleton,
        ← mul_add]
    obtain ⟨c', hc'⟩ := IH _ ha' ⟨_, rfl⟩ _ ⟨b', rfl⟩
    simp only [submodule_span_eq] at hc'
    rw [hc', span_singleton_mul_span_singleton]
    exact ⟨_, rfl⟩
