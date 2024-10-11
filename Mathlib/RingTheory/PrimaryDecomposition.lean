/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
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

namespace Ideal

lemma noZeroDivisors_or_valuationRing_of_zero_divisors_mem_jacobson [IsPrincipalIdealRing R]
    (h0 : {x : R | ∃ y ≠ 0, y * x = 0} ⊆ (jacobson ⊥ : Ideal R)) :
    NoZeroDivisors R ∨ (PreValuationRing R ∧
      (jacobson ⊥ : Ideal R).IsMaximal ∧ ∀ I : Ideal R, ∃ k, I = (jacobson ⊥) ^ k) := by
  classical
  rcases subsingleton_or_nontrivial R with _|_
  · exact Or.inl (Subsingleton.to_noZeroDivisors R)
  obtain ⟨s, hs⟩ := IsPrincipalIdealRing.principal (jacobson ⊥ : Ideal R)
  rcases eq_or_ne s 0 with rfl|hsn
  · refine Or.inl ⟨fun h ↦ (em _).imp_right fun ha ↦ ?_⟩
    simpa [hs] using h0 ⟨_, ha, h⟩
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

end Ideal

open Ideal in
lemma IsPrincipalIdealRing.of_isNoetherian_of_isPrincipal_maximal_of_zero_divisors_mem_jacobson
    [IsNoetherianRing R] (h : ∀ I : Ideal R, I.IsMaximal → I.IsPrincipal)
    (h0 : {x : R | ∃ y ≠ 0, y * x = 0} ⊆ (Ideal.jacobson ⊥ : Ideal R)) :
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
    · simpa using ⟨b, rfl⟩
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
