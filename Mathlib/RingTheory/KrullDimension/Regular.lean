/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Regular.RegularSequence

/-!

# Krull Dimension of quotient regular sequence

-/

section orderIso

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def primeSpectrum_quotient_orderIso_zeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R := R) I) :=
  let e : PrimeSpectrum (R ⧸ I) ≃ (PrimeSpectrum.zeroLocus (R := R) I) :=
    (Equiv.ofInjective _ (PrimeSpectrum.comap_injective_of_surjective _
      Ideal.Quotient.mk_surjective)).trans (Equiv.setCongr
      (by rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]))
  { __ := e, map_rel_iff' := fun {a b} ↦ by
        show a.asIdeal.comap _ ≤ b.asIdeal.comap _ ↔ a ≤ b
        rw [← Ideal.map_le_iff_le_comap,
          Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
          PrimeSpectrum.asIdeal_le_asIdeal] }

end orderIso

section QuotSMulTop

instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M] (N : Submodule R M) :
    Subsingleton (M ⧸ N) := by
  apply subsingleton_of_forall_eq 0
  rintro ⟨x⟩
  exact congrArg (Quot.mk ⇑N.quotientRel) (Subsingleton.eq_zero x)

end QuotSMulTop

section FiniteDimensionalOrder

open RingTheory Sequence IsLocalRing Submodule Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (x : R)
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

instance [Nontrivial M] : FiniteDimensionalOrder (Module.support R M) := by
  rw [support_eq_zeroLocus]
  have := primeSpectrum_quotient_orderIso_zeroLocus (annihilator R M)
  have : IsLocalRing (R ⧸ annihilator R M) := by
    have : annihilator R M ≤ maximalIdeal R := by
      sorry
    sorry
  have : FiniteDimensionalOrder (PrimeSpectrum (R ⧸ annihilator R M)) := inferInstance
  sorry

end FiniteDimensionalOrder

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsNoetherianRing R] in
theorem IsLocalRing.eq_maximalIdeal_of_isPrime_of_ge (p : Ideal R) [hp : p.IsPrime]
    (h : p ≥ maximalIdeal R) : p = maximalIdeal R :=
  le_antisymm (le_maximalIdeal hp.ne_top) h

namespace Module

local notation "𝔪" => IsLocalRing.maximalIdeal R

open RingTheory Sequence IsLocalRing Submodule Ideal

theorem move_chain (p : LTSeries (PrimeSpectrum R)) {x : R} (hx : x ∈ p.last.1) :
    ∃ q : LTSeries (PrimeSpectrum R),
      x ∈ (q 1).1 ∧ q.length = p.length ∧ q 0 = p 0 ∧ q.last = p.last := sorry

example (a b : ℤ) (lt : ¬ a < b) (h : a ≤ b) : a = b := by
  linarith

open scoped Classical in
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  by_cases h : Subsingleton M
  · rw [(supportDim_eq_bot_iff_subsingleton R M).mpr h]
    rw [(supportDim_eq_bot_iff_subsingleton R (QuotSMulTop x M)).mpr inferInstance, WithBot.bot_add]
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
  apply iSup_le_iff.mpr
  intro q
  have hm : ⟨𝔪, IsMaximal.isPrime' 𝔪⟩ ∈ support R M := sorry
  let p : LTSeries (support R M) :=
    if lt : (q.last).1.1 < 𝔪 then q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt
    else q
  have : x ∈ p.last.1.1 := by
    by_cases lt : (q.last).1.1 < 𝔪
    · rw [show p = q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt from dif_pos lt]
      simp only [RelSeries.last_snoc, hx]
    · rw [show p = q from dif_neg lt]
      have : q.last.1.1 = 𝔪 := by
        contrapose! lt
        have : q.last.1.1 ≤ 𝔪 := by
          apply?
        exact lt_of_le_of_ne this lt
      sorry

theorem supportDim_quotSMulTop_succ_eq_supportDim (x : R) (reg : IsSMulRegular M x)
    (mem : x ∈ maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M := sorry

theorem supportDim_regular_sequence_add_length_eq_supportDim (rs : List R)
    (reg : IsRegular M rs) :
    supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  generalize len : rs.length = n
  induction' n with n hn generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using supportDim_eq_of_equiv R _ _ (Submodule.quotEquivOfEqBot ⊥ rfl)
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isRegular_cons_iff M _ _).mp reg).1
      have mem : x ∈ maximalIdeal R := by
        simp only [mem_maximalIdeal, mem_nonunits_iff]
        by_contra isu
        absurd reg.2
        simp [Ideal.span_singleton_eq_top.mpr isu]
      rw [supportDim_eq_of_equiv R _ _ (quotOfListConsSMulTopEquivQuotSMulTopInner M x rs'),
        ← supportDim_quotSMulTop_succ_eq_supportDim x this mem,
        ← hn rs' ((isRegular_cons_iff M _ _).mp reg).2 len, add_assoc]

end Module
