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

section move

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem move_chain (p : LTSeries (PrimeSpectrum R)) {x : R} (hx : x ∈ p.last.1) :
    ∃ q : LTSeries (PrimeSpectrum R),
      x ∈ (q 1).1 ∧ q.length = p.length ∧ q 0 = p 0 ∧ q.last = p.last := sorry

end move

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

open RingTheory Sequence IsLocalRing Submodule Ideal Pointwise

omit [IsNoetherianRing R] in
theorem IsLocalRing.le_maximalIdeal_of_isPrime (p : Ideal R) [hp : p.IsPrime] :
    p ≤ maximalIdeal R :=
  le_maximalIdeal hp.ne_top

theorem sdqwfd (x : R) : Ideal.span {x} • ⊤ = x • (⊤ : Submodule R M) := by
  apply Submodule.ideal_span_singleton_smul


namespace Module

local notation "𝔪" => IsLocalRing.maximalIdeal R

example (a b : ℤ) (lt : ¬ a < b) (h : a ≤ b) : a = b := by
  linarith

open scoped Classical in
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  by_cases h : Subsingleton M
  · rw [(supportDim_eq_bot_iff_subsingleton R M).mpr h]
    rw [(supportDim_eq_bot_iff_subsingleton R (QuotSMulTop x M)).mpr inferInstance, WithBot.bot_add]
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
  have hm : ⟨𝔪, IsMaximal.isPrime' 𝔪⟩ ∈ support R M := maximalIdeal_mem_support R M
  refine iSup_le_iff.mpr (fun q ↦ ?_)
  let p : LTSeries (support R M) :=
    if lt : (q.last).1.1 < 𝔪 then q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt else q
  obtain ⟨hx, le⟩ : x ∈ p.last.1.1 ∧ q.length ≤ p.length := by
    by_cases lt : (q.last).1.1 < 𝔪
    · rw [show p = q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt from dif_pos lt]
      simp only [q.last_snoc, hx, RelSeries.snoc_length, le_add_iff_nonneg_right, zero_le, and_self]
    · have hq : q.last.1.1 = 𝔪 := by
        contrapose! lt
        exact lt_of_le_of_ne (le_maximalIdeal_of_isPrime q.last.1.1) lt
      simp only [show p = q from dif_neg lt, hq, hx, le_refl, and_self]
  apply (Nat.cast_le.mpr le).trans ?_
  rcases move_chain (p.map (fun a ↦ a.1) (fun ⦃_ _⦄ a ↦ a)) hx with ⟨q, hx, hq, _, _⟩
  have : (p.map (fun a ↦ a.1) (fun ⦃_ _⦄ a ↦ a)).length = p.length :=
    p.map_length (fun a ↦ a.1) (fun ⦃_ _⦄ a ↦ a)
  let q' : LTSeries (support R (QuotSMulTop x M)) := {
    length := p.length - 1
    toFun := by
      intro ⟨i, hi⟩
      refine ⟨q (i + 1), ?_⟩
      have : x • (⊤ : Submodule R M) = Ideal.span {x} • ⊤ := by
        sorry
      simp_rw [QuotSMulTop]
      have := Submodule.ideal_span_singleton_smul x (⊤ : Submodule R M)
      --simp_rw [← this, support_quotient]
      sorry
    step := sorry
  }
  calc
    (p.length : WithBot ℕ∞) ≤ (p.length - 1 + 1 : ℕ) := Nat.cast_le.mpr le_tsub_add
    _ = (p.length - (1 : ℕ) : WithBot ℕ∞) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by
      refine add_le_add_right ?_ 1
      exact le_iSup_iff.mpr fun _ h ↦ h q'

theorem supportDim_quotSMulTop_succ_eq_supportDim (x : R) (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M := sorry

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
