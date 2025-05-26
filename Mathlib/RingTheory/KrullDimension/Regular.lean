/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yonele Hu
-/
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.LTSeries

/-!

# Krull Dimension of quotient regular sequence

## Main results

- `Module.supportDim_regular_sequence_add_length_eq_supportDim`: If $M$ is a finite module over a
  Noetherian local ring $R$, $r_1, \dots, r_n$ is an $M$-sequence, then
  $\dim M/(r_1, \dots, r_n)M + n = \dim M$.
-/

namespace Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "𝔪" => IsLocalRing.maximalIdeal R

open RingTheory Sequence IsLocalRing Ideal PrimeSpectrum

open scoped Classical in
/-- If $M$ is a finite module over a Noetherian local ring $R$, then $\dim M \le \dim M/xM + 1$
  for all $x$ in the maximal ideal of the local ring $R$. -/
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  rcases subsingleton_or_nontrivial M with h | h
  · rw [(supportDim_eq_bot_iff_subsingleton R M).mpr h]
    rw [(supportDim_eq_bot_iff_subsingleton R (QuotSMulTop x M)).mpr inferInstance, WithBot.bot_add]
  have hm : ⟨𝔪, IsMaximal.isPrime' 𝔪⟩ ∈ support R M := maximalIdeal_mem_support R M
  refine iSup_le_iff.mpr (fun q ↦ ?_)
  let p : LTSeries (support R M) :=
    if lt : (q.last).1.1 < 𝔪 then q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt else q
  obtain ⟨hxp, le⟩ : x ∈ p.last.1.1 ∧ q.length ≤ p.length := by
    by_cases lt : (q.last).1.1 < 𝔪
    · rw [show p = q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt from dif_pos lt]
      simp only [q.last_snoc, hx, RelSeries.snoc_length, le_add_iff_nonneg_right, zero_le, and_self]
    · have hq : q.last.1.1 = 𝔪 := by
        contrapose! lt
        exact lt_of_le_of_ne (le_maximalIdeal_of_isPrime q.last.1.1) lt
      simp only [show p = q from dif_neg lt, hq, hx, le_refl, and_self]
  obtain ⟨q, hxq, hq, h0, _⟩ := PrimeSpectrum.exist_lTSeries_mem_one_of_mem_last
    (p.map (fun a ↦ a.1) (fun ⦃_ _⦄ a ↦ a)) hxp
  refine (Nat.cast_le.mpr le).trans ?_
  by_cases h : p.length = 0
  · have hb : supportDim R (QuotSMulTop x M) ≠ ⊥ :=
      (supportDim_ne_bot_iff_nontrivial R (QuotSMulTop x M)).mpr <|
        nontrivial_quotSMulTop_of_mem_annihilator_jacobson (maximalIdeal_le_jacobson _ hx)
    rw [h, ← WithBot.coe_unbot (supportDim R (QuotSMulTop x M)) hb]
    exact WithBot.coe_le_coe.mpr (zero_le ((supportDim R (QuotSMulTop x M)).unbot hb + 1))
  let q' : LTSeries (support R (QuotSMulTop x M)) := {
    length := p.length - 1
    toFun := by
      intro ⟨i, hi⟩
      have hi : i + 1 < q.length + 1 :=
        Nat.succ_lt_succ (hi.trans_eq ((Nat.sub_add_cancel (Nat.pos_of_ne_zero h)).trans hq))
      refine ⟨q ⟨i + 1, hi⟩, ?_⟩
      simp only [support_quotSMulTop, Set.mem_inter_iff, mem_zeroLocus, Set.singleton_subset_iff]
      refine ⟨?_, q.monotone
        ((Fin.natCast_eq_mk (Nat.lt_of_add_left_lt hi)).trans_le (Nat.le_add_left 1 i)) hxq⟩
      have hp : p.head.1 ∈ support R M := p.head.2
      simp only [support_eq_zeroLocus, mem_zeroLocus, SetLike.coe_subset_coe] at hp ⊢
      exact hp.trans (h0.trans_le (q.head_le _))
    step := fun ⟨i, _⟩ ↦ q.strictMono (i + 1).lt_add_one
  }
  calc
    (p.length : WithBot ℕ∞) ≤ (p.length - 1 + 1 : ℕ) := Nat.cast_le.mpr le_tsub_add
    _ = (p.length - (1 : ℕ) : WithBot ℕ∞) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by
      refine add_le_add_right ?_ 1
      exact le_iSup_iff.mpr fun _ h ↦ h q'

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- If $M$ is a finite module over a comm ring $R$, then $\dim M/xM + 1 \le \dim M$
  for all $M$-regular element $x$. -/
theorem supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) :
    supportDim R (QuotSMulTop x M) + 1 ≤ supportDim R M := by
  rcases subsingleton_or_nontrivial M with h | _
  · rw [(supportDim_eq_bot_iff_subsingleton R M).mpr h]
    rw [(supportDim_eq_bot_iff_subsingleton R (QuotSMulTop x M)).mpr inferInstance, WithBot.bot_add]
  rcases subsingleton_or_nontrivial (QuotSMulTop x M) with h | _
  · simp [(supportDim_eq_bot_iff_subsingleton R (QuotSMulTop x M)).mpr h]
  simp only [supportDim, Order.krullDim_eq_iSup_length]
  apply WithBot.coe_le_coe.mpr
  simp only [ENat.iSup_add, iSup_le_iff]
  intro p
  let q : LTSeries (support R M) := {
    length := p.length
    toFun := by
      intro i
      have hq := (p i).2
      simp only [support_quotSMulTop, Set.mem_inter_iff] at hq
      exact ⟨(p i).1, hq.1⟩
    step := by
      intro i
      simp only [Subtype.mk_lt_mk, Subtype.coe_lt_coe, p.3 i]
  }
  have hx : x ∈ q.head.1.1 := by
    have hp := p.head.2
    simp only [support_quotSMulTop, Set.mem_inter_iff, mem_zeroLocus, Set.singleton_subset_iff,
      SetLike.mem_coe] at hp
    exact hp.2
  have hq := q.head.2
  simp only [support_eq_zeroLocus, mem_zeroLocus, SetLike.coe_subset_coe] at hq
  rcases Ideal.exists_minimalPrimes_le hq with ⟨r, hrm, hr⟩
  let r : support R M := ⟨⟨r, minimalPrimes_isPrime hrm⟩, mem_support_iff_of_finite.mpr hrm.1.2⟩
  have hr : r < q.head := lt_of_le_of_ne hr (fun h ↦ hn q.head.1.1 (by rwa [← h]) hx)
  exact le_of_eq_of_le (by simpa only [q.cons_length] using by rfl) (le_iSup _ (q.cons r hr))

theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ maximalIdeal R) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  le_antisymm (supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes hn)
    (supportDim_le_supportDim_quotSMulTop_succ hx)

theorem supportDim_quotSMulTop_succ_eq_supportDim {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (fun _ ↦ notMem_minimalPrimes_of_isSMulRegular reg) hx

/-- If $M$ is a finite module over a Noetherian local ring $R$, $r_1, \dots, r_n$ is an
  $M$-sequence, then $\dim M/(r_1, \dots, r_n)M + n = \dim M$. -/
theorem supportDim_regular_sequence_add_length_eq_supportDim (rs : List R)
    (reg : IsRegular M rs) :
    supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  generalize len : rs.length = n
  induction' n with n hn generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)
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
      rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x _),
        ← supportDim_quotSMulTop_succ_eq_supportDim this mem,
        ← hn rs' ((isRegular_cons_iff M _ _).mp reg).2 len, add_assoc]

end Module
