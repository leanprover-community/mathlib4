/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
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

open RingTheory Sequence IsLocalRing Ideal PrimeSpectrum Pointwise

omit [IsLocalRing R] in
theorem supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson {x : R}
    (h : x ∈ (annihilator R M).jacobson) : supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  nontriviality M
  refine iSup_le_iff.mpr (fun q ↦ ?_)
  obtain ⟨m, hmm, hm⟩ := exists_le_maximal _ q.last.1.2.1
  have hj : (annihilator R M).jacobson ≤ m :=
    sInf_le ⟨(mem_support_iff_of_finite.mp q.last.2).trans hm, hmm⟩
  -- Append `m` to `q`.
  classical let p : LTSeries (support R M) :=
    if hq : q.last.1.1 < m then q.snoc ⟨⟨m, inferInstance⟩, mem_support_mono hm q.last.2⟩ hq else q
  obtain ⟨hxp, le⟩ : x ∈ p.last.1.1 ∧ q.length ≤ p.length := by
    by_cases lt : q.last.1.1 < m
    · simpa [show p = q.snoc ⟨⟨m, _⟩, _⟩ lt from dif_pos lt] using hj h
    · have hq : q.last.1.1 = m := by
        contrapose! lt
        exact lt_of_le_of_ne hm lt
      simpa [show p = q from dif_neg lt, hq] using hj h
  -- `q` is a chain of primes such that `x ∈ q 1`, `p.length = q.length` and `p.head = q.head`.
  obtain ⟨q, hxq, hq, h0, _⟩ : ∃ q : LTSeries (PrimeSpectrum R), _ ∧ _ ∧ p.head = q.head ∧ _ :=
    exist_ltSeries_mem_one_of_mem_last (p.map Subtype.val (fun ⦃_ _⦄ lt ↦ lt)) hxp
  refine (Nat.cast_le.mpr le).trans ?_
  by_cases hp0 : p.length = 0
  · have hb : supportDim R (QuotSMulTop x M) ≠ ⊥ :=
      (supportDim_ne_bot_iff_nontrivial R (QuotSMulTop x M)).mpr <|
        nontrivial_quotSMulTop_of_mem_annihilator_jacobson h
    rw [hp0, ← WithBot.coe_unbot (supportDim R (QuotSMulTop x M)) hb]
    exact WithBot.coe_le_coe.mpr (zero_le ((supportDim R (QuotSMulTop x M)).unbot hb + 1))
  -- Let `q' i := q (i + 1)`, then `q'` is a chain of prime ideals in `Supp(M/xM)`.
  let q' : LTSeries (support R (QuotSMulTop x M)) := {
    length := p.length - 1
    toFun := by
      intro ⟨i, hi⟩
      have hi : i + 1 < q.length + 1 :=
        Nat.succ_lt_succ (hi.trans_eq ((Nat.sub_add_cancel (Nat.pos_of_ne_zero hp0)).trans hq))
      exact ⟨q ⟨i + 1, hi⟩, by simpa using
        ⟨mem_support_mono (by simpa [h0] using q.monotone (Fin.zero_le _)) p.head.2, q.monotone
          ((Fin.natCast_eq_mk (Nat.lt_of_add_left_lt hi)).trans_le (Nat.le_add_left 1 i)) hxq⟩⟩
    step := by exact fun _ ↦ q.strictMono (by simp)
  }
  calc (p.length : WithBot ℕ∞) ≤ (p.length - 1 + 1 : ℕ) := Nat.cast_le.mpr le_tsub_add
    _ ≤ _ := by simpa using add_le_add_right (by exact le_iSup_iff.mpr fun _ h ↦ h q') 1

/-- If $M$ is a finite module over a Noetherian local ring $R$, then $\dim M \le \dim M/xM + 1$
  for every $x$ in the maximal ideal of the local ring $R$. -/
@[stacks 0B52 "the second inequality"]
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 :=
  supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson ((maximalIdeal_le_jacobson _) hx)

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- If $M$ is a finite module over a commutative ring $R$, $x \in M$ is not in any minimal prime of
  $M$, then $\dim M/xM + 1 \le \dim M$. -/
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
  have hp := p.head.2
  simp only [support_quotSMulTop, Set.mem_inter_iff, mem_zeroLocus, Set.singleton_subset_iff] at hp
  have le : support R (QuotSMulTop x M) ⊆ support R M := by simp
  -- Since `Supp(M/xM) ⊆ Supp M`, `p` can be viewed as a chain of prime ideals in `Supp M`,
  -- which we denote by `q`.
  let q : LTSeries (support R M) :=
    p.map (Set.MapsTo.restrict id (support R (QuotSMulTop x M)) (support R M) le) (fun _ _ h ↦ h)
  obtain ⟨r, hrm, hr⟩ := exists_minimalPrimes_le (mem_support_iff_of_finite.mp q.head.2)
  let r : support R M := ⟨⟨r, minimalPrimes_isPrime hrm⟩, mem_support_iff_of_finite.mpr hrm.1.2⟩
  have hr : r < q.head := lt_of_le_of_ne hr (fun h ↦ hn q.head.1.1 (by rwa [← h]) hp.2)
  exact le_of_eq_of_le (by simp [q]) (le_iSup _ (q.cons r hr))

omit [IsLocalRing R] in
theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ (annihilator R M).jacobson) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  le_antisymm (supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes hn)
    (supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson hx)

omit [IsLocalRing R] in
theorem supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ (annihilator R M).jacobson) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
    (fun _ ↦ reg.notMem_of_mem_minimalPrimes) hx

omit [IsLocalRing R] in
lemma _root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg
    ((annihilator R R).ringJacobson_le_jacobson hx)

omit [IsLocalRing R] in
lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h := Submodule.ideal_span_singleton_smul x (⊤ : Ideal R)
  simp only [smul_eq_mul, mul_top] at h
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
    ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson reg hx]

@[stacks 0B52 "the equality case"]
theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ maximalIdeal R) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson hn <|
    (maximalIdeal_le_jacobson _) hx

theorem supportDim_quotSMulTop_succ_eq_supportDim {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg ((maximalIdeal_le_jacobson _) hx)

lemma _root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim {x : R} (reg : IsSMulRegular R x)
    (hx : x ∈ maximalIdeal R) : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
  ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
    rwa [ringJacobson_eq_maximalIdeal R]

@[stacks 00KW]
lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
    rwa [ringJacobson_eq_maximalIdeal R]

/-- If $M$ is a finite module over a Noetherian local ring $R$, $r_1, \dots, r_n$ is an
  $M$-sequence, then $\dim M/(r_1, \dots, r_n)M + n = \dim M$. -/
theorem supportDim_add_length_eq_supportDim_of_isRegular (rs : List R) (reg : IsRegular M rs) :
    supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  induction rs generalizing M with
  | nil =>
    rw [ofList_nil, Submodule.bot_smul]
    simpa  using supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)
  | cons x rs' ih =>
    have mem : x ∈ maximalIdeal R := by
      simpa using fun isu ↦ reg.2 (by simp [span_singleton_eq_top.mpr isu])
    simp [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x _),
      ← supportDim_quotSMulTop_succ_eq_supportDim ((isRegular_cons_iff M _ _).mp reg).1 mem,
      ← ih ((isRegular_cons_iff M _ _).mp reg).2, ← add_assoc]

lemma _root_.ringKrullDim_add_length_eq_ringKrullDim_of_isRegular (rs : List R)
    (reg : IsRegular R rs) : ringKrullDim (R ⧸ ofList rs) + rs.length = ringKrullDim R := by
  have eq : ofList rs = ofList rs • (⊤ : Ideal R) := by simp
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R eq).toRingEquiv,
    ← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_add_length_eq_supportDim_of_isRegular rs reg

end Module
