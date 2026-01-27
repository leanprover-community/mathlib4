/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.LTSeries

/-!

# Krull Dimension of quotient regular sequence

## Main results

- `Module.supportDim_add_length_eq_supportDim_of_isRegular`: If `M` is a finite module over a
  Noetherian local ring `R`, `r₁, …, rₙ` is an `M`-sequence, then
  `dim M/(r₁, …, rₙ)M + n = dim M`.
-/

public section

namespace Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

open RingTheory Sequence IsLocalRing Ideal PrimeSpectrum Pointwise

omit [IsNoetherianRing R] [Module.Finite R M] in
lemma exists_ltSeries_support_isMaximal_last_of_ltSeries_support (q : LTSeries (support R M)) :
    ∃ p : LTSeries (support R M), q.length ≤ p.length ∧ p.last.1.1.IsMaximal := by
  obtain ⟨m, hmm, hm⟩ := exists_le_maximal _ q.last.1.2.1
  obtain hlt | rfl := lt_or_eq_of_le hm
  · use q.snoc ⟨⟨m, inferInstance⟩, mem_support_mono hm q.last.2⟩ hlt
    simpa
  · use q

theorem supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson {x : R}
    (h : x ∈ (annihilator R M).jacobson) : supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  nontriviality M
  refine iSup_le_iff.mpr (fun p ↦ ?_)
  wlog hxp : x ∈ p.last.1.1 generalizing p
  · obtain ⟨p, hle, hm⟩ := exists_ltSeries_support_isMaximal_last_of_ltSeries_support p
    have hj : (annihilator R M).jacobson ≤ p.last.1.1 :=
      sInf_le ⟨mem_support_iff_of_finite.mp p.last.2, inferInstance⟩
    exact (Nat.cast_le.mpr hle).trans <| this _ (hj h)
  -- `q` is a chain of primes such that `x ∈ q 1`, `p.length = q.length` and `p.head = q.head`.
  obtain ⟨q, hxq, hq, h0, _⟩ : ∃ q : LTSeries (PrimeSpectrum R), _ ∧ _ ∧ p.head = q.head ∧ _ :=
    exist_ltSeries_mem_one_of_mem_last (p.map Subtype.val (fun ⦃_ _⦄ lt ↦ lt)) hxp
  by_cases hp0 : p.length = 0
  · have hb : supportDim R (QuotSMulTop x M) ≠ ⊥ :=
      (supportDim_ne_bot_iff_nontrivial R (QuotSMulTop x M)).mpr <|
        Submodule.Quotient.nontrivial_iff.mpr <|
          (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator h).symm
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
  grw [le_tsub_add (b := p.length) (a := 1), Nat.cast_add_one, supportDim, Order.krullDim,
    ← le_iSup _ q']

omit [IsNoetherianRing R] in
/-- If `M` is a finite module over a commutative ring `R`, `x ∈ M` is not in any minimal prime of
  `M`, then `dim M/xM + 1 ≤ dim M`. -/
theorem supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) :
    supportDim R (QuotSMulTop x M) + 1 ≤ supportDim R M := by
  nontriviality M
  nontriviality (QuotSMulTop x M)
  have : Nonempty (Module.support R M) := nonempty_support_of_nontrivial.to_subtype
  have : Nonempty (Module.support R (QuotSMulTop x M)) := nonempty_support_of_nontrivial.to_subtype
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

theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ (annihilator R M).jacobson) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  le_antisymm (supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes hn)
    (supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson hx)

theorem supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ (annihilator R M).jacobson) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
    (fun _ ↦ reg.notMem_of_mem_minimalPrimes) hx

lemma _root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg
    ((annihilator R R).ringJacobson_le_jacobson hx)

lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h : span {x} = x • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
    ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson reg hx]

/-- If `r` is a nonzerodivisor contained in an ideal of maximal height,
`dim (R / (r)) + 1 = dim R`. -/
lemma ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R)
    {p : Ideal R} [p.IsPrime] (h : p.height = ringKrullDim R) (hp : r ∈ p) :
    ringKrullDim (R ⧸ span {r}) + 1 = ringKrullDim R := by
  refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr) (h ▸ ?_)
  exact Ideal.height_le_ringKrullDim_quotient_add_one hp

variable [IsLocalRing R]

/-- If `M` is a finite module over a Noetherian local ring `R`, then `dim M ≤ dim M/xM + 1`
  for every `x` in the maximal ideal of the local ring `R`. -/
@[stacks 0B52 "the second inequality"]
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 :=
  supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson ((maximalIdeal_le_jacobson _) hx)

lemma _root_.ringKrullDim_le_ringKrullDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ x • (⊤ : Ideal R)) + 1 := by
  rw [← Module.supportDim_self_eq_ringKrullDim, ← Module.supportDim_quotient_eq_ringKrullDim]
  exact supportDim_le_supportDim_quotSMulTop_succ hx

@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_card (since := "2026-01-12")]
lemma _root_.ringKrullDim_le_ringKrullDim_add_card {S : Finset R}
    (hS : (S : Set R) ⊆ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span (SetLike.coe S)) + S.card := by
  apply ringKrullDim_le_ringKrullDim_quotient_add_card
  rwa [IsLocalRing.ringJacobson_eq_maximalIdeal]

@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
  (since := "2026-01-12026-01-122")]
lemma _root_.ringKrullDim_le_ringKrullDim_add_spanFinrank {I : Ideal R} (h : I ≠ ⊤) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ I) + I.spanFinrank := by
  apply ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  exact le_maximalIdeal h

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
    simpa [ringJacobson_eq_maximalIdeal R]

lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
    rwa [ringJacobson_eq_maximalIdeal R]

open nonZeroDivisors in
@[stacks 00KW]
lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    {x : R} (reg : x ∈ R⁰) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (Module.Flat.isSMulRegular_of_nonZeroDivisors reg) hx

/-- If `M` is a finite module over a Noetherian local ring `R`, `r₁, …, rₙ` is an
  `M`-sequence, then `dim M/(r₁, …, rₙ)M + n = dim M`. -/
theorem supportDim_add_length_eq_supportDim_of_isRegular (rs : List R) (reg : IsRegular M rs) :
    supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  induction rs generalizing M with
  | nil =>
    rw [ofList_nil, Submodule.bot_smul]
    simpa using supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)
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
