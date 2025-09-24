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

- `Module.supportDim_add_length_eq_supportDim_of_isRegular`: If $M$ is a finite module over a
  Noetherian local ring $R$, $r_1, \dots, r_n$ is an $M$-sequence, then
  $\dim M/(r_1, \dots, r_n)M + n = \dim M$.
-/

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

omit [IsNoetherianRing R] in
/-- If $M$ is a finite module over a commutative ring $R$, $x \in M$ is not in any minimal prime of
  $M$, then $\dim M/xM + 1 \le \dim M$. -/
theorem supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) :
    supportDim R (QuotSMulTop x M) + 1 ≤ supportDim R M := by
  nontriviality M
  nontriviality (QuotSMulTop x M)
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

lemma _root_.ringKrullDim_le_ringKrullDim_quotSMulTop_succ [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) : ringKrullDim R ≤ ringKrullDim (R ⧸ x • (⊤ : Ideal R)) + 1 := by
  rw [← Module.supportDim_self_eq_ringKrullDim, ← Module.supportDim_quotient_eq_ringKrullDim]
  exact supportDim_le_supportDim_quotSMulTop_succ hx

lemma _root_.ringKrullDim_le_ringKrullDim_add_card [IsLocalRing R] {S : Finset R}
    (hS : (S : Set R) ⊆ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span S.toSet) + S.card := by
  classical
  induction' S using Finset.induction_on with a S nmem ih
  · simp only [Finset.card_empty, CharP.cast_eq_zero, add_zero]
    apply le_of_eq
    rw [Finset.coe_empty, Ideal.span_empty]
    exact RingEquiv.ringKrullDim (RingEquiv.quotientBot R).symm
  · have sub : (S : Set R) ⊆ maximalIdeal R := fun x hx ↦ hS (Finset.mem_insert_of_mem hx)
    have : Nontrivial (R ⧸ Ideal.span S.toSet) :=
      Ideal.Quotient.nontrivial (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr sub))
    have lochom : IsLocalHom (Ideal.Quotient.mk (Ideal.span S.toSet)) :=
      IsLocalHom.of_surjective _ (Ideal.Quotient.mk_surjective)
    let _ : IsLocalRing (R ⧸ span S.toSet) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    apply le_trans (ih sub)
    simp only [Finset.card_insert_of_notMem nmem, Nat.cast_add, Nat.cast_one, add_comm _ 1,
      ← add_assoc]
    apply add_le_add_right
    let f : R ⧸ span S.toSet →+* R ⧸ span (insert a S).toSet :=
      Ideal.Quotient.factor (Ideal.span_mono (S.subset_insert a))
    have surj : Function.Surjective f := Ideal.Quotient.factor_surjective _
    have kereq : RingHom.ker f =
      (Ideal.Quotient.mk (span S.toSet) a) • (⊤ : Ideal (R ⧸ span S.toSet)) := by
      ext x
      rcases Ideal.Quotient.mk_surjective x with ⟨y, hy⟩
      simp only [← hy, RingHom.mem_ker, Quotient.factor_mk, f]
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top,
        Ideal.Quotient.eq_zero_iff_mem, ← mem_comap]
      have : span {(Ideal.Quotient.mk (span S.toSet)) a} =
        (span {a}).map (Ideal.Quotient.mk (span S.toSet)) := by simp [Ideal.map_span]
      rw [this, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        ← Ideal.span_union]
      simp
    let f' : (R ⧸ span S.toSet) ⧸ (Ideal.Quotient.mk (span S.toSet) a) •
      (⊤ : Ideal (R ⧸ span S.toSet)) →+* R ⧸ span (insert a S).toSet :=
      Ideal.Quotient.lift _ f (by simp [← kereq])
    have bij : Function.Bijective f' := by
      refine ⟨?_, Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.factor_surjective _)⟩
      rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      rcases Ideal.Quotient.mk_surjective x with ⟨y, hy⟩
      simp only [← hy, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, kereq, f'] at hx
      simpa [← hy, Ideal.Quotient.eq_zero_iff_mem] using hx
    let e : (R ⧸ span S.toSet) ⧸ (Ideal.Quotient.mk (span S.toSet) a) •
      (⊤ : Ideal (R ⧸ span S.toSet)) ≃+* R ⧸ span (insert a S).toSet :=
      RingEquiv.ofBijective f' bij
    rw [← ringKrullDim_eq_of_ringEquiv e]
    apply ringKrullDim_le_ringKrullDim_quotSMulTop_succ
    have := ((IsLocalRing.local_hom_TFAE _).out 0 4).mp lochom
    simpa [← mem_comap, this] using hS (Finset.mem_insert_self a S)

theorem supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson {x : R}
    (hn : ∀ p ∈ (annihilator R M).minimalPrimes, x ∉ p) (hx : x ∈ (annihilator R M).jacobson) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  le_antisymm (supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes hn)
    (supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson hx)

theorem supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ (annihilator R M).jacobson) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
  supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
    (fun _ ↦ reg.notMem_of_mem_minimalPrimes) hx

lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h := Submodule.ideal_span_singleton_smul x (⊤ : Ideal R)
  simp only [smul_eq_mul, mul_top] at h
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
    ← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg
    ((annihilator R R).ringJacobson_le_jacobson hx)

lemma _root_.ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
  exact supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson reg
    ((annihilator R R).ringJacobson_le_jacobson hx)

variable [IsLocalRing R]

/-- If $M$ is a finite module over a Noetherian local ring $R$, then $\dim M \le \dim M/xM + 1$
  for every $x$ in the maximal ideal of the local ring $R$. -/
@[stacks 0B52 "the second inequality"]
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 :=
  supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson ((maximalIdeal_le_jacobson _) hx)

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
