/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! # Alon's Combinatorial Nullstellensatz -/

open Finsupp

variable {R : Type*} [CommRing R]

theorem _root_.Polynomial.eq_zero_of_eval_zero [IsDomain R] (P : Polynomial R) (S : Set R)
    (Hdeg : Polynomial.natDegree P < S.ncard) (Heval : ∀ x ∈ S, P.eval x = 0) :
    P = 0 := by
  classical
  by_contra hP
  apply not_le.mpr Hdeg
  apply le_trans _ (Polynomial.card_roots' P)
  apply le_trans _ (Multiset.toFinset_card_le _)
  simp only [← Set.ncard_coe_Finset]
  apply Set.ncard_le_ncard _ P.roots.toFinset.finite_toSet
  intro s hs
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
    Polynomial.IsRoot.def]
  refine ⟨hP, Heval s hs⟩

namespace MvPolynomial

open Finsupp

theorem eq_zero_of_eval_zero_at_prod_nat {n : ℕ} [IsDomain R]
    (P : MvPolynomial (Fin n) R) (S : Fin n → Set R)
    (Hdeg : ∀ i, P.degreeOf i < (S i).ncard)
    (Heval : ∀ (x : Fin n → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  induction n generalizing R with
  | zero =>
    suffices P = C (constantCoeff P) by
      specialize Heval 0 (fun i ↦ False.elim (not_lt_zero' i.prop))
      rw [eval_zero] at Heval
      rw [this, Heval, map_zero]
    ext m
    suffices m = 0 by
      rw [this]
      simp only [← constantCoeff_eq, coeff_C, ↓reduceIte]
    ext d; exfalso; exact not_lt_zero' d.prop
  | succ n hrec =>
    let Q := finSuccEquiv R n P
    suffices Q = 0 by
      simp only [Q] at this
      rw [← AlgEquiv.symm_apply_apply (finSuccEquiv R n) P, this, map_zero]
    have Heval' : ∀ (x : Fin n → R) (_ : ∀ i, x i ∈ S i.succ),
      Polynomial.map (eval x) Q = 0 := fun x hx ↦ by
      apply Polynomial.eq_zero_of_eval_zero _ (S 0)
      · apply lt_of_le_of_lt _ (Hdeg 0)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [Q]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert map_zero (MvPolynomial.eval x)
        ext m
        simp only [coeff_zero, finSuccEquiv_coeff_coeff]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        convert Finset.le_sup hm
        simp only [cons_zero]
      · intro y hy
        rw [← eval_eq_eval_mv_eval']
        apply Heval
        intro i
        induction i using Fin.inductionOn with
        | zero => simp only [Fin.cons_zero, hy]
        | succ i _ => simp only [Fin.cons_succ]; apply hx
    ext m d
    simp only [Polynomial.coeff_zero, coeff_zero]
    suffices Q.coeff m = 0 by
      simp only [this, coeff_zero]
    apply hrec _ (fun i ↦ S (i.succ))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg i.succ)
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      simp only [Q, finSuccEquiv_coeff_coeff, ← ne_eq, ← MvPolynomial.mem_support_iff] at he
      convert Finset.le_sup he
      simp only [cons_succ]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

theorem weightedTotalDegree_rename_of_injective {σ τ : Type*} [DecidableEq τ] {e : σ → τ}
    {w : τ → ℕ} {P : MvPolynomial σ R} (he : Function.Injective e) :
    weightedTotalDegree w ((rename e) P) = weightedTotalDegree (w ∘ e) P := by
  unfold weightedTotalDegree
  rw [support_rename_of_injective he, Finset.sup_image]
  congr; ext; unfold weight; simp

theorem eq_zero_of_eval_zero_at_prod {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Set R)
    (Hdeg : ∀ i, P.degreeOf i < (S i).ncard)
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  suffices MvPolynomial.rename e P = 0 by
    have that := MvPolynomial.rename_injective (R := R) e (e.injective)
    rw [RingHom.injective_iff_ker_eq_bot] at that
    rwa [← RingHom.mem_ker, that] at this
  apply eq_zero_of_eval_zero_at_prod_nat _ (fun i ↦ S (e.symm i))
  · intro i
    classical
    convert Hdeg (e.symm i)
    conv_lhs => rw [← e.apply_symm_apply i, degreeOf_rename_of_injective e.injective]
  · intro x hx
    simp only [MvPolynomial.eval_rename]
    apply Heval
    intro s
    simp only [Function.comp_apply]
    convert hx (e s)
    simp only [Equiv.symm_apply_apply]

open MonomialOrder

lemma _root_.MonomialOrder.degree_binomial [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i - C r) = single i 1 := by
  rw [degree_sub_of_lt, degree_X]
  simp only [degree_C, map_zero, degree_X]
  rw [← bot_eq_zero, bot_lt_iff_ne_bot, bot_eq_zero, ← map_zero m.toSyn]
  simp

lemma _root_.MonomialOrder.lCoeff_binomial {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.lCoeff (X i - C r) = 1 := by
  classical
  by_cases H : Nontrivial R
  · simp only [lCoeff, m.degree_binomial i r]
    simp only [coeff_sub, coeff_single_X, true_and, if_true, coeff_C, sub_eq_self]
    rw [if_neg]
    intro h
    apply zero_ne_one (α := ℕ)
    simp only [Finsupp.ext_iff, coe_zero, Pi.zero_apply] at h
    rw [h i, single_eq_same]
  · by_contra H'
    exact H (nontrivial_of_ne _ _ H')

theorem _root_.MonomialOrder.prod_degree [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (s : Finset R) :
    m.degree (s.prod (fun r ↦ X i - C r)) = single i s.card := by
  classical
  have H : ∀ r ∈ s, m.degree (X i - C r) = single i 1 := by
    intro r _
    rw [degree_sub_of_lt, degree_X]
    simp only [degree_C, map_zero, degree_X]
    rw [← bot_eq_zero, bot_lt_iff_ne_bot, bot_eq_zero, ← map_zero m.toSyn]
    simp
  rw [MonomialOrder.degree_prod_of_regular]
  · rw [Finset.sum_congr rfl H]
    simp only [Finset.sum_const, smul_single, smul_eq_mul, mul_one]
  · intro r hr
    convert isRegular_one
    simp only [lCoeff, H r hr]
    simp only [coeff_sub, coeff_single_X, true_and, if_true, coeff_C, sub_eq_self]
    rw [if_neg]
    intro h
    apply zero_ne_one (α := ℕ)
    simp only [Finsupp.ext_iff, coe_zero, Pi.zero_apply] at h
    rw [h i, single_eq_same]

variable {σ : Type*}

/-- The polynomial in `X i` that vanishes at all elements of `S`. -/
private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  S.prod (fun r ↦ X i - C r)

private theorem Alon.degP [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i S.card := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_binomial i r)]
  · intro r _
    simp only [lCoeff_binomial, isRegular_one]

private theorem Alon.lCoeffP [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.lCoeff (P S i) = 1 := by
  simp only [P]
  rw [lCoeff_prod_of_regular ?_]
  · apply Finset.prod_eq_one
    intro r _
    apply m.lCoeff_binomial
  · intro r _
    convert isRegular_one
    apply lCoeff_binomial

private lemma prod_support_le {ι : Type*} (i : ι) (s : Finset R) (m : ι →₀ ℕ)
    (hm : m ∈ (Alon.P s i).support) :
    ∃ e ≤ s.card, m = single i e := by
  classical
  have hP : Alon.P s i = MvPolynomial.rename (fun (_ : Unit) ↦ i) (Alon.P s ()) := by
    simp [Alon.P, map_prod]
  rw [hP, support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  haveI : Nontrivial R := nontrivial_of_ne _ _ he
  refine ⟨e (), ?_, ?_⟩
  · suffices e ≼[lex] single () s.card by
      simpa [lex_unit_le_iff] using this
    rw [← Alon.degP]
    apply MonomialOrder.le_degree
    rw [mem_support_iff]
    convert he
  · rw [← hm]
    ext j
    by_cases hj : j = i
    · rw [hj, mapDomain_apply (Function.injective_of_subsingleton _), single_eq_same]
    · rw [mapDomain_notin_range, single_eq_of_ne (Ne.symm hj)]
      simp [Set.range_const, Set.mem_singleton_iff, hj]

variable [Fintype σ]

theorem Alon1 [IsDomain R] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R)
      (_ : ∀ i, ((S i).prod (fun s ↦ X i - C s) * (h i)).totalDegree ≤ f.totalDegree),
    f = linearCombination (MvPolynomial σ R) (fun i ↦ (S i).prod (fun r ↦ X i - C r)) h := by
  letI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i ↦ Alon.P (S i) i)
      (fun i ↦ by simp only [Alon.lCoeffP, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this, add_zero] at hf
    exact ⟨fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod r (fun i ↦ S i)
  · intro i
    rw [degreeOf_eq_sup, Set.ncard_coe_Finset, Finset.sup_lt_iff (by simp [Sne i])]
    intro c hc
    rw [← not_le]
    intro h'
    apply hr c hc i
    intro j
    rw [Alon.degP, single_apply]
    split_ifs with hj
    · rw [← hj]
      exact h'
    · exact zero_le _
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero]
    rw [linearCombination_apply, map_finsupp_sum, Finsupp.sum, Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul, map_mul]
    convert mul_zero _
    rw [Alon.P, map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp only [map_sub, eval_X, eval_C, sub_self]

theorem Alon2 [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree)
    (S : σ → Finset R) (htS : ∀ i, t i < (S i).card) :
    ∃ (s : σ → R) (_ : ∀ i, s i ∈ S i), eval s f ≠ 0 := by
  letI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  classical
  by_contra Heval
  apply ht
  push_neg at Heval
  obtain ⟨h, hh, hf⟩ := Alon1 S
    (fun i ↦ by rw [← Finset.card_pos]; exact lt_of_le_of_lt (zero_le _) (htS i))
    f Heval
  change f = linearCombination (MvPolynomial σ R) (fun i ↦ Alon.P (S i) i) h at hf
  change ∀ i, (Alon.P (S i) i * h i).totalDegree ≤ _ at hh
  rw [hf]
  rw [linearCombination_apply, Finsupp.sum, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  set g := h i * Alon.P (S i) i with hg
  by_cases hi : h i = 0
  · simp [hi]
  have : g.totalDegree ≤ f.totalDegree := by
    simp only [hg, mul_comm, hh i]
  -- one could simplify this by proving `totalDegree_mul_eq` (at least in a domain)
  rw [hg, ← degLex_degree_degree,
    degree_mul_of_isRegular_right hi (by simp only [Alon.lCoeffP, isRegular_one]),
    Alon.degP, degree_add, degLex_degree_degree, degree_apply_single, ht'] at this
  rw [smul_eq_mul, coeff_mul, Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only [Finset.mem_antidiagonal] at hpq
  simp only [mul_eq_zero, Classical.or_iff_not_imp_right]
  rw [← ne_eq, ← mem_support_iff]
  intro hq
  obtain ⟨e, _, hq⟩ := prod_support_le _ _ _ hq
  apply coeff_eq_zero_of_totalDegree_lt
  change (h i).totalDegree < p.degree
  apply lt_of_add_lt_add_right (a := (S i).card)
  apply lt_of_le_of_lt this
  rw [← hpq, degree_add, add_lt_add_iff_left, hq, degree_apply_single]
  rw [← not_le]
  intro hq'
  apply not_le.mpr (htS i)
  apply le_trans hq'
  simp only [← hpq, hq, coe_add, Pi.add_apply, single_eq_same, le_add_iff_nonneg_left, zero_le]

end MvPolynomial
