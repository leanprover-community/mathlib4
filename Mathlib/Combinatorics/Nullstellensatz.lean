/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finsupp.Lex

/-! # Alon's Combinatorial Nullstellensatz -/

open Finsupp

/- theorem Finsupp.degree_add {α N : Type*} [AddCommMonoid N] (a b : α →₀ N) :
    (a + b).degree = a.degree + b.degree := by
  change (a + b).sum (fun _ e ↦ e) = a.sum (fun _ e ↦ e) + b.sum fun _ e ↦ e
  exact sum_add_index' (congrFun rfl) fun _ b₁ ↦ congrFun rfl
-/

variable {R : Type*} [CommRing R]

theorem _root_.Polynomial.eq_zero_of_eval_zero [IsDomain R] (P : Polynomial R) (S : Set R)
    (Hdeg : Polynomial.natDegree P < S.ncard) (Heval : ∀ x ∈ S, P.eval x = 0) :
    P = 0 := by
  classical
  by_contra hP
  rw [← not_le] at Hdeg; apply Hdeg
  apply le_trans _ (Polynomial.card_roots' P)
  apply le_trans _ (Multiset.toFinset_card_le _)
  simp only [← Set.ncard_coe_Finset]
  apply Set.ncard_le_ncard
  intro s hs
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
    Polynomial.IsRoot.def]
  refine ⟨hP, Heval s hs⟩
  exact Finset.finite_toSet P.roots.toFinset

namespace MvPolynomial

open Finsupp

theorem eq_zero_of_eval_zero_at_prod_nat {n : ℕ} [IsDomain R]
    (P : MvPolynomial (Fin n) R) (S : Fin n → Set R)
    (Hdeg : ∀ i, P.weightedTotalDegree (Finsupp.single i 1) < (S i).ncard)
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
        rw [← not_le] at hd
        apply hd
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        apply le_trans _ (le_weightedTotalDegree _ hm)
        rw [Finsupp.weight_apply]
        apply le_of_eq
        rw [Finsupp.sum_eq_single 0]
        · simp
        · intro z _ hz
          rw [Finsupp.single_apply, if_neg (Ne.symm hz), smul_zero]
        · simp
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
      rw [weightedTotalDegree]
      simp only [Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      simp only [Q, finSuccEquiv_coeff_coeff, ← ne_eq, ← MvPolynomial.mem_support_iff] at he
      apply le_trans _ (le_weightedTotalDegree _ he)
      apply le_of_eq
      rw [Finsupp.weight_apply, Finsupp.sum_eq_single i, Finsupp.single_apply, if_pos rfl]
      · rw [Finsupp.weight_apply, Finsupp.sum_eq_single i.succ, Finsupp.single_apply, if_pos rfl]
        · simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one, Finsupp.cons_succ]
        · intro j _ hj
          rw [Finsupp.single_apply, if_neg (Ne.symm hj), smul_zero]
        · simp
      · intro c _ hc
        rw [Finsupp.single_apply, if_neg (Ne.symm hc), smul_zero]
      · simp
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
    (Hdeg : ∀ i, P.weightedTotalDegree (Finsupp.single i 1) < (S i).ncard)
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
    rw [weightedTotalDegree_rename_of_injective e.injective]
    congr
    ext s
    simp only [Function.comp_apply]
    nth_rewrite 1 [← e.apply_symm_apply i, Finsupp.single_apply_left e.injective]
    rfl
  · intro x hx
    simp only [MvPolynomial.eval_rename]
    apply Heval
    intro s
    simp only [Function.comp_apply]
    convert hx (e s)
    simp only [Equiv.symm_apply_apply]

variable {σ : Type*} [Fintype σ]

lemma prod_totalDegree_le {ι : Type*} (i : ι) (s : Finset R) :
    (s.prod (fun r ↦ X i - C r)).totalDegree ≤ s.card := by
  apply le_trans (totalDegree_finset_prod s (fun r ↦ X i - C r))
  refine le_trans (s.sum_le_card_nsmul (fun r ↦ (X i - C r).totalDegree) 1 ?_) ?_
  · intro r _
    simp only
    apply le_trans (totalDegree_sub_C_le _ _)
    by_cases H : Nontrivial R
    · rw [totalDegree_X]
    · apply le_of_eq_of_le _ zero_le_one
      rw [totalDegree_eq_zero_iff]
      intro m hm
      exfalso
      apply H
      simp only [mem_support_iff] at hm
      exact nontrivial_of_ne (coeff m (X i)) 0 hm
  · simp only [smul_eq_mul, mul_one, le_refl]

lemma support_monomial_mul {ι : Type*} (f : MvPolynomial ι R) (d : ι →₀ ℕ)  :
    (monomial d 1 * f).support = f.support.map (addLeftEmbedding d) := by
  ext m
  simp only [mem_support_iff, ne_eq, Finset.mem_map, addLeftEmbedding_apply]
  rw [not_iff_comm]
  push_neg
  simp_rw [not_imp_not]
  classical
  constructor
  · intro H
    rw [coeff_mul]
    let n : (ι →₀ ℕ) × (ι →₀ ℕ) := ⟨d, m - d⟩
    by_cases hn : n ∈ Finset.antidiagonal m
    · rw [Finset.sum_eq_single (d, m - d)]
      simp only [coeff_monomial, if_pos, one_mul]
      apply H
      simpa only [Finset.mem_antidiagonal] using hn
      · rintro ⟨u, v⟩ h h'
        rw [coeff_monomial, if_neg, zero_mul]
        intro k
        apply h'
        simp only [Finset.mem_antidiagonal] at h
        simp [k, ← h]
      · intro h
        simp only [coeff_monomial, ↓reduceIte, one_mul]
        exfalso
        exact h hn
    · rw [Finset.sum_eq_zero]
      rintro ⟨u, v⟩ h
      simp only [Finset.mem_antidiagonal] at h
      simp only [coeff_monomial, ite_mul, one_mul, zero_mul, ite_eq_right_iff]
      intro h'
      apply H
      rw [h', h]
  · intro H e he
    rwa [← he, coeff_monomial_mul, one_mul] at H

lemma prod_support_le {ι : Type*} (i : ι) (s : Finset R) (m : ι →₀ ℕ)
    (hm : m ∈ (s.prod (fun r ↦ X i - C r)).support) :
    ∃ e ≤ s.card, m = single i e := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, mem_support_iff, ne_eq] at hm
    use 0
    simp only [Finset.card_empty, le_refl, single_zero, true_and]
    by_contra h'
    apply hm
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm h')]
  | @insert a s has h =>
    simp only [mem_support_iff, ne_eq] at hm
    simp only [Finset.prod_insert has, sub_mul, coeff_sub, coeff_C_mul] at hm
    by_cases hm' : m ∈ (s.prod fun r ↦ X i - C r).support
    · obtain ⟨e, he, he'⟩ := h m hm'
      refine ⟨e, ?_, he'⟩
      apply le_trans he
      rw [← Finset.cons_eq_insert _ _ has, Finset.card_cons]
      exact Nat.le_add_right s.card 1
    · simp only [not_mem_support_iff] at hm'
      rw [hm', mul_zero, sub_zero, ← ne_eq, ← mem_support_iff] at hm
      simp only [support_X_mul, Finset.mem_map, addLeftEmbedding_apply] at hm
      obtain ⟨n, hn, hm⟩ := hm
      obtain ⟨p, hp, hq⟩ := h n hn
      use p + 1
      constructor
      · rw [← Finset.cons_eq_insert _ _ has, Finset.card_cons]
        exact Nat.add_le_add_right hp 1
      · rw [← hm, hq, add_comm, single_add]

lemma prod_leadCoeff {ι : Type*} (i : ι) (s : Finset R) :
    (s.prod (fun r ↦ X i - C r)).coeff (single i s.card) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has hrec =>
    rw [Finset.prod_insert has, sub_mul, coeff_sub, coeff_C_mul]
    rw [← Finset.cons_eq_insert _ _ has, Finset.card_cons, single_add, add_comm]
    rw [coeff_X_mul, hrec]
    simp only [sub_eq_self]
    convert mul_zero _
    rw [← not_mem_support_iff]
    intro h
    have h' := prod_support_le i s _ h
    obtain ⟨e, he, he'⟩ := h'
    rw [← single_add, (Finsupp.single_injective _).eq_iff] at he'
    rw [← he'] at he
    simp at he

lemma prod_totalDegree [Nontrivial R] {ι : Type*} (i : ι) (s : Finset R) :
    (s.prod (fun r ↦ X i - C r)).totalDegree = s.card := by
  apply le_antisymm (prod_totalDegree_le i s)
  apply le_of_eq_of_le _ (le_totalDegree (s := single i s.card) ?_)
  simp only [sum_single_index]
  rw [mem_support_iff, prod_leadCoeff]
  exact one_ne_zero

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
  simp only [lCoeff, m.degree_binomial i r]
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
  rw [Finset.sum_congr rfl H]
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

theorem Alon1 [IsDomain R] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R)
      (_ : ∀ i, ((S i).prod (fun s ↦ X i - C s) * (h i)).totalDegree ≤ f.totalDegree),
    f = linearCombination (MvPolynomial σ R) (fun i ↦ (S i).prod (fun r ↦ X i - C r)) h := by 
  letI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  let P (i) :  MvPolynomial σ R := (S i).prod (fun r ↦ X i - C r)
  have degP (i) : (degLex σ).degree (P i) = single i (S i).card := by 
    simp only [P]
    rw [degree_prod_of_regular]
    · simp_rw [degree_binomial]
      simp
    · intro r _
      rw [lCoeff_binomial]
      apply isRegular_one
  have lCoeffP (i) : IsUnit ((degLex σ).lCoeff (P i)) := by
    convert isUnit_one
    simp only [P]
    rw [lCoeff_prod_of_regular ?_]
    · apply Finset.prod_eq_one
      intro r _
      apply (degLex σ).lCoeff_binomial
    · intro r _
      convert isRegular_one
      apply lCoeff_binomial
  obtain ⟨h, r, hf, hh, hr⟩ := (degLex σ).monomialOrderDiv P lCoeffP f
  use h
  suffices r = 0 by
    rw [this, add_zero] at hf
    exact ⟨fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod r (fun i ↦ S i)
  · intro i
    simp only [weightedTotalDegree, Set.ncard_coe_Finset]
    rw [Finset.sup_lt_iff (by simp [Sne i])]
    intro c hc
    rw [← not_le, weight_single_one_apply]
    intro h'
    apply hr c hc i
    intro j
    rw [degP, single_apply]
    split_ifs with hj
    · rw [← hj]
      exact h'
    · exact zero_le _
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero]
    simp only [linearCombination, coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
      smul_eq_mul]
    rw [Finsupp.sum, eval_sum, Finset.sum_eq_zero]
    intro i _
    rw [map_mul]
    convert mul_zero _
    rw [map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp only [map_sub, eval_X, eval_C, sub_self]

theorem Alon2 [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree)
    (S : σ → Finset R) (htS : ∀ i, t i < (S i).card) :
    ∃ (s : σ → R) (_ : ∀ i, s i ∈ S i), eval s f ≠ 0 := by
  classical
  by_contra Heval
  apply ht
  push_neg at Heval
  obtain ⟨h, hh, hf⟩ := Alon1 S
    (fun i ↦ by rw [← Finset.card_pos]; exact lt_of_le_of_lt (zero_le _) (htS i))
    f Heval
  rw [hf] 
  simp only [linearCombination, coe_lsum, sum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
    smul_eq_mul, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  set g := h i * ((S i).prod fun r ↦ X i - C r) with hg
  by_contra ht
  have : g.totalDegree = f.totalDegree := by
    apply le_antisymm (by simp only [g, mul_comm, hh i])
    rw [ht']
    apply le_totalDegree
    rwa [mem_support_iff]
  suffices ∃ p, p + single i (S i).card = t by
    obtain ⟨p, hp⟩ := this
    apply not_le.mpr (htS i)
    simp [← hp]
  by_contra hp
  push_neg at hp
  apply ht
  rw [hg, coeff_mul, Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only [Finset.mem_antidiagonal] at hpq
  simp only [mul_eq_zero, Classical.or_iff_not_imp_right]
  rw [← ne_eq, ← mem_support_iff]
  intro hq
  obtain ⟨e, he, hq⟩ := prod_support_le _ _ _ hq
  apply coeff_eq_zero_of_totalDegree_lt
  change (h i).totalDegree < p.degree
  apply lt_of_add_lt_add_right (a := (S i).card)
  rw [hg, totalDegree_mul_eq, prod_totalDegree] at this
  · rw [this, ht', ← hpq, degree_add, add_lt_add_iff_left, ← not_le]
    intro hq'
    apply hp p
    rw [← hpq, hq]
    simp only [add_right_inj]
    apply congr_arg
    apply le_antisymm _ he
    apply le_of_le_of_eq hq'
    simp only [hq, degree_apply_single i e]
  · intro H; apply ht; simp [hg, H]
  · intro H; apply ht; simp [hg, H]

end MvPolynomial
