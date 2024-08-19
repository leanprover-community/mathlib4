import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finsupp.Lex

/-! # Alon's Combinatorial Nullstellensatz -/

variable {R : Type*} [CommRing R] [IsDomain R]

theorem Polynomial.eq_zero_of_eval_zero (P : Polynomial R) (S : Set R)
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

variable {n : ℕ} 

theorem eq_zero_of_eval_zero_at_prod (P : MvPolynomial (Fin n) R) (S : Fin n → Set R)
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

noncomputable example (s : R) : Polynomial R := Polynomial.X (R := R) - Polynomial.C s 

noncomputable example (S : Finset R) : Polynomial R := 
  S.prod (fun s ↦ Polynomial.X - Polynomial.C s)

lemma prod_totalDegree_aux {ι : Type*} (i : ι) (s : Finset R) :
    (s.prod (fun r ↦ X i - C r)).totalDegree = s.card := by
  have hle (s : Finset R) : (s.prod (fun r ↦ X i - C r)).totalDegree ≤ s.card := by 
    apply le_trans (totalDegree_finset_prod s (fun r ↦ X i - C r))
    refine le_trans (s.sum_le_card_nsmul (fun r ↦ (X i - C r).totalDegree) 1 ?_) ?_
    · intro r _
      simp only
      apply le_trans (totalDegree_sub_C_le _ _)
      rw [totalDegree_X]
    · simp only [smul_eq_mul, mul_one, le_refl]
  apply le_antisymm (hle s)
  apply le_trans _ (le_totalDegree (s := Finsupp.single i s.card) ?_)
  · apply le_of_eq
    simp only [sum_single_index]
  · rw [mem_support_iff]
    convert one_ne_zero
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has hrec => 
      have hs' : (insert a s).card = s.card + 1 := by
        rw [← Finset.cons_eq_insert _ _ has, Finset.card_cons] 
      rw [Finset.prod_insert has]
      rw [coeff_mul]
      rw [Finset.sum_eq_single ⟨single i 1, single i s.card⟩]
      · simp only [hrec, mul_one]
        simp only [coeff_sub, coeff_single_X, and_self, ↓reduceIte, coeff_C, sub_eq_self,
          ite_eq_right_iff]
        intro h
        exfalso
        apply zero_ne_one (α := R)
        simp only [Finsupp.ext_iff] at h
        simpa using h i
      · rintro ⟨u, v⟩ h h'
        simp only [antidiagonal_single, Finset.mem_map, Finset.mem_antidiagonal,
          Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.exists,
          Prod.map_apply, Prod.mk.injEq] at h
        obtain ⟨k, l, hkl, hu, hv⟩ := h
        simp only [← hu, ← hv]
        by_cases hk : k = 0
        · rw [hk, zero_add, hs'] at hkl
          convert mul_zero _
          apply coeff_eq_zero_of_totalDegree_lt
          apply lt_of_le_of_lt (hle _)
          rw [Finset.sum_eq_single i]
          · simp [hkl]
          · intro b _ hb
            rw [single_apply, if_neg hb.symm]
          · simp
        · convert zero_mul _
          simp only [coeff_sub, coeff_single_X, and_true, coeff_C]
          rw [if_neg, if_neg, sub_zero]
          · intro h
            apply hk
            rw [Finsupp.ext_iff] at h
            simpa [Ne.symm hk] using h i
          · intro h
            apply h'
            simp only [← hu, ← hv, Prod.mk.injEq, congr_arg (single i) h, true_and]
            apply congr_arg
            rw [h, hs', add_comm] at hkl
            simpa using hkl
      · intro h
        simp only [antidiagonal_single, Finset.mem_map, Finset.mem_antidiagonal,
          Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.exists, Prod.map_apply,
          Prod.mk.injEq, not_exists, not_and] at h
        exfalso
        apply h 1 s.card
        · rw [hs', add_comm]
        · rfl
        · rfl
    infer_instance

#check Finset.nonempty

lemma euclDivd_aux (D : ℕ) (f : MvPolynomial (Fin n) R) (hD : f.totalDegree ≤ D) 
    (S : Fin n → Finset R) (Sne : ∀ i, (S i).nonempty) :
    ∃ (h : Fin n → MvPolynomial (Fin n) R) (r : MvPolynomial (Fin n) R),
    f = Finset.univ.sum (fun i => (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) + r ∧
    (∀ i w, (h i).weightedTotalDegree w + (S i).card * (w i) ≤ f.weightedTotalDegree w) ∧
    (∀ i, r.weightedTotalDegree (Finsupp.single i 1) < (S i).card) := by  sorry

lemma euclDivd (f : MvPolynomial (Fin n) R) (S : Fin n → Finset R) (Sne : ∀ i, (S i).nonempty) :
    ∃ (h : Fin n → MvPolynomial (Fin n) R) (r : MvPolynomial (Fin n) R),
    f = Finset.univ.sum (fun i => (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) + r ∧
    (∀ i w, (h i).weightedTotalDegree w + (S i).card * (w i) ≤ f.weightedTotalDegree w) ∧
    (∀ i, r.weightedTotalDegree (Finsupp.single i 1) < (S i).card) := 
  euclDivd_aux f.totalDegree f le_refl S Sne


theorem Alon1 (f : MvPolynomial (Fin n) R) (S : Fin n → Finset R)
    (Heval : ∀ (x : Fin n → R), (∀ i, x i ∈ S i) → eval x f = 0) : 
    ∃ (h : Fin n → MvPolynomial (Fin n) R)
      (_ : ∀ i, (h i).totalDegree + (S i).card ≤ f.totalDegree),
    f = Finset.univ.sum (fun i ↦ (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) := sorry

theorem Alon2 (f : MvPolynomial (Fin n) R) 
    (t : Fin n →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree) 
    (S : Fin n → Finset R) (htS : ∀ i, t i < (S i).card) : 
    ∃ (s : Fin n → R) (_ : ∀ i, s i ∈ S i), eval s f ≠ 0 := by 
  by_contra Heval
  apply ht
  push_neg at Heval
  obtain ⟨h, hh, hf⟩ := Alon1 f S Heval
  rw [hf, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_mul]
  rw [Finset.sum_eq_zero]
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  
  by_contra h'
  simp only [mul_eq_zero, not_or, ← ne_eq, ← mem_support_iff] at h'
  rcases h' with ⟨hd, he⟩
  suffices e = Finsupp.single i (S i).card by
    apply not_le.mpr (htS i)
    rw [← hde, Finsupp.coe_add, Pi.add_apply, this]
    simp only [Finsupp.single_eq_same, le_add_iff_nonneg_left, zero_le]
  suffices e i = (S i).card by
    ext j 
    by_cases hj : i = j
    · simp [hj.symm, this]
    · rw [single_apply, if_neg hj]
      sorry
  suffices e.degree = (S i).card by
    apply le_antisymm
    · rw [← this]
      conv_rhs => 
        rw [← Finsupp.erase_add_single i e]
      simp only [degree_eq_weight_one]
      simp only [map_add]
      suffices weight 1 (single i (e i)) = e i by 
        rw [this]
        apply le_add_of_nonneg_left
        exact Nat.zero_le ((weight 1) (erase i e))
      simp only [Finsupp.weight]
      simp
    · -- rw [← not_lt]
      -- intro H
      rw [← add_le_add_iff_left (d i)]
      rw [Finsupp.ext_iff] at hde
      specialize hde i
      simp only [coe_add, Pi.add_apply] at hde
      rw [hde]
      sorry
  apply le_antisymm
  · have := le_totalDegree he
    rw [prod_totalDegree_aux] at this
    apply le_trans _ this
    apply le_of_eq
    rfl
  · rw [← not_lt]
    intro H
    rw [← add_lt_add_iff_left d.degree, 
      degree_eq_weight_one, ← map_add, hde, ← degree_eq_weight_one] at H
    sorry
  /- This polynomial has degree (h i).totalDegree  + (S i).card ≤ t.degree
     so if coeff t _ ≠ 0, then t is a maximal monomial in _
     maximal monomials in the product :
     `d` a maximal monomial in `h i`
     (h i).totalDegree = d.degree
      maximal monomial in the product : d + single i (S i)
      at i : > t i
      This should be a contradiction
  -/

end MvPolynomial
