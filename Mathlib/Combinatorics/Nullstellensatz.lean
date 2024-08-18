import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.Definitions

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
  dsimp only
  by_cases hd : d.degree ≤ (h i).totalDegree 
  · suffices coeff e ((S i).prod (fun s ↦ X i - C s)) = 0 by 
      rw [this, mul_zero]
    by_cases he : e = Finsupp.single i (e.degree)
    · suffices (S i).card < e.degree by 
        sorry
      specialize hh i
      specialize htS i

      rw [← not_le] at htS ⊢
      intro he'; apply htS

      rw [ht', ← hde] at hh
      rw [Finsupp.degree_eq_weight_one, map_add, ← Finsupp.degree_eq_weight_one] at hh
      -- , ← map_add, hde, ← Finsupp.degree_eq_weight_one, ← ht'] at hh
      have := add_le_add hd he'
      rw [Finsupp.degree_eq_weight_one, ← map_add, hde, ← Finsupp.degree_eq_weight_one, ← ht'] at this
      

      sorry
    · sorry
  · suffices coeff d (h i) = 0 by 
      rw [this, zero_mul]
    by_contra h'; apply hd
    rw [← ne_eq, ← MvPolynomial.mem_support_iff] at h'
    exact le_totalDegree h'

    
    sorry


  sorry 
end MvPolynomial
