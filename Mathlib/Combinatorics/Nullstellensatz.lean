import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finsupp.Lex

/-! # Alon's Combinatorial Nullstellensatz -/

section LexHom 
/-! ### Lexicographic order with degree -/

variable {α : Type*}

/-- A type synonym to equip a type with its lexicographic order sorted by degrees. -/
def LexHom (α : Type*) :=
  α

/-- `toLexHom` is the identity function to the `LexHom` of a type.  -/
@[match_pattern]
def toLexHom : α ≃ LexHom α :=
  Equiv.refl _

/-- `ofLexHom` is the identity function from the `LexHom` of a type.  -/
@[match_pattern]
def ofLexHom : LexHom α ≃ α :=
  Equiv.refl _

@[simp]
theorem toLexHom_symm_eq : (@toLexHom α).symm = ofLexHom :=
  rfl

@[simp]
theorem ofLexHom_symm_eq : (@ofLexHom α).symm = toLexHom :=
  rfl

@[simp]
theorem toLexHom_ofLexHom (a : LexHom α) : toLexHom (ofLexHom a) = a :=
  rfl

@[simp]
theorem ofLexHom_toLexHom (a : α) : ofLexHom (toLexHom a) = a :=
  rfl

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem toLexHom_inj {a b : α} : toLexHom a = toLexHom b ↔ a = b :=
  Iff.rfl

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem ofLexHom_inj {a b : LexHom α} : ofLexHom a = ofLexHom b ↔ a = b :=
  Iff.rfl

/-- A recursor for `LexHom`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def LexHom.rec {β : LexHom α → Sort*} (h : ∀ a, β (toLexHom a)) :
    ∀ a, β a := fun a => h (ofLexHom a)

@[simp] lemma LexHom.forall {p : LexHom α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLexHom a) := Iff.rfl
@[simp] lemma LexHom.exists {p : LexHom α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLexHom a) := Iff.rfl

namespace Finsupp

variable {M N : Type*} [AddCommMonoid M] [CanonicallyOrderedAddCommMonoid N] 

/-- `Finsupp.LexHom r s` is the homogeneous lexicographic order on `α →₀ M`, 
where `α` is ordered by `r` and `M` is ordered by `s`.

The type synonym `LexHom (α →₀ M)` has an order given by `Finsupp.LexHom (· < ·) (· < ·)`. -/
protected def LexHom (r : α → α → Prop) (s : M → M → Prop) :
    (α →₀ M) → (α →₀ M) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))

theorem lexHom_def {r : α → α → Prop} {s : M → M → Prop} {a b : α →₀ M} :
    Finsupp.LexHom r s a b ↔ 
      Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl 

theorem LexHom.wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] (hr : WellFounded (Function.swap r)) 
    {s : M → M → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.LexHom r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.LexHom
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)

instance [LT α] [LT M] : LT (LexHom (α →₀ M)) :=
  ⟨fun f g ↦ Finsupp.LexHom (· < ·) (· < ·) (ofLexHom f) (ofLexHom g)⟩

theorem LexHom.lt_def [LT α] [LT M] {a b : LexHom (α →₀ M)} :
    a < b ↔ (toLex ((ofLexHom a).degree, toLex (ofLexHom a))) < 
        (toLex ((ofLexHom b).degree, toLex (ofLexHom b))) := 
  Iff.rfl

theorem LexHom.lt_iff [LT α] [LT M] {a b : LexHom (α →₀ M)} :
    a < b ↔ (ofLexHom a).degree < (ofLexHom b).degree ∨ 
    (((ofLexHom a).degree = (ofLexHom b).degree) ∧ toLex (ofLexHom a) < toLex (ofLexHom b)) := by
  simp only [Finsupp.LexHom.lt_def, Prod.Lex.lt_iff]

variable [LinearOrder α]

instance LexHom.isStrictOrder [PartialOrder M] :
    IsStrictOrder (LexHom (α →₀ M)) (· < ·) :=
  { irrefl := fun a ↦ by simp [LexHom.lt_def] 
    trans := by
      intro a b c hab hbc
      simp only [LexHom.lt_iff] at hab hbc ⊢
      rcases hab with (hab | hab)
      · rcases hbc with (hbc | hbc)
        · left; exact lt_trans hab hbc
        · left; exact lt_of_lt_of_eq hab hbc.1
      · rcases hbc with (hbc | hbc)
        · left; exact lt_of_eq_of_lt hab.1 hbc
        · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩ }

/-- The partial order on `Finsupp`s obtained by the homogeneous lexicographic ordering.
See `Finsupp.LexHom.linearOrder` for a proof that this partial order is in fact linear. -/
instance LexHom.partialOrder [PartialOrder M] : PartialOrder (LexHom (α →₀ M)) := 
  PartialOrder.lift 
    (fun (f : LexHom (α →₀ M)) ↦ toLex ((ofLexHom f).degree, toLex (ofLexHom f)))
    (fun f g ↦ by simp) 
   
/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance LexHom.linearOrder [LinearOrder M] : LinearOrder (LexHom (α →₀ M)) := 
  LinearOrder.lift'
    (fun (f : LexHom (α →₀ M)) ↦ toLex ((ofLexHom f).degree, toLex (ofLexHom f)))
    (fun f g ↦ by simp) 

theorem LexHom.le_iff [PartialOrder M] {x y : LexHom (α →₀ M)} :
    x ≤ y ↔ (ofLexHom x).degree < (ofLexHom y).degree ∨
      (ofLexHom x).degree = (ofLexHom y).degree ∧ toLex (ofLexHom x) ≤ toLex (ofLexHom y) := by
  simp only [le_iff_eq_or_lt, LexHom.lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y 
  · simp [h]
  · by_cases k : (ofLexHom x).degree < (ofLexHom y).degree
    · simp [k]
    · simp only [h, k, false_or]

theorem LexHom.monotone_degree [LinearOrder M] : 
    Monotone (fun (x : LexHom (α →₀ M)) ↦ (ofLexHom x).degree) := by
  intro x y 
  rw [LexHom.le_iff] 
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

instance LexHom.orderBot : OrderBot (LexHom (α →₀ N)) where
  bot := toLexHom (0 : α →₀ N)
  bot_le x := by
    simp only [LexHom.le_iff, ofLexHom_toLexHom, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofLexHom x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or, ge_iff_le]
      exact bot_le
    · simp [h]

instance LexHom.wellFoundedLT [WellFoundedGT α] [WellFoundedLT N] :
    WellFoundedLT (LexHom (α →₀ N)) := 
  ⟨LexHom.wellFounded wellFounded_gt wellFounded_lt fun n ↦ (zero_le n).not_lt⟩

end Finsupp

end LexHom

variable {R : Type*} [CommRing R] 

theorem MvPolynomial.lexHomDegree_eq_bot_iff {σ : Type*} [LinearOrder σ] {f : MvPolynomial σ R} : 
    f.support.sup toLexHom = ⊥ ↔ f.totalDegree = 0 := by
  simp only [eq_bot_iff]
  simp only [le_bot_iff, Finset.sup_eq_bot_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall₂_congr
  intro a ha
  rw [show (⊥ : LexHom (σ →₀ ℕ)) = toLexHom 0 by rfl, toLexHom_inj]
  exact Finsupp.ext_iff

theorem MvPolynomial.lexHomDegree_degree {σ : Type*} [LinearOrder σ] {f : MvPolynomial σ R} :
    (ofLexHom (f.support.sup toLexHom)).degree = f.totalDegree := by
  by_cases hf : f = 0
  · simp only [hf, support_zero, Finset.sup_empty, totalDegree_zero]
    exact Finsupp.degree_zero
  · obtain ⟨d, hd, hd'⟩ := Finset.exists_max_image _ toLexHom (support_nonempty.mpr hf)
    have hdD : toLexHom d = f.support.sup toLexHom := by 
      apply le_antisymm (Finset.le_sup hd)
      simp only [Finset.sup_le_iff]
      exact hd' 
    rw [← hdD, ofLexHom_toLexHom]
    apply le_antisymm (le_totalDegree hd)
    rw [totalDegree, Finset.sup_le_iff]
    intro c hc
    exact Finsupp.LexHom.monotone_degree (hd' c hc)

theorem Polynomial.eq_zero_of_eval_zero [IsDomain R] (P : Polynomial R) (S : Set R)
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

variable {σ : Type*} 

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

noncomputable example (s : R) : Polynomial R := Polynomial.X (R := R) - Polynomial.C s 

noncomputable example (S : Finset R) : Polynomial R := 
  S.prod (fun s ↦ Polynomial.X - Polynomial.C s)

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

lemma euclDivd_aux {n : ℕ} 
    (S : Fin n → Finset R) (Sne : ∀ i, (S i).Nonempty) 
    (D : LexHom (Fin n →₀ ℕ)) 
    (f : MvPolynomial (Fin n) R) (hfD : f.support.sup toLexHom ≤ D) :
    ∃ (h : Fin n → MvPolynomial (Fin n) R) (r : MvPolynomial (Fin n) R),
    f = Finset.univ.sum (fun i => (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) + r ∧
    (∀ i, (h i * (S i).prod (fun (s : R) ↦ (X i - C s))).totalDegree ≤ f.totalDegree) ∧
    (∀ i, r.weightedTotalDegree (Finsupp.single i 1) < (S i).card) := by 
  induction D using WellFoundedLT.induction generalizing f with
  | _ D hrecD => 
  rcases lt_or_eq_of_le hfD with (hfD | hfD)
  · apply hrecD _ hfD f (le_refl _)
  by_cases hD0 : D = ⊥
  · use fun _ ↦ 0, f
    rw [hD0, lexHomDegree_eq_bot_iff] at hfD
    simp only [hfD, zero_mul, Finset.sum_const_zero, add_zero, totalDegree_zero, le_refl,
      implies_true, true_and, zero_add]
    · intro i
      apply lt_of_le_of_lt (b := f.totalDegree)
      · rw [← weightedTotalDegree_one]
        apply weightedTotalDegree_mono
        intro j
        simp only [Pi.one_apply, single_apply]
        split_ifs <;> simp
      · simp only [hfD, Finset.card_pos, Sne i]
  -- Now, f is not constant, hence nonzero
  have hf : f ≠ 0 := fun hf ↦ hD0 (by simpa [eq_comm, hf] using hfD)
  obtain ⟨d, hd, hd'⟩ := Finset.exists_max_image _ toLexHom (support_nonempty.mpr hf)
  have hdD : toLexHom d = D := by 
    rw [← hfD]
    apply le_antisymm (Finset.le_sup hd)
    simp only [Finset.sup_le_iff]
    exact hd' 
  let f' := f - monomial d (f.coeff d)
  have hf : f = f' + monomial d (f.coeff d) := by 
    simp only [f', sub_add_cancel]
  have hf' : f'.support = f.support.erase d := by 
    ext c
    simp [f']
    split_ifs with h
    · simp [h]
    · simp [sub_zero, Ne.symm h]
  have hf'D : f'.support.sup toLexHom < D := by
    rw [Finset.sup_lt_iff]
    · intro c hc
      simp only [hf', Finset.mem_erase] at hc
      rw [← hdD, lt_iff_le_and_ne]
      exact ⟨hd' _ hc.2, fun h ↦ hc.1 (toLexHom.injective h)⟩
    · exact Ne.bot_lt' fun a ↦ hD0 a.symm
  obtain ⟨h', r', Hf', Hh', Hr'⟩ := hrecD (f'.support.sup toLexHom) hf'D f' (le_refl _)
  by_cases H : ∀ i, ofLexHom D i < (S i).card
  · -- First case, the monomial `ofLexHom D` is small, we just add it to the remainder
    use h', r' + monomial d (f.coeff d)
    constructor
    · nth_rewrite 1 [hf]
      rw [Hf', add_assoc]
    constructor
    · intro i
      apply le_trans (Hh' i)
      simp only [totalDegree]
      apply Finset.sup_mono
      simp only [hf']
      exact Finset.erase_subset d f.support
    · intro i
      apply lt_of_le_of_lt (weightedTotalDegree_add _)
      simp only [sup_lt_iff]
      refine ⟨Hr' i, ?_⟩
      apply lt_of_eq_of_lt _ (H i)
      classical
      rw [weightedTotalDegree_monomial, if_neg, weight_single_one_apply, ← hdD, ofLexHom_toLexHom]
      rwa [mem_support_iff] at hd
  · -- Second case, the monomial isn't small, we have to perform a division
    -- and argue by induction
    push_neg at H
    obtain ⟨i, hi⟩ := H
    let d' := d - single i (S i).card
    have hd' : d' + single i (S i).card = d := by
      ext j
      simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply, d']
      apply Nat.sub_add_cancel
      simp only [single_apply]
      split_ifs with h
      · apply le_of_le_of_eq hi
        rw [← h, ← hdD, ofLexHom_toLexHom]
      · exact zero_le (d j)
    -- write `monomial d (f.coeff d) = `monomial d' (f.coeff d) * _ + f''` 
    -- where `f''` is smaller
    let f'' := monomial d (f.coeff d) - monomial d' (f.coeff d) * (S i).prod (fun s ↦ X i - C s)
    have hf'' : monomial d (f.coeff d) 
      = monomial d' (f.coeff d) * (S i).prod (fun s ↦ X i - C s) + f'' := by
      simp only [f'', add_sub_cancel]
    have hf''_degree : f''.totalDegree < f.totalDegree := by
      rw [← f.lexHomDegree_degree, hfD, ← hdD, ofLexHom_toLexHom]
      simp only [totalDegree]
      rw [Finset.sup_lt_iff]
      · intro b hb
        suffices ∃ e < (S i).card, b = d' + single i e by
          obtain ⟨e, he, hb⟩ := this
          change b.degree < d.degree
          simp only [hb, ← hd', degree_eq_weight_one, map_add]
          simp only [← degree_eq_weight_one, degree_apply_single]
          exact Nat.add_lt_add_left he d'.degree
        simp only [mem_support_iff, f'', coeff_sub] at hb
        rw [coeff_monomial] at hb
        by_cases h : d = b
        · rw [if_pos h, ← h] at hb
          nth_rewrite 2 [← hd'] at hb
          rw [coeff_monomial_mul] at hb
          exfalso
          apply hb
          rw [prod_leadCoeff, mul_one, sub_self]
        · rw [if_neg h, zero_sub, ne_eq, neg_eq_zero] at hb
          rw [coeff_mul] at hb
          by_cases h' : d' ≤ b 
          · rw [Finset.sum_eq_single (d', b-d')] at hb
            · simp only [coeff_monomial, ↓reduceIte] at hb
              replace hb := right_ne_zero_of_mul hb
              rw [← mem_support_iff] at hb
              obtain ⟨e, he, he'⟩ := prod_support_le _ _ _ hb
              use e
              suffices b = d' + single i e by
                refine ⟨?_, this⟩
                apply lt_of_le_of_ne he
                intro he
                apply h
                rw [this, ← hd', he]
              rw [← he']
              ext j
              simp [Nat.add_sub_of_le (h' j)]
            · rintro ⟨u, v⟩ huv
              by_cases h : u = d'
              · intro k
                exfalso
                apply k
                simp only [Prod.mk.injEq]
                refine ⟨h, ?_⟩
                simp only [Finset.mem_antidiagonal] at huv
                rw [← huv, h, add_tsub_cancel_left]
              · intro _
                rw [coeff_monomial, if_neg (Ne.symm h), zero_mul]
            · intro k
              exfalso
              apply k
              simp only [Finset.mem_antidiagonal] 
              ext i
              simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply]
              exact Nat.add_sub_of_le (h' i)
          · exfalso
            apply hb
            rw [Finset.sum_eq_zero]
            rintro ⟨u, v⟩ huv
            simp only [Finset.mem_antidiagonal] at huv
            simp only [coeff_monomial]
            split_ifs with hu
            · exfalso
              apply h'
              rw [hu, ← huv]
              exact le_self_add
            · rw [zero_mul]
             

      · rw [← hd', degree_eq_weight_one, map_add, ← degree_eq_weight_one, degree_apply_single]
        apply lt_of_lt_of_le (b := (S i).card)
        simp only [bot_eq_zero', Finset.card_pos, Sne i]
        exact Nat.le_add_left (S i).card d'.degree
    have hf''2 : f''.support.sup toLexHom < D := by
      rw [Finsupp.LexHom.lt_iff]
      left
      rw [f''.lexHomDegree_degree, ← hfD, f.lexHomDegree_degree]
      exact hf''_degree
    obtain ⟨h'', r'', Hf'', Hh'', Hr''⟩ := hrecD _ hf''2 f'' (le_refl _)
    use h' + h'' + single i (monomial d' (f.coeff d)), r' + r''
    constructor
    · nth_rewrite 1 [hf, Hf', hf'', Hf'']
      simp only [← add_assoc]
      apply congr_arg₂ _ _ rfl
      simp only [add_assoc]
      rw [add_comm r']
      simp only [← add_assoc]
      apply congr_arg₂ _ _ rfl
      suffices monomial d' (f.coeff d) * (S i).prod (fun s ↦ X i - C s) = Finset.univ.sum
        (fun j ↦ (single i (monomial d' (f.coeff d)) j) * (S j).prod (fun s ↦ X j - C s)) by
        rw [this]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [← add_mul]
        apply congr_arg₂ _ _ rfl
        simp only [Pi.add_apply, add_assoc]
        apply congr_arg₂ _ rfl
        apply add_comm
      rw [Finset.sum_eq_single i, single_eq_same]
      · intro j _ hj
        rw [single_eq_of_ne hj.symm, zero_mul]
      · intro h 
        exfalso
        exact h (Finset.mem_univ i)
    constructor
    · intro j
      simp only [Pi.add_apply, add_mul]
      apply le_trans (totalDegree_add _ _)
      simp only [max_le_iff]
      constructor
      apply le_trans (totalDegree_add _ _)
      simp only [max_le_iff]
      constructor
      · apply le_trans (Hh' j)
        simp only [totalDegree, hf']
        exact Finset.sup_mono (Finset.erase_subset d f.support)
      · exact le_trans (Hh'' j) (le_of_lt hf''_degree)
      · simp only [single_apply]
        split_ifs with h
        · apply le_trans (totalDegree_mul _ _)
          apply le_of_le_of_eq (add_le_add (totalDegree_monomial_le _ _) (prod_totalDegree_le _ _))
          rw [← lexHomDegree_degree, hfD, ← hdD, ofLexHom_toLexHom, ← hd', ← h]
          rw [degree_eq_weight_one, map_add, ← degree_eq_weight_one, degree_apply_single]
          rfl
        · simp 
    · intro i
      apply lt_of_le_of_lt (weightedTotalDegree_add _)
      simp only [sup_lt_iff]
      exact ⟨Hr' i, Hr'' i⟩

lemma euclDivd {n : ℕ} (f : MvPolynomial (Fin n) R)
    (S : Fin n → Finset R) (Sne : ∀ i, (S i).Nonempty) :
    ∃ (h : Fin n → MvPolynomial (Fin n) R) (r : MvPolynomial (Fin n) R),
    f = Finset.univ.sum (fun i => (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) + r ∧
    (∀ i,
      (h i * (S i).prod (fun (s : R) ↦ (X i - C s))).totalDegree ≤ f.totalDegree) ∧
    (∀ i, r.weightedTotalDegree (Finsupp.single i 1) < (S i).card) := 
  euclDivd_aux S Sne _ f (le_refl _)

theorem Alon1 {n : ℕ} [IsDomain R] (S : Fin n → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial (Fin n) R) (Heval : ∀ (x : Fin n → R), (∀ i, x i ∈ S i) → eval x f = 0) : 
    ∃ (h : Fin n → MvPolynomial (Fin n) R)
      (_ : ∀ i, (h i * (S i).prod (fun s ↦ X i - C s)).totalDegree ≤ f.totalDegree),
    f = Finset.univ.sum (fun i ↦ (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) := by
  obtain ⟨h, r, hf, hh, hr⟩ := euclDivd f S Sne
  use h, hh
  simp only [hf, add_right_eq_self]
  apply eq_zero_of_eval_zero_at_prod_nat r (fun i ↦ S i) 
  · intro i
    apply lt_of_lt_of_eq (hr i)
    simp only [Set.ncard_coe_Finset]
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub]
    rw [map_sum, Finset.sum_eq_zero, neg_zero]
    intro i _
    rw [map_mul]
    convert mul_zero _
    rw [map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp only [map_sub, eval_X, eval_C, sub_self]

theorem Alon2 {n : ℕ} [IsDomain R] 
    (f : MvPolynomial (Fin n) R) 
    (t : Fin n →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree) 
    (S : Fin n → Finset R) (htS : ∀ i, t i < (S i).card) : 
    ∃ (s : Fin n → R) (_ : ∀ i, s i ∈ S i), eval s f ≠ 0 := by 
  by_contra Heval
  apply ht
  push_neg at Heval
  obtain ⟨h, hh, hf⟩ := Alon1 S 
    (fun i ↦ by rw [← Finset.card_pos]; exact lt_of_le_of_lt (zero_le _) (htS i)) 
    f Heval
  rw [hf, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_contra h'
  

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
