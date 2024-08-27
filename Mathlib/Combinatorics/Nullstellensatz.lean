import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finsupp.Lex

/-! # Alon's Combinatorial Nullstellensatz -/

open Finsupp 

theorem Finsupp.degree_add {α N : Type*} [AddCommMonoid N] (a b : α →₀ N) :
    (a + b).degree = a.degree + b.degree := by
  change (a + b).sum (fun _ e ↦ e) = a.sum (fun _ e ↦ e) + b.sum fun _ e ↦ e
  exact sum_add_index' (congrFun rfl) fun _ b₁ ↦ congrFun rfl
  
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

noncomputable instance : AddCommMonoid (LexHom (α →₀ M)) := ofLexHom.addCommMonoid

theorem toLexHom_add (a b : α →₀ M) : toLexHom (a + b) = toLexHom a + toLexHom b := rfl

theorem ofLexHom_add (a b : LexHom (α →₀ M)) : ofLexHom (a + b) = ofLexHom a + ofLexHom b := rfl

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

theorem LexHom.le_iff [PartialOrder M] {x y : LexHom (α →₀ M)} :
    x ≤ y ↔ (ofLexHom x).degree < (ofLexHom y).degree ∨
      (ofLexHom x).degree = (ofLexHom y).degree ∧ toLex (ofLexHom x) ≤ toLex (ofLexHom y) := by
  simp only [le_iff_eq_or_lt, LexHom.lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y 
  · simp [h]
  · by_cases k : (ofLexHom x).degree < (ofLexHom y).degree
    · simp [k]
    · simp only [h, k, false_or]

noncomputable instance {M : Type*} [OrderedCancelAddCommMonoid M] :
    OrderedCancelAddCommMonoid (LexHom (α →₀ M)) where
  toAddCommMonoid := ofLexHom.addCommMonoid
  toPartialOrder := LexHom.partialOrder
  le_of_add_le_add_left a b c h := by
    rw [LexHom.le_iff] at h ⊢
    simpa only [ofLexHom_add, degree_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [LexHom.le_iff] at h ⊢
    simpa [ofLexHom_add, degree_add] using h
  
/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance LexHom.linearOrder [LinearOrder M] : LinearOrder (LexHom (α →₀ M)) := 
  LinearOrder.lift'
    (fun (f : LexHom (α →₀ M)) ↦ toLex ((ofLexHom f).degree, toLex (ofLexHom f)))
    (fun f g ↦ by simp) 

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
noncomputable instance {M : Type*} [LinearOrderedCancelAddCommMonoid M] :
    LinearOrderedCancelAddCommMonoid (LexHom (α →₀ M)) where 
  toOrderedCancelAddCommMonoid := inferInstance
  le_total := LexHom.linearOrder.le_total
  decidableLE := LexHom.linearOrder.decidableLE
  min_def := LexHom.linearOrder.min_def
  max_def := LexHom.linearOrder.max_def
  compare_eq_compareOfLessAndEq := LexHom.linearOrder.compare_eq_compareOfLessAndEq

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

section LexHomDegree

namespace MvPolynomial

variable {σ : Type*} [LinearOrder σ] {R : Type*} [CommSemiring R] 

/-- the homogeneous lexicographic order of a multivariate polynomial -/
def lexHomDegree (f : MvPolynomial σ R) := f.support.sup toLexHom

theorem lexHom_induction [WellFoundedGT σ] {motive : MvPolynomial σ R → Prop}
    (hrec : ∀ (f : MvPolynomial σ R)
      (_ : ∀ (g : MvPolynomial σ R) (_ : g.lexHomDegree < f.lexHomDegree), motive g), motive f)
    (f : MvPolynomial σ R) :
    motive f := by
  suffices ∀ d, ∀ f : MvPolynomial σ R, f.lexHomDegree = d → motive f by
    apply this f.lexHomDegree f rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d hrecd =>
  intro f hf
  apply hrec
  intro g
  rw [hf]
  exact fun hg ↦ hrecd _ hg g rfl
  
@[simp]
theorem lexHomDegree_zero : lexHomDegree (0 : MvPolynomial σ R) = ⊥ := rfl

theorem lexHomDegree_le_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} :
    f.lexHomDegree ≤ toLexHom d ↔ ∀ c ∈ f.support, toLexHom c ≤ toLexHom d := by
  simp only [lexHomDegree, Finset.sup_le_iff]

theorem le_lexHomDegree {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    toLexHom d ≤ f.lexHomDegree := by
  simp only [lexHomDegree]
  exact Finset.le_sup hd

theorem coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : f.lexHomDegree < toLexHom d) :
    f.coeff d = 0 := by
  rw [← not_mem_support_iff]
  exact fun h ↦ not_le.mpr hd (le_lexHomDegree h)

theorem eq_lexHomDegree_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hf : f ≠ 0) : 
    f.lexHomDegree = toLexHom d ↔ d ∈ f.support ∧ (∀ c ∈ f.support, toLexHom c ≤ toLexHom d) := by 
  obtain ⟨D, hD, hD'⟩ := Finset.exists_max_image _ toLexHom (support_nonempty.mpr hf)
  have hdD : f.lexHomDegree = toLexHom D := le_antisymm (Finset.sup_le hD') (Finset.le_sup hD)
  rw [le_antisymm_iff, lexHomDegree_le_iff, and_comm, and_congr_left_iff]
  intro H
  refine ⟨?_, le_lexHomDegree⟩
  intro h
  convert hD
  rw [← toLexHom_inj]
  apply le_antisymm (hdD.symm ▸ h) (H _ hD)

theorem lexHomDegree_spec {f : MvPolynomial σ R} (hf : f ≠ 0) :
    ofLexHom f.lexHomDegree ∈ f.support ∧ (∀ c ∈ f.support, toLexHom c ≤ f.lexHomDegree) := 
  (eq_lexHomDegree_iff (d := f.lexHomDegree) hf).1 rfl

theorem lexHomDegree_degree {f : MvPolynomial σ R} :
    (ofLexHom f.lexHomDegree).degree = f.totalDegree := by
  by_cases hf : f = 0
  · simp only [hf, support_zero, Finset.sup_empty, totalDegree_zero]
    exact Finsupp.degree_zero
  · have := lexHomDegree_spec hf
    apply le_antisymm (le_totalDegree this.1)
    · rw [totalDegree, Finset.sup_le_iff]
      intro c hc
      exact Finsupp.LexHom.monotone_degree (this.2 c hc)

theorem lexHomDegree_eq_bot_iff {f : MvPolynomial σ R} : 
    f.lexHomDegree = ⊥ ↔ f.totalDegree = 0 := by
  rw [← lexHomDegree_degree, ← ofLexHom_inj]
  exact Iff.symm (Finsupp.degree_eq_zero_iff _)

theorem lexHomDegree_add {f g : MvPolynomial σ R} :
    (f + g).lexHomDegree ≤ f.lexHomDegree ⊔ g.lexHomDegree := by
  rw [← toLexHom_ofLexHom (f.lexHomDegree ⊔ g.lexHomDegree)]
  rw [lexHomDegree_le_iff]
  intro c hc
  simp only [toLexHom_ofLexHom, le_sup_iff]
  by_cases hc' : c ∈ f.support
  · left
    exact le_lexHomDegree hc'
  · right
    apply le_lexHomDegree
    simp only [mem_support_iff, coeff_add, ne_eq, not_not] at hc hc' ⊢
    simpa [hc', zero_add] using hc

theorem lexHomDegree_mul {f g : MvPolynomial σ R} :
    (f * g).lexHomDegree ≤ f.lexHomDegree + g.lexHomDegree := by
  rw [← toLexHom_ofLexHom (f.lexHomDegree + g.lexHomDegree), lexHomDegree_le_iff]
  simp only [toLexHom_ofLexHom]
  intro c hc
  rw [mem_support_iff] at hc
  rw [← not_lt]
  intro hc'
  apply hc
  rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨u, v⟩ h
  by_cases hu : f.lexHomDegree < toLexHom u 
  · convert zero_mul _ 
    exact coeff_eq_zero_of_lt hu
  · convert mul_zero _
    apply coeff_eq_zero_of_lt
    simp only [Finset.mem_antidiagonal] at h
    simp only [← h, toLexHom_add] at hc'
    dsimp only
    simp only [not_lt] at hu
    apply lt_of_add_lt_add_left (a := f.lexHomDegree)
    apply lt_of_lt_of_le hc'
    exact add_le_add_right hu (toLexHom v)

theorem lexHomDegree_leadingCoeff {f g : MvPolynomial σ R} :
    (f * g).coeff (ofLexHom (f.lexHomDegree + g.lexHomDegree)) = 
      f.coeff (ofLexHom f.lexHomDegree) * g.coeff (ofLexHom g.lexHomDegree) := by 
  rw [coeff_mul]
  convert Finset.sum_eq_single (ofLexHom f.lexHomDegree, ofLexHom g.lexHomDegree) _ _
  · rintro ⟨d, e⟩ h h'
    simp only [Finset.mem_antidiagonal] at h
    rw [← ofLexHom_toLexHom (d + e), ofLexHom_inj, toLexHom_add] at h
    by_cases k : toLexHom d ≤ f.lexHomDegree
    · convert mul_zero _
      apply coeff_eq_zero_of_lt
      dsimp only
      apply lt_of_add_lt_add_left (a := f.lexHomDegree)
      rw [← h, lt_iff_le_and_ne]
      constructor
      · exact add_le_add_right k (toLexHom e)
      · intro k'
        simp only [h, add_right_inj] at k'
        simp only [k', add_left_inj] at h
        simp [← h, k'] at h'
    · convert zero_mul _
      apply coeff_eq_zero_of_lt
      dsimp only
      rw [not_le] at k
      exact k
  · simp [Finset.mem_antidiagonal, ofLexHom_add]

theorem lexHomDegree_mul_eq {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) [IsDomain R] :
    (f * g).lexHomDegree = f.lexHomDegree + g.lexHomDegree := by
  apply le_antisymm lexHomDegree_mul
  rw [← toLexHom_ofLexHom (f.lexHomDegree + g.lexHomDegree)]
  apply le_lexHomDegree
  rw [mem_support_iff]
  rw [lexHomDegree_leadingCoeff]
  simp only [ne_eq, mul_eq_zero, not_or]
  simp only [← ne_eq, ← mem_support_iff]
  exact ⟨(lexHomDegree_spec hf).1, (lexHomDegree_spec hg).1⟩

end MvPolynomial

end LexHomDegree

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

variable {σ : Type*} 

-- This should be generalized to any type than `Fin n` (possibly finite)
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

theorem euclDivd {n : ℕ} (f : MvPolynomial (Fin n) R)
    (S : Fin n → Finset R) (Sne : ∀ i, (S i).Nonempty) :
    ∃ (h : Fin n → MvPolynomial (Fin n) R) (r : MvPolynomial (Fin n) R),
    f = Finset.univ.sum (fun i => (h i) * (S i).prod (fun (s : R) ↦ (X i - C s))) + r ∧
    (∀ i,
      (h i * (S i).prod (fun (s : R) ↦ (X i - C s))).totalDegree ≤ f.totalDegree) ∧
    (∀ i, r.weightedTotalDegree (Finsupp.single i 1) < (S i).card) := by
  induction f using lexHom_induction with
  | _ f hrec =>
  by_cases hD0 : f.lexHomDegree = ⊥
  · use fun _ ↦ 0, f
    rw [lexHomDegree_eq_bot_iff] at hD0
    simp only [zero_mul, Finset.sum_const_zero, zero_add, totalDegree_zero, zero_le, implies_true,
      true_and]
    · intro i
      apply lt_of_le_of_lt (b := f.totalDegree)
      · rw [← weightedTotalDegree_one]
        apply weightedTotalDegree_mono
        intro j
        simp only [Pi.one_apply, single_apply]
        split_ifs <;> simp
      · simp only [hD0, Finset.card_pos, Sne i]
  -- Now, f is not constant, hence nonzero
  have hf_ne_zero : f ≠ 0 := fun hf ↦ hD0 (by simp [hf])
  let d := ofLexHom f.lexHomDegree
  have hd : f.lexHomDegree = toLexHom d := by
    simp only [d, toLexHom_ofLexHom]
  let f' := f - monomial d (f.coeff d)
  have hf : f = f' + monomial d (f.coeff d) := by 
    simp only [f', sub_add_cancel]
  have hf' : f'.support = f.support.erase d := by 
    ext c
    simp [f']
    split_ifs with h
    · simp [h]
    · simp [sub_zero, Ne.symm h]
  have hf'D : f'.lexHomDegree < toLexHom d := by
    unfold lexHomDegree
    rw [Finset.sup_lt_iff]
    · intro c hc
      simp only [hf', Finset.mem_erase] at hc
      rw [lt_iff_le_and_ne, ← hd]
      exact ⟨le_lexHomDegree hc.2, fun h ↦ hc.1 (toLexHom.injective h)⟩
    · exact Ne.bot_lt' fun a ↦ hD0 a.symm
  obtain ⟨h', r', Hf', Hh', Hr'⟩ := hrec f' hf'D 
  by_cases H : ∀ i, d i < (S i).card
  · -- First case, the monomial `d` is small, we just add it to the remainder
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
      rw [weightedTotalDegree_monomial, if_neg, weight_single_one_apply]
      rw [← ne_eq, ← mem_support_iff] 
      exact (lexHomDegree_spec hf_ne_zero).1
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
      · exact le_of_le_of_eq hi (congrArg d h)
      · exact zero_le (d j)
    -- write `monomial d (f.coeff d) = `monomial d' (f.coeff d) * _ + f''` 
    -- where `f''` is smaller
    let f'' := monomial d (f.coeff d) - monomial d' (f.coeff d) * (S i).prod (fun s ↦ X i - C s)
    have hf'' : monomial d (f.coeff d) 
      = monomial d' (f.coeff d) * (S i).prod (fun s ↦ X i - C s) + f'' := by
      simp only [f'', add_sub_cancel]
    have hf''_degree : f''.totalDegree < f.totalDegree := by
      rw [← f.lexHomDegree_degree]
      simp only [totalDegree]
      rw [Finset.sup_lt_iff]
      · intro b hb
        change b.degree < d.degree
        suffices ∃ e < (S i).card, b = d' + single i e by
          obtain ⟨e, he, hb⟩ := this
          simp only [hb, ← hd', degree_add, degree_apply_single]
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
      · change _ < d.degree
        rw [← hd', degree_add, degree_apply_single]
        apply lt_of_lt_of_le (b := (S i).card)
        simp only [bot_eq_zero', Finset.card_pos, Sne i]
        exact Nat.le_add_left (S i).card d'.degree
    have hf''2 : f''.lexHomDegree < f.lexHomDegree := by
      rw [LexHom.lt_iff]
      left
      simp only [lexHomDegree_degree]
      exact hf''_degree
    obtain ⟨h'', r'', Hf'', Hh'', Hr''⟩ := hrec f'' hf''2 
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
          rw [← lexHomDegree_degree]
          change d'.degree + (S j).card = d.degree
          rw [← hd', ← h, degree_add, degree_apply_single]
        · simp 
    · intro i
      apply lt_of_le_of_lt (weightedTotalDegree_add _)
      simp only [sup_lt_iff]
      exact ⟨Hr' i, Hr'' i⟩

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
  set g := h i * ((S i).prod fun r ↦ X i - C r) with hg
  by_contra ht
  have : g.totalDegree = f.totalDegree := by
    apply le_antisymm  (by exact hh i)
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
