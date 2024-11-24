/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finsupp.MonomialOrder

/-! Homogeneous lexicographic monomial ordering 

* `MonomialOrder.degLex`: a variant of the lexicographic ordering that first compares degrees.
For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `DegLex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.degLex_le_iff`
and `MonomialOrder.degLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

-/

section finsupp

open Finsupp 

@[simp]
theorem degree_add {α : Type*} (a b : α →₀ ℕ) : (a + b).degree = a.degree + b.degree :=
  sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl

@[simp]
theorem degree_single {α : Type*} (a : α) (m : ℕ) : (Finsupp.single a m).degree = m := by 
  simp only [degree]
  rw [Finset.sum_eq_single a]
  · simp only [single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne hba.symm 
  · intro ha
    simp only [mem_support_iff, single_eq_same, ne_eq, Decidable.not_not] at ha
    rw [single_eq_same, ha]

@[simp]
theorem equivMapDomain_add {α β M : Type*} [AddCommMonoid M] (f : α ≃ β) (x y : α →₀ M) :
    equivMapDomain f (x + y) = equivMapDomain f x + equivMapDomain f y := by
  exact ext (congrFun rfl)

end finsupp

section degLex

/-- A type synonym to equip a type with its lexicographic order sorted by degrees. -/
def DegLex (α : Type*) := α

variable {α : Type*}

/-- `toDegLex` is the identity function to the `DegLex` of a type.  -/
@[match_pattern] def toDegLex : α ≃ DegLex α := Equiv.refl _

theorem toDegLex_injective : Function.Injective (toDegLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b := Iff.rfl

/-- `ofDegLex` is the identity function from the `DegLex` of a type.  -/
@[match_pattern] def ofDegLex : DegLex α ≃ α := Equiv.refl _

theorem ofDegLex_injective : Function.Injective (ofDegLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b := Iff.rfl

@[simp] theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex := rfl

@[simp] theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex := rfl

@[simp] theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a := rfl

@[simp] theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a := rfl

/-- A recursor for `DegLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegLex.rec {β : DegLex α → Sort*} (h : ∀ a, β (toDegLex a)) :
    ∀ a, β a := fun a => h (ofDegLex a)

@[simp] lemma DegLex.forall_iff {p : DegLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDegLex a) := Iff.rfl
@[simp] lemma DegLex.exists_iff {p : DegLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDegLex a) := Iff.rfl

noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (DegLex α) := ofDegLex.addCommMonoid

theorem toDegLex_add [AddCommMonoid α] (a b : α) :
    toDegLex (a + b) = toDegLex a + toDegLex b := rfl

theorem ofDegLex_add [AddCommMonoid α] (a b : DegLex α) :
    ofDegLex (a + b) = ofDegLex a + ofDegLex b := rfl

namespace Finsupp

/-- `Finsupp.DegLex r s` is the homogeneous lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegLex (α →₀ M)` has an order given by `Finsupp.DegLex (· < ·) (· < ·)`. -/
protected def DegLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))

theorem degLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl

theorem DegLex.wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegLex r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)

instance [LT α] : LT (DegLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩

theorem DegLex.lt_def [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (toLex ((ofDegLex a).degree, toLex (ofDegLex a))) <
        (toLex ((ofDegLex b).degree, toLex (ofDegLex b))) :=
  Iff.rfl

theorem DegLex.lt_iff [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree ∨
    (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDegLex a) < toLex (ofDegLex b)) := by
  simp only [Finsupp.DegLex.lt_def, Prod.Lex.lt_iff]

variable [LinearOrder α]

instance DegLex.isStrictOrder : IsStrictOrder (DegLex (α →₀ ℕ)) (· < ·) :=
  { irrefl := fun a ↦ by simp [DegLex.lt_def]
    trans := by
      intro a b c hab hbc
      simp only [DegLex.lt_iff] at hab hbc ⊢
      rcases hab with (hab | hab)
      · rcases hbc with (hbc | hbc)
        · left; exact lt_trans hab hbc
        · left; exact lt_of_lt_of_eq hab hbc.1
      · rcases hbc with (hbc | hbc)
        · left; exact lt_of_eq_of_lt hab.1 hbc
        · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩ }

/-- The partial order on `Finsupp`s obtained by the homogeneous lexicographic ordering.
See `Finsupp.DegLex.linearOrder` for a proof that this partial order is in fact linear. -/
instance DegLex.partialOrder : PartialOrder (DegLex (α →₀ ℕ)) :=
  PartialOrder.lift
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)

theorem DegLex.le_iff {x y : DegLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofDegLex x).degree < (ofDegLex y).degree ∨
      (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) ≤ toLex (ofDegLex y) := by
  simp only [le_iff_eq_or_lt, DegLex.lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]

theorem DegLex.single_strictAnti : StrictAnti (fun (a : α) ↦ toDegLex (single a 1)) := by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]

theorem DegLex.single_antitone : Antitone (fun (a : α) ↦ toDegLex (single a 1)) :=
  DegLex.single_strictAnti.antitone

theorem DegLex.single_lt_iff {a b : α} :
    toDegLex (Finsupp.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b := 
  DegLex.single_strictAnti.lt_iff_lt

theorem DegLex.single_le_iff {a b : α} :
    toDegLex (Finsupp.single b 1) ≤ toDegLex (Finsupp.single a 1) ↔ a ≤ b := 
  DegLex.single_strictAnti.le_iff_le

noncomputable instance : OrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  toAddCommMonoid := ofDegLex.addCommMonoid
  toPartialOrder := DegLex.partialOrder
  le_of_add_le_add_left a b c h := by
    rw [DegLex.le_iff] at h ⊢
    simpa only [ofDegLex_add, degree_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [DegLex.le_iff] at h ⊢
    simpa [ofDegLex_add, degree_add] using h

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance DegLex.linearOrder : LinearOrder (DegLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
noncomputable instance :
    LinearOrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  toOrderedCancelAddCommMonoid := inferInstance
  le_total := DegLex.linearOrder.le_total
  decidableLE := DegLex.linearOrder.decidableLE
  min_def := DegLex.linearOrder.min_def
  max_def := DegLex.linearOrder.max_def
  compare_eq_compareOfLessAndEq := DegLex.linearOrder.compare_eq_compareOfLessAndEq

theorem DegLex.monotone_degree :
    Monotone (fun (x : DegLex (α →₀ ℕ)) ↦ (ofDegLex x).degree) := by
  intro x y
  rw [DegLex.le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

instance DegLex.orderBot : OrderBot (DegLex (α →₀ ℕ)) where
  bot := toDegLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [DegLex.le_iff, ofDegLex_toDegLex, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or, ge_iff_le]
      exact bot_le
    · simp [h]

instance DegLex.wellFoundedLT [WellFoundedGT α] :
    WellFoundedLT (DegLex (α →₀ ℕ)) :=
  ⟨DegLex.wellFounded wellFounded_gt wellFounded_lt fun n ↦ (zero_le n).not_lt⟩

/-- for the deg-lexicographic ordering, X 1 < X 0 -/
example : toDegLex (single 1 1) < toDegLex (single 0 1) := by 
  rw [DegLex.single_lt_iff]
  exact Nat.one_pos

/-- for the deg-lexicographic ordering, X 0 * X 1 < X 0  ^ 2 -/
example : toDegLex (single 0 2) > toDegLex (single 0 1 + single 1 1) := by 
  simp only [gt_iff_lt, DegLex.lt_iff, ofDegLex_toDegLex, degree_add]
  simp only [degree_single, Nat.reduceAdd, lt_self_iff_false, true_and, false_or]
  use 0
  simp

/-- for the deg-lexicographic ordering, X 0 < X 1 ^ 2 -/
example : toDegLex (single 0 1) < toDegLex (single 1 2) := by 
  simp only [gt_iff_lt, DegLex.lt_iff, ofDegLex_toDegLex, degree_add]
  simp [degree_single]

end Finsupp

open scoped MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ]

/-- The deg-lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.degLex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := DegLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    change toDegLex a ≤ toDegLex b
    simp only [DegLex.le_iff, ofDegLex_toDegLex]
    by_cases ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ (not_lt.mp ha), toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h, degree_add]
      exact Nat.le_add_right a.degree (b - a).degree

theorem MonomialOrder.degLex_le_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≼[degLex] b ↔ toDegLex a ≤ toDegLex b :=
  Iff.rfl

theorem MonomialOrder.degLex_lt_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≺[degLex] b ↔ toDegLex a < toDegLex b :=
  Iff.rfl

theorem MonomialOrder.degLex_single_le_iff [WellFoundedGT σ] {a b : σ} :
    single a 1 ≼[degLex] single b 1 ↔ b ≤ a := by
  rw [MonomialOrder.degLex_le_iff, DegLex.single_le_iff]

theorem MonomialOrder.degLex_single_lt_iff [WellFoundedGT σ] {a b : σ} :
    single a 1 ≺[degLex] single b 1 ↔ b < a := by
  rw [MonomialOrder.degLex_lt_iff, DegLex.single_lt_iff]

end degLex

section degRevLex

/-- A type synonym to equip a type with its lexicographic order sorted 
  by reverse lexicographic degrees. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}
/-- `toDegRevLex` is the identity function to the `DegRevLex` of a type.  -/
@[match_pattern] def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

theorem toDegRevLex_injective : Function.Injective (toDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegRevLex_inj {a b : α} : toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

/-- `ofDegRevLex` is the identity function from the `DegRevLex` of a type.  -/
@[match_pattern] def ofDegRevLex : DegRevLex α ≃ α := Equiv.refl _

theorem ofDegRevLex_injective : Function.Injective (ofDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofDegRevLex_inj {a b : DegRevLex α} : ofDegRevLex a = ofDegRevLex b ↔ a = b := Iff.rfl

@[simp] theorem ofDegRevLex_symm_eq : (@ofDegRevLex α).symm = toDegRevLex := rfl

@[simp] theorem toDegRevLex_symm_eq : (@toDegRevLex α).symm = ofDegRevLex := rfl

@[simp] theorem ofDegRevLex_toDegRevLex (a : α) : ofDegRevLex (toDegRevLex a) = a := rfl

@[simp] theorem toDegRevLex_ofDegRevLex (a : DegRevLex α) : toDegRevLex (ofDegRevLex a) = a := rfl

/-- A recursor for `DegRevLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegRevLex.rec {β : DegRevLex α → Sort*} (h : ∀ a, β (toDegRevLex a)) :
    ∀ a, β a := fun a => h (ofDegRevLex a)

@[simp]
lemma DegRevLex.forall_iff {p : DegRevLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDegRevLex a) := Iff.rfl

@[simp]
lemma DegRevLex.exists_iff {p : DegRevLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDegRevLex a) := Iff.rfl

noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (DegRevLex α) := ofDegRevLex.addCommMonoid

theorem toDegRevLex_add [AddCommMonoid α] (a b : α) :
    toDegRevLex (a + b) = toDegRevLex a + toDegRevLex b := rfl

theorem ofDegRevLex_add [AddCommMonoid α] (a b : DegRevLex α) :
    ofDegRevLex (a + b) = ofDegRevLex a + ofDegRevLex b := rfl

namespace Finsupp

open OrderDual Function

/-- `Finsupp.DegRevLex r s` is the homogeneous reverse lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegRevLex (α →₀ M)` has an order given by `Finsupp.DegRevLex (· < ·) (· < ·)`. -/
protected def DegRevLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Function.swap (Finsupp.Lex (swap r) s))) on (fun x ↦ (x.degree, x))

theorem degRevLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegRevLex r s a b ↔
      Prod.Lex s (fun x y ↦ Finsupp.Lex (swap r) s y x) (a.degree, a) (b.degree, b) :=
  Iff.rfl

theorem degRevLex_iff {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegRevLex r s a b ↔
      s a.degree b.degree ∨ (a.degree = b.degree ∧ Finsupp.Lex (swap r) s b a) := by
  rw [degRevLex_def, Prod.lex_def]

/- instance [LT α] : LT (DegRevLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.DegRevLex (· < ·) (· < ·) (ofDegRevLex f) (ofDegRevLex g)⟩

theorem DegRevLex.lt_def [LT α] {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ 
      toLex ((ofDegRevLex a).degree, toLex (equivCongrLeft toDual (ofDegRevLex b))) <
        toLex ((ofDegRevLex b).degree, toLex (equivCongrLeft toDual (ofDegRevLex a))) := by
  change Finsupp.DegRevLex _ _ (ofDegRevLex a) (ofDegRevLex b) ↔ _
  simp only [Prod.Lex.lt_iff, degRevLex_def']
  exact or_congr Iff.rfl (and_congr_right (fun _ ↦ Iff.rfl))

theorem DegRevLex.lt_iff [LT α] {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (((ofDegRevLex a).degree = (ofDegRevLex b).degree) ∧ 
        toLex (equivCongrLeft toDual (ofDegRevLex b)) < 
          toLex (equivCongrLeft OrderDual.toDual (ofDegRevLex a))) := by
  simp only [lt_def, equivCongrLeft_apply, Prod.Lex.lt_iff]
-/

variable [LinearOrder α]

/- instance DegRevLex.isStrictOrder : IsStrictOrder (DegRevLex (α →₀ ℕ)) (· < ·) :=
  { irrefl := fun a ↦ by simp [DegRevLex.lt_def]
    trans := by
      intro a b c hab hbc
      simp only [DegRevLex.lt_iff] at hab hbc ⊢
      rcases hab with (hab | hab)
      · rcases hbc with (hbc | hbc)
        · left; exact lt_trans hab hbc
        · left; exact lt_of_lt_of_eq hab hbc.1
      · rcases hbc with (hbc | hbc)
        · left; exact lt_of_eq_of_lt hab.1 hbc
        · right; refine ⟨Eq.trans hab.1 hbc.1, lt_trans hbc.2 hab.2⟩ }
-/

/- This is a good and short definition, but it doesn't work with the earlier LT.lt, 
  which is thus commented out -/
/-- The partial order on `Finsupp`s obtained by the homogeneous lexicographic ordering.
See `Finsupp.DegRevLex.linearOrder` for a proof that this partial order is in fact linear. -/
instance DegRevLex.partialOrder : PartialOrder (DegRevLex (α →₀ ℕ)) := 
   PartialOrder.lift
    (fun (f : DegRevLex (α →₀ ℕ)) ↦ 
      toLex ((ofDegRevLex f).degree, toDual (toLex (equivCongrLeft toDual (ofDegRevLex f)))))
    (fun f g ↦ by 
      simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_imp]
      exact fun _ a ↦ a)  
/- {
  lt := LT.lt
  le := fun x y ↦ x = y ∨ x < y
  le_refl := fun _ ↦ Or.inl rfl
  le_trans := fun a b c hab hbc ↦ by
    simp only [LE.le] at hab 
    cases hab with
    | inl h => rw [h]; exact hbc
    | inr h => 
      simp only [LE.le] at hbc ⊢
      right
      cases hbc with
      | inl q => rw [← q]; exact h
      | inr q => exact DegRevLex.isStrictOrder.trans _ _ _ h q
  lt_iff_le_not_le := fun x y ↦ by
    constructor
    · intro h
      constructor
      · right; exact h
      · intro q
        apply DegRevLex.isStrictOrder.irrefl x
        cases q with
        | inl q => 
          rwa [q] at h
        | inr q => 
          exact DegRevLex.isStrictOrder.trans _ _ _ h q
    · rintro ⟨h, q⟩
      cases h with
      | inl h => 
        exfalso; apply q; rw [h, LE.le]; left; exact rfl
      | inr h => exact h
  le_antisymm := fun x y h q ↦ by 
    cases h with
    | inl h => exact h
    | inr h => 
      cases q with 
      | inl q => exact q.symm 
      | inr q => 
        exfalso
        exact DegRevLex.isStrictOrder.irrefl x (DegRevLex.isStrictOrder.trans _ _ _ h q) } -/

theorem DegRevLex.le_iff {x y : DegRevLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofDegRevLex x).degree < (ofDegRevLex y).degree ∨
      (ofDegRevLex x).degree = (ofDegRevLex y).degree ∧ 
        toLex (equivCongrLeft toDual (ofDegRevLex y)) ≤ 
          toLex (equivCongrLeft toDual (ofDegRevLex x)) := by
  conv_lhs => rw [LE.le, Preorder.toLE, PartialOrder.toPreorder, partialOrder]
  simp only [equivCongrLeft_apply, Prod.Lex.le_iff, toDual_le_toDual]

 theorem DegRevLex.lt_iff {x y : DegRevLex (α →₀ ℕ)} :
    x < y ↔ (ofDegRevLex x).degree < (ofDegRevLex y).degree ∨
      (ofDegRevLex x).degree = (ofDegRevLex y).degree ∧ 
        toLex (equivCongrLeft toDual (ofDegRevLex y)) < 
          toLex (equivCongrLeft toDual (ofDegRevLex x)) := by
  conv_lhs => rw [LT.lt, Preorder.toLT, PartialOrder.toPreorder, partialOrder]
  simp only [equivCongrLeft_apply, Prod.Lex.lt_iff, toDual_lt_toDual]

 theorem DegRevLex.lt_single_iff {a b : α} :
    toDegRevLex (single a 1) < toDegRevLex (single b 1) ↔ b < a := by 
  rw [DegRevLex.lt_iff]
  simp only [ofDegRevLex_toDegRevLex, degree_single, lt_self_iff_false, equivCongrLeft_apply,
    equivMapDomain_single, true_and, false_or]

noncomputable instance : OrderedCancelAddCommMonoid (DegRevLex (α →₀ ℕ)) where
  toAddCommMonoid := ofDegRevLex.addCommMonoid
  toPartialOrder := DegRevLex.partialOrder
  le_of_add_le_add_left a b c h := by
    rw [DegRevLex.le_iff] at h ⊢
    simpa [ofDegRevLex_add, degree_add, add_lt_add_iff_left, add_right_inj,
      equivCongrLeft_apply, equivMapDomain_add] using h
  add_le_add_left a b h c := by
    rw [DegRevLex.le_iff] at h ⊢
    simpa [ofDegRevLex_add, equivMapDomain_add, degree_add] using h

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance DegRevLex.linearOrder : LinearOrder (DegRevLex (α →₀ ℕ)) :=
  LinearOrder.lift' (fun (f : DegRevLex (α →₀ ℕ)) ↦ 
    toLex ((ofDegRevLex f).degree, toDual (toLex (equivCongrLeft toDual (ofDegRevLex f)))))
    (fun f g ↦ by 
      simp only [equivCongrLeft_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_imp, 
        Finsupp.ext_iff]
      intro _ h
      rw [← ofDegRevLex_inj]
      ext a
      simpa only [equivMapDomain_apply, toDual_symm_eq, ofDual_toDual] using h (toDual a))

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
noncomputable instance :
    LinearOrderedCancelAddCommMonoid (DegRevLex (α →₀ ℕ)) where
  toOrderedCancelAddCommMonoid := inferInstance
  le_total := DegRevLex.linearOrder.le_total
  decidableLE := DegRevLex.linearOrder.decidableLE
  min_def := DegRevLex.linearOrder.min_def
  max_def := DegRevLex.linearOrder.max_def
  compare_eq_compareOfLessAndEq := DegRevLex.linearOrder.compare_eq_compareOfLessAndEq

theorem DegRevLex.monotone_degree :
    Monotone (fun (x : DegRevLex (α →₀ ℕ)) ↦ (ofDegRevLex x).degree) := by
  intro x y
  rw [DegRevLex.le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

instance DegRevLex.orderBot : OrderBot (DegRevLex (α →₀ ℕ)) where
  bot := toDegRevLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [DegRevLex.le_iff, ofDegRevLex_toDegRevLex, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofDegRevLex x).degree with (h | h)
    · simp only [degree_eq_zero_iff] at h
      simp only [h, degree_zero, lt_self_iff_false, equivCongrLeft_apply, equivMapDomain_zero,
        toLex_zero, le_refl, and_self, or_true]
    · simp only [h, equivCongrLeft_apply, equivMapDomain_zero, toLex_zero, true_or]

theorem DegRevLex.wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegRevLex r s) := by
  suffices Set.univ.WellFoundedOn (Prod.Lex s (swap (Finsupp.Lex (swap r) s))) by
    unfold Finsupp.DegRevLex
    rw [← Set.wellFoundedOn_range]
    exact Set.WellFoundedOn.mono this (le_refl _) (fun _ _ ↦ trivial)
  rw [Set.wellFoundedOn_univ] 
  apply WellFounded.prod_lex hs
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  apply Set.WellFoundedOn.mono wft
  sorry

instance DegRevLex.wellFoundedLT [WellFoundedGT α] :
    WellFoundedLT (DegRevLex (α →₀ ℕ)) :=
  ⟨DegRevLex.wellFounded wellFounded_gt wellFounded_lt fun n ↦ (zero_le n).not_lt⟩

/-- for the reverse deg-lexicographic ordering, X 0 < X 1 ^ 2 -/
example : toDegRevLex (Finsupp.single 0 1) < toDegRevLex (Finsupp.single 1 2) := by 
  simp only [gt_iff_lt, DegRevLex.lt_iff, ofDegRevLex_toDegRevLex, degree_add]
  simp [degree_single]

/- Here we deviate from algebraic geometry by getting the opposite ordering on indeterminates -/

/-- for the reverse deg-lexicographic ordering, X 1 > X 0 -/
example : toDegRevLex (Finsupp.single 1 1) > toDegRevLex (Finsupp.single 0 1) := by 
  simp [DegRevLex.lt_iff, ofDegRevLex_toDegRevLex, degree_single]
  rw [Finsupp.lex_lt_iff]
  use 0
  simp

/- The following two examples show the difference between `DegLex` and `DegRevLex` -/

/-- for the deg-lexicographic ordering, X 1 ^ 2 < X 0 * X 2 -/
example : toDegLex (Finsupp.single 1 2) < toDegLex (Finsupp.single 0 1 + Finsupp.single 2 1) := by 
  simp only [gt_iff_lt, DegLex.lt_iff, ofDegLex_toDegLex, degree_add]
  simp only [degree_single, Nat.reduceAdd, lt_self_iff_false, true_and, false_or]
  use 0
  simp

/-- for the reverse deg-lexicographic ordering, X 1 ^ 2 > X 0 * X 2 -/
example : 
    toDegRevLex (Finsupp.single 1 2) > toDegRevLex (Finsupp.single 0 1 + Finsupp.single 2 1) := by 
  simp only [gt_iff_lt, DegRevLex.lt_iff, ofDegRevLex_toDegRevLex, degree_add]
  simp only [degree_single, Nat.reduceAdd, lt_self_iff_false, true_and, false_or]
  use 0
  simp

end Finsupp

open scoped MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ]

/-- The deg-lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.degRevLex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := DegRevLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegRevLex, map_add' := toDegRevLex_add }
  toSyn_monotone a b h := by
    change toDegRevLex a ≤ toDegRevLex b
    simp only [DegRevLex.le_iff, ofDegRevLex_toDegRevLex]
    by_cases ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ (not_lt.mp ha), toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h, degree_add]
      exact Nat.le_add_right a.degree (b - a).degree

theorem MonomialOrder.degRevLex_le_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≼[degRevLex] b ↔ toDegRevLex a ≤ toDegRevLex b :=
  Iff.rfl

theorem MonomialOrder.degRevLex_lt_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≺[degRevLex] b ↔ toDegRevLex a < toDegRevLex b :=
  Iff.rfl
