/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! Homogeneous reverse lexicographic monomial ordering

* `MonomialOrder.degRevLex`: the homogeneous reverse lexicographic ordering.
It first compares degrees, and on monomials of the same degree,
it `a > b` if the first distinct entry at which `a` differs from that of `b` is greater.

For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `DegRevLex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.degRevLex_le_iff`
and `MonomialOrder.degRevLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

-/

section degRevLex

/-- A type synonym to equip a type with its lexicographic order sorted
  by reverse lexicographic degrees. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}
/-- `toDegRevLex` is the identity function to the `DegRevLex` of a type. -/
@[match_pattern] def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

theorem toDegRevLex_injective : Function.Injective (toDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegRevLex_inj {a b : α} : toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

/-- `ofDegRevLex` is the identity function from the `DegRevLex` of a type. -/
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
/-- The partial order on `Finsupp`s obtained by the homogeneous reverse lexicographic ordering.
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
  simp [Prod.Lex.le_iff]

 theorem DegRevLex.lt_iff {x y : DegRevLex (α →₀ ℕ)} :
    x < y ↔ (ofDegRevLex x).degree < (ofDegRevLex y).degree ∨
      (ofDegRevLex x).degree = (ofDegRevLex y).degree ∧
        toLex (equivCongrLeft toDual (ofDegRevLex y)) <
          toLex (equivCongrLeft toDual (ofDegRevLex x)) := by
  conv_lhs => rw [LT.lt, Preorder.toLT, PartialOrder.toPreorder, partialOrder]
  simp [Prod.Lex.lt_iff]

/-- Explicit expansion -/
theorem DegRevLex.lt_iff' {x y : DegRevLex (α →₀ ℕ)} :
    x < y ↔ (ofDegRevLex x).degree < (ofDegRevLex y).degree ∨
      (ofDegRevLex x).degree = (ofDegRevLex y).degree ∧
        ∃ j, (∀ i > j, ofDegRevLex x i = ofDegRevLex y i) ∧
          ofDegRevLex y j < ofDegRevLex x j := by
  rw [DegRevLex.lt_iff]
  apply or_congr
  · exact gt_iff_lt
  · simp only [and_congr_right_iff]
    intro h
    simp only [equivCongrLeft_apply, lex_lt_iff, ofLex_toLex, equivMapDomain_apply, toDual_symm_eq,
      OrderDual.forall, ofDual_toDual, OrderDual.exists, toDual_lt_toDual]
    apply exists_congr
    intro a
    simp only [and_congr_left_iff]
    intro ha
    apply forall₂_congr
    intro i hi
    exact eq_comm

theorem DegRevLex.single_lt_iff {a b : α} :
    toDegRevLex (single a 1) < toDegRevLex (single b 1) ↔ b < a := by
  simp [DegRevLex.lt_iff, ofDegRevLex_toDegRevLex, degree_single, Finsupp.Lex.single_lt_iff]

theorem DegRevLex.single_strictAnti : StrictAnti (fun (a : α) ↦ toDegRevLex (single a 1)) := by
  intro _ _ h
  simp only [DegRevLex.single_lt_iff, h]

theorem DegRevLex.single_antitone : Antitone (fun (a : α) ↦ toDegRevLex (single a 1)) :=
  DegRevLex.single_strictAnti.antitone

 theorem DegRevLex.single_le_iff {a b : α} :
    toDegRevLex (single a 1) ≤ toDegRevLex (single b 1) ↔ b ≤ a :=
  DegRevLex.single_strictAnti.le_iff_le

noncomputable instance : IsOrderedCancelAddMonoid (DegRevLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [DegRevLex.le_iff] at h ⊢
    simpa [ofDegRevLex_add, degree_add, add_lt_add_iff_left, add_right_inj,
      equivCongrLeft_apply, equivMapDomain_eq_mapDomain, mapDomain_add] using h
  add_le_add_left a b h c := by
    rw [DegRevLex.le_iff] at h ⊢
    simpa [ofDegRevLex_add, equivMapDomain_eq_mapDomain, mapDomain_add, degree_add] using h

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance : LinearOrder (DegRevLex (α →₀ ℕ)) :=
  LinearOrder.lift' (fun (f : DegRevLex (α →₀ ℕ)) ↦
    toLex ((ofDegRevLex f).degree, toDual (toLex (equivCongrLeft toDual (ofDegRevLex f)))))
    (fun f g ↦ by
      simp only [equivCongrLeft_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_imp,
        Finsupp.ext_iff]
      intro _ h
      rw [← ofDegRevLex_inj]
      ext a
      simpa only [equivMapDomain_apply, toDual_symm_eq, ofDual_toDual] using h (toDual a))

theorem DegRevLex.monotone_degree :
    Monotone (fun (x : DegRevLex (α →₀ ℕ)) ↦ (ofDegRevLex x).degree) := by
  intro x y
  rw [DegRevLex.le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

/-- The `0` function is the minimal element of `DegRevLex`. -/
instance : OrderBot (DegRevLex (α →₀ ℕ)) where
  bot := toDegRevLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [DegRevLex.le_iff, ofDegRevLex_toDegRevLex, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofDegRevLex x).degree with (h | h)
    · simp only [degree_eq_zero_iff] at h
      simp only [h, degree_zero, lt_self_iff_false, equivCongrLeft_apply, equivMapDomain_zero,
        toLex_zero, le_refl, and_self, or_true]
    · simp only [h, equivCongrLeft_apply, equivMapDomain_zero, toLex_zero, true_or]

/-- `Finsupp.DegRevLex` is well founded. -/
theorem DegRevLex.wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] [Finite α]
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegRevLex r s) := by
  sorry

/-- `Finsupp.DegRevLex` is well founded. -/
instance DegRevLex.wellFoundedLT [Finite α] :
    WellFoundedLT (DegRevLex (α →₀ ℕ)) := by
  apply IsWellFounded.mk
  sorry

/-- for the reverse deg-lexicographic ordering, X 0 < X 1 ^ 2 -/
example : toDegRevLex (Finsupp.single 0 1) < toDegRevLex (Finsupp.single 1 2) := by
  simp only [gt_iff_lt, DegRevLex.lt_iff, ofDegRevLex_toDegRevLex, degree_add]
  simp [degree_single]

/- Here we deviate from algebraic geometry by getting the opposite ordering on indeterminates -/

/-- for the reverse deg-lexicographic ordering, X 0 > X 1 -/
example : toDegRevLex (single 0 1) > toDegRevLex (single 1 1) := by
  simp only [DegRevLex.single_lt_iff, zero_lt_one]

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
  simp only [DegRevLex.lt_iff']
  simp
  use 2
  simp
  intro i hi
  rw [single_eq_of_ne _, single_eq_of_ne _, single_eq_of_ne _, add_zero]
  · exact ne_of_lt (lt_trans Nat.one_lt_two hi)
  · exact ne_of_lt hi
  · exact ne_of_lt (lt_trans Nat.zero_lt_two hi)

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
    simp only [AddEquiv.coe_mk, DegRevLex.le_iff, ofDegRevLex_toDegRevLex, equivCongrLeft_apply]
    rcases Nat.lt_or_ge a.degree b.degree with ha | ha
    · exact Or.inl ha
    · suffices b = a by simp [this]
      obtain ⟨c, rfl⟩ := exists_add_of_le h
      convert add_zero a
      simpa [degree_eq_zero_iff] using ha
  wf := sorry

theorem MonomialOrder.degRevLex_le_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≼[degRevLex] b ↔ toDegRevLex a ≤ toDegRevLex b :=
  Iff.rfl

theorem MonomialOrder.degRevLex_lt_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≺[degRevLex] b ↔ toDegRevLex a < toDegRevLex b :=
  Iff.rfl

  end degRevLex
