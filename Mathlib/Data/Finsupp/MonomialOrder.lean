/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
import Mathlib.Logic.Equiv.TransferInstance

/-! # Monomial orders

## Monomial orders

A *monomial order* is well ordering relation on a type of the form `σ →₀ ℕ` which
is compatible with addition and for which `0` is the smallest element.
Since several monomial orders may have to be used simultaneously, one cannot
get them as instances.
In this formalization, they are presented as a structure `MonomialOrder` which encapsulates
`MonomialOrder.toSyn`, an additive and monotone isomorphism to a linearly ordered cancellative
additive commutative monoid.
The entry `MonomialOrder.wf` asserts that `MonomialOrder.syn` is well founded.

The terminology comes from commutative algebra and algebraic geometry, especially Gröbner bases,
where `c : σ →₀ ℕ` are exponents of monomial.

Given a monomial order `m : MonomialOrder σ`, we provide the notation
`c ≼[m] d` and `c ≺[m] d` to compare `c d : σ →₀ ℕ` with respect to `m`.
It is activated using `open scoped MonomialOrder`.

## Examples

We provide four examples of monomial orders, the most standard ones in commutative algebra.

* `MonomialOrder.lex` : the lexicographic ordering on `σ →₀ ℕ`.
For this, `σ` needs to be embedded with an ordering relation which statisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `Lex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.lex_le_iff`
and `MonomialOrder.lex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

* `MonomialOrder.revLex` : the reverse lexicographic ordering on `σ →₀ ℕ`.
For this, `σ` needs to be endowed with an ordering relation which satisfies `WellFoundedLT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `Lex (σᵒᵈ →₀ ℕ)` and the two lemmas `MonomialOrder.revLex_le_iff`
and `MonomialOrder.revLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σᵒᵈ →₀ ℕ)`.

* `MonomialOrder.degLex`: a variant of the lexicographic ordering that first compares degrees.
For this, `σ` needs to be embedded with an ordering relation which statisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `DegLex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.degLex_le_iff`
and `MonomialOrder.degLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

* `MonomialOrder.degRevLex`: a variant of the reverse lexicographic ordering
that first compares degrees.
For this, `σ` needs to be embedded with an ordering relation which statisfies `WellFoundedLT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `DegLex (σᵒᵈ →₀ ℕ)` and the two lemmas `MonomialOrder.degRevLex_le_iff`
and `MonomialOrder.degRevLex_lt_iff` rewrite the ordering as comparisons in the type
`DegLex (σᵒᵈ →₀ ℕ)`.

-/

/-- Monomial orders : equivalence of `σ →₀ ℕ` with a well ordered type -/
structure MonomialOrder (σ : Type*) where
  /-- The synonym type -/
  syn : Type*
  /-- `syn` is a linearly ordered cancellative additive commutative monoid -/
  locacm : LinearOrderedCancelAddCommMonoid syn := by infer_instance
  /-- the additive equivalence from `σ →₀ ℕ` to `syn` -/
  toSyn : (σ →₀ ℕ) ≃+ syn
  /-- `toSyn` is monotone -/
  toSyn_monotone : Monotone toSyn
  /-- `syn` is a well ordering -/
  wf : WellFoundedLT syn

attribute [instance] MonomialOrder.locacm MonomialOrder.wf

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)


lemma le_add_right (a b : σ →₀ ℕ) :
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simp [map_add, zero_add] at this
    exact this

@[simp]
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl

theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a ≤ 0 := eq_bot_iff

lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

/-- Given a monomial order, notation for the corresponding strict order relation on `σ →₀ ℕ` -/
scoped
notation:25 c "≺[" m:25 "]" d:25 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

/-- Given a monomial order, notation for the corresponding order relation on `σ →₀ ℕ` -/
scoped
notation:25 c "≼[" m:25 "]" d:25 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)

end MonomialOrder

section Lex

open Finsupp

open scoped MonomialOrder

-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance {α N : Type*} [LinearOrder α] [OrderedCancelAddCommMonoid N] :
    OrderedCancelAddCommMonoid (Lex (α →₀ N)) where
  le_of_add_le_add_left a b c h := by simpa only [add_le_add_iff_left] using h
  add_le_add_left a b h c := by simpa only [add_le_add_iff_left] using h

theorem Finsupp.lex_lt_iff {α N : Type*} [LinearOrder α] [LinearOrder N] [Zero N]
    {a b : Lex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, j< i → ofLex a j = ofLex b j) ∧ ofLex a i < ofLex b i :=
    Finsupp.lex_def

theorem Finsupp.lex_le_iff {α N : Type*} [LinearOrder α] [LinearOrder N] [Zero N]
    {a b : Lex (α →₀ N)} :
    a ≤ b ↔ a = b ∨ ∃ i, (∀ j, j< i → ofLex a j = ofLex b j) ∧ ofLex a i < ofLex b i := by
    rw [le_iff_eq_or_lt, Finsupp.lex_lt_iff]

/- -- #check Finsupp.toLex_monotone
theorem _root_.Finsupp.toLex_monotone' {σ : Type*} [LinearOrder σ] :
    Monotone (toLex (α := σ →₀ ℕ)) := by
  apply Finsupp.toLex_monotone
  intro a b h
  rw [← (add_tsub_cancel_of_le h), toLex_add]
  simp only [AddEquiv.refl_symm, le_add_iff_nonneg_right, ge_iff_le]
  apply bot_le
-/

variable {σ : Type*} [LinearOrder σ]

/-- The lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.lex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ →₀ ℕ)
  locacm := Lex.linearOrderedCancelAddCommMonoid
  toSyn := {
    toEquiv := toLex
    map_add' := toLex_add } -- AddEquiv.refl _ -- (AddEquiv.refl (Lex (σ →₀ ℕ))).symm
  wf := Lex.wellFoundedLT
  toSyn_monotone := Finsupp.toLex_monotone

theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ toLex c ≤ toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ toLex c < toLex d := Iff.rfl

/-- The reverse lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.revLex [WellFoundedLT σ] :
    MonomialOrder σ :=
  MonomialOrder.lex (σ := σᵒᵈ)

theorem MonomialOrder.revLex_le_iff [WellFoundedLT σ] {c d : σ →₀ ℕ} :
    c ≼[revLex] d ↔ (toLex c : Lex (σᵒᵈ →₀ ℕ)) ≤ (toLex d : Lex (σᵒᵈ →₀ ℕ)) :=
  Iff.rfl

theorem MonomialOrder.revLlex_lt_iff [WellFoundedLT σ] {c d : σ →₀ ℕ} :
    c ≺[revLex] d ↔ (toLex c : Lex (σᵒᵈ →₀ ℕ)) < (toLex d : Lex (σᵒᵈ →₀ ℕ)) :=
  Iff.rfl

end Lex

section degLex

/-- A type synonym to equip a type with its lexicographic order sorted by degrees. -/
def DegLex (α : Type*) := α

variable {α : Type*}
/-- `toDegLex` is the identity function to the `DegLex` of a type.  -/
@[match_pattern]
def toDegLex : α ≃ DegLex α :=
  Equiv.refl _

/-- `ofDegLex` is the identity function from the `DegLex` of a type.  -/
@[match_pattern]
def ofDegLex : DegLex α ≃ α :=
  Equiv.refl _

@[simp]
theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex :=
  rfl

@[simp]
theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex :=
  rfl

@[simp]
theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a :=
  rfl

@[simp]
theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a :=
  rfl

theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b :=
  Iff.rfl

theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b :=
  Iff.rfl

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

variable {M N : Type*} [AddCommMonoid M] [CanonicallyOrderedAddCommMonoid N]

/-- `Finsupp.DegLex r s` is the homogeneous lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegLex (α →₀ M)` has an order given by `Finsupp.DegLex (· < ·) (· < ·)`. -/
protected def DegLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))

theorem degLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegLex r s a b ↔
      Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
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

theorem degree_add {α : Type*} (a b : α →₀ ℕ) :
    (a + b).degree = a.degree + b.degree :=
  sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl

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

end Finsupp

open scoped MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ]

/-- The deg-lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.degLex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := DegLex (σ →₀ ℕ)
  locacm := inferInstance
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  wf := Finsupp.DegLex.wellFoundedLT
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

/-- The deg-reverse lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.degRevLex [WellFoundedLT σ] :
    MonomialOrder σ :=
  MonomialOrder.degLex (σ := σᵒᵈ)

theorem MonomialOrder.degRevLex_le_iff [WellFoundedLT σ] {a b : σ →₀ ℕ} :
    a ≼[degRevLex] b ↔ (toDegLex a : σᵒᵈ →₀ ℕ) ≤ (toDegLex b : σᵒᵈ →₀ ℕ) :=
  Iff.rfl

theorem MonomialOrder.degRevLex_lt_iff [WellFoundedLT σ] {a b : σ →₀ ℕ} :
    a ≺[degRevLex] b ↔ (toDegLex a : σᵒᵈ →₀ ℕ) < (toDegLex b : σᵒᵈ →₀ ℕ) :=
  Iff.rfl


end degLex


