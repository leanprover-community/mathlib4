/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Subtype
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Notation
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Spread
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Inhabit
import Mathlib.Tactic.SimpRw

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `OrderDual α` : A type synonym reversing the meaning of all inequalities, with notation `αᵒᵈ`.
* `AsLinearOrder α`: A type synonym to promote `PartialOrder α` to `LinearOrder α` using
  `IsTotal α (≤)`.

### Transferring orders

- `Order.Preimage`, `Preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `PartialOrder.lift`, `LinearOrder.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `DenselyOrdered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication. This is enforced by a linter. See Note [nolint_ge] for more infos.

Dot notation is particularly useful on `≤` (`LE.le`) and `<` (`LT.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`LE.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `LE.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## Tags

preorder, order, partial order, poset, linear order, chain
-/


open Function

variable {ι α β : Type*} {π : ι → Type*}

/-! ### Bare relations -/

attribute [ext] LE

section LE

variable [LE α] {a b c : α}

protected lemma LE.le.ge (h : a ≤ b) : b ≥ a := h
protected lemma GE.ge.le (h : a ≥ b) : b ≤ a := h

theorem le_of_le_of_eq' : b ≤ c → a = b → a ≤ c := flip le_of_eq_of_le
theorem le_of_eq_of_le' : b = c → a ≤ b → a ≤ c := flip le_of_le_of_eq

alias LE.le.trans_eq := le_of_le_of_eq
alias LE.le.trans_eq' := le_of_le_of_eq'
alias Eq.trans_le := le_of_eq_of_le
alias Eq.trans_ge := le_of_eq_of_le'

end LE

section LT

variable [LT α] {a b c : α}

protected lemma LT.lt.gt (h : a < b) : b > a := h
protected lemma GT.gt.lt (h : a > b) : b < a := h

theorem lt_of_lt_of_eq' : b < c → a = b → a < c := flip lt_of_eq_of_lt
theorem lt_of_eq_of_lt' : b = c → a < b → a < c := flip lt_of_lt_of_eq

alias LT.lt.trans_eq := lt_of_lt_of_eq
alias LT.lt.trans_eq' := lt_of_lt_of_eq'
alias Eq.trans_lt := lt_of_eq_of_lt
alias Eq.trans_gt := lt_of_eq_of_lt'

end LT

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `RelEmbedding` (assuming `f`
is injective). -/
@[simp]
def Order.Preimage (f : α → β) (s : β → β → Prop) (x y : α) : Prop := s (f x) (f y)

@[inherit_doc] infixl:80 " ⁻¹'o " => Order.Preimage

/-- The preimage of a decidable order is decidable. -/
instance Order.Preimage.decidable (f : α → β) (s : β → β → Prop) [H : DecidableRel s] :
    DecidableRel (f ⁻¹'o s) := fun _ _ ↦ H _ _

/-! ### Preorders -/

section Preorder

variable [Preorder α] {a b c d : α}

theorem not_lt_iff_not_le_or_ge : ¬a < b ↔ ¬a ≤ b ∨ b ≤ a := by
  rw [lt_iff_le_not_ge, Classical.not_and_iff_not_or_not, Classical.not_not]

-- Unnecessary brackets are here for readability
lemma not_lt_iff_le_imp_ge : ¬ a < b ↔ (a ≤ b → b ≤ a) := by
  simp [not_lt_iff_not_le_or_ge, or_iff_not_imp_left]

@[deprecated (since := "2025-05-11")] alias not_lt_iff_le_imp_le := not_lt_iff_le_imp_ge

lemma ge_of_eq (h : a = b) : b ≤ a := le_of_eq h.symm

@[simp] lemma lt_self_iff_false (x : α) : x < x ↔ False := ⟨lt_irrefl x, False.elim⟩

alias le_trans' := ge_trans
alias lt_trans' := gt_trans
alias LE.le.trans := le_trans
alias LE.le.trans' := le_trans'
alias LT.lt.trans := lt_trans
alias LT.lt.trans' := lt_trans'
alias LE.le.trans_lt := lt_of_le_of_lt
alias LE.le.trans_lt' := lt_of_le_of_lt'
alias LT.lt.trans_le := lt_of_lt_of_le
alias LT.lt.trans_le' := lt_of_lt_of_le'
alias LE.le.lt_of_not_ge := lt_of_le_not_ge
alias LT.lt.le := le_of_lt
alias LT.lt.ne := ne_of_lt
alias Eq.le := le_of_eq
alias Eq.ge := ge_of_eq
alias LT.lt.asymm := lt_asymm
alias LT.lt.not_gt := lt_asymm

@[deprecated (since := "2025-05-11")] alias LE.le.lt_of_not_le := LE.le.lt_of_not_ge
@[deprecated (since := "2025-06-07")] alias LT.lt.not_lt := LT.lt.not_gt

theorem ne_of_not_le (h : ¬a ≤ b) : a ≠ b := fun hab ↦ h (le_of_eq hab)

protected lemma Eq.not_lt (hab : a = b) : ¬a < b := fun h' ↦ h'.ne hab
protected lemma Eq.not_gt (hab : a = b) : ¬b < a := hab.symm.not_lt

@[simp] lemma le_of_subsingleton [Subsingleton α] : a ≤ b := (Subsingleton.elim a b).le

-- Making this a @[simp] lemma causes confluence problems downstream.
@[nontriviality]
lemma not_lt_of_subsingleton [Subsingleton α] : ¬a < b := (Subsingleton.elim a b).not_lt

namespace LT.lt

protected theorem false : a < a → False := lt_irrefl a

theorem ne' (h : a < b) : b ≠ a := h.ne.symm

end LT.lt

theorem le_of_forall_le (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b := H _ le_rfl
theorem le_of_forall_ge (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a := H _ le_rfl

theorem forall_le_iff_le : (∀ ⦃c⦄, c ≤ a → c ≤ b) ↔ a ≤ b :=
  ⟨le_of_forall_le, fun h _ hca ↦ le_trans hca h⟩

theorem forall_ge_iff_le : (∀ ⦃c⦄, a ≤ c → b ≤ c) ↔ b ≤ a :=
  ⟨le_of_forall_ge, fun h _ hca ↦ le_trans h hca⟩

@[deprecated (since := "2025-07-27")] alias forall_le_iff_ge := forall_ge_iff_le

/-- monotonicity of `≤` with respect to `→` -/
@[gcongr] theorem le_imp_le_of_le_of_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a ≤ b → c ≤ d :=
  fun hab ↦ (h₁.trans hab).trans h₂

@[deprecated (since := "2025-07-31")] alias le_implies_le_of_le_of_le := le_imp_le_of_le_of_le

/-- monotonicity of `<` with respect to `→` -/
@[gcongr] theorem lt_imp_lt_of_le_of_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a < b → c < d :=
  fun hab ↦ (h₁.trans_lt hab).trans_le h₂

namespace Mathlib.Tactic.GCongr

@[gcongr] theorem gt_imp_gt (h₁ : a ≤ c) (h₂ : d ≤ b) : a > b → c > d := lt_imp_lt_of_le_of_le h₂ h₁

/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[gcongr_forward] def exactLeOfLt : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``le_of_lt #[h])

end Mathlib.Tactic.GCongr

end Preorder

/-! ### Partial order -/

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem ge_antisymm : a ≤ b → b ≤ a → b = a :=
  flip le_antisymm

theorem lt_of_le_of_ne' : a ≤ b → b ≠ a → a < b := fun h₁ h₂ ↦ lt_of_le_of_ne h₁ h₂.symm

theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_ne

theorem Ne.lt_of_le' : b ≠ a → a ≤ b → a < b :=
  flip lt_of_le_of_ne'

alias LE.le.antisymm := le_antisymm
alias LE.le.antisymm' := ge_antisymm
alias LE.le.lt_of_ne := lt_of_le_of_ne
alias LE.le.lt_of_ne' := lt_of_le_of_ne'

-- Unnecessary brackets are here for readability
lemma le_imp_eq_iff_le_imp_ge' : (a ≤ b → b = a) ↔ (a ≤ b → b ≤ a) where
  mp h hab := (h hab).le
  mpr h hab := (h hab).antisymm hab

@[deprecated (since := "2025-05-11")] alias le_imp_eq_iff_le_imp_le := le_imp_eq_iff_le_imp_ge'

-- Unnecessary brackets are here for readability
lemma le_imp_eq_iff_le_imp_ge : (a ≤ b → a = b) ↔ (a ≤ b → b ≤ a) where
  mp h hab := (h hab).ge
  mpr h hab := hab.antisymm (h hab)

@[deprecated (since := "2025-05-11")] alias ge_imp_eq_iff_le_imp_le := le_imp_eq_iff_le_imp_ge

namespace LE.le

theorem lt_iff_ne (h : a ≤ b) : a < b ↔ a ≠ b :=
  ⟨fun h ↦ h.ne, h.lt_of_ne⟩

theorem lt_iff_ne' (h : a ≤ b) : a < b ↔ b ≠ a :=
  ⟨fun h ↦ h.ne.symm, h.lt_of_ne'⟩

theorem not_lt_iff_eq (h : a ≤ b) : ¬a < b ↔ a = b :=
  h.lt_iff_ne.not_left

theorem not_lt_iff_eq' (h : a ≤ b) : ¬a < b ↔ b = a :=
  h.lt_iff_ne'.not_left

theorem ge_iff_eq (h : a ≤ b) : b ≤ a ↔ a = b :=
  ⟨h.antisymm, Eq.ge⟩

theorem ge_iff_eq' (h : a ≤ b) : b ≤ a ↔ b = a :=
  ⟨fun h' ↦ h'.antisymm h, Eq.le⟩

@[deprecated (since := "2025-06-08")] alias gt_iff_ne := lt_iff_ne'
@[deprecated (since := "2025-06-08")] alias le_iff_eq := ge_iff_eq'
@[deprecated (since := "2025-06-08")] alias not_gt_iff_eq := not_lt_iff_eq'

end LE.le

-- See Note [decidable namespace]
protected theorem Decidable.le_iff_eq_or_lt [DecidableLE α] : a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eq.trans or_comm

theorem le_iff_eq_or_lt : a ≤ b ↔ a = b ∨ a < b := le_iff_lt_or_eq.trans or_comm

theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ ↦ h1.lt_of_ne h2⟩

@[deprecated LE.le.not_lt_iff_eq (since := "2025-06-08")]
lemma eq_iff_not_lt_of_le (hab : a ≤ b) : a = b ↔ ¬ a < b := hab.not_lt_iff_eq.symm

@[deprecated (since := "2025-06-08")] alias LE.le.eq_iff_not_lt := eq_iff_not_lt_of_le

-- See Note [decidable namespace]
protected theorem Decidable.eq_iff_le_not_lt [DecidableLE α] : a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h ↦ ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ ↦
    h₁.antisymm <| Decidable.byContradiction fun h₃ ↦ h₂ (h₁.lt_of_not_ge h₃)⟩

theorem eq_iff_le_not_lt : a = b ↔ a ≤ b ∧ ¬a < b := open scoped Classical in
  Decidable.eq_iff_le_not_lt

-- See Note [decidable namespace]
protected theorem Decidable.eq_or_lt_of_le [DecidableLE α] (h : a ≤ b) : a = b ∨ a < b :=
  (Decidable.lt_or_eq_of_le h).symm

theorem eq_or_lt_of_le (h : a ≤ b) : a = b ∨ a < b := (lt_or_eq_of_le h).symm
theorem eq_or_lt_of_le' (h : a ≤ b) : b = a ∨ a < b := (eq_or_lt_of_le h).imp Eq.symm id
theorem lt_or_eq_of_le' (h : a ≤ b) : a < b ∨ b = a := (eq_or_lt_of_le' h).symm

alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le
alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le
alias LE.le.lt_or_eq := lt_or_eq_of_le
alias LE.le.eq_or_lt := eq_or_lt_of_le
alias LE.le.eq_or_lt' := eq_or_lt_of_le'
alias LE.le.lt_or_eq' := lt_or_eq_of_le'

@[deprecated (since := "2025-06-08")] alias eq_or_gt_of_le := eq_or_lt_of_le'
@[deprecated (since := "2025-06-08")] alias gt_or_eq_of_le := lt_or_eq_of_le'
@[deprecated (since := "2025-06-08")] alias LE.le.eq_or_gt := LE.le.eq_or_lt'
@[deprecated (since := "2025-06-08")] alias LE.le.gt_or_eq := LE.le.lt_or_eq'

theorem eq_of_le_of_not_lt (h₁ : a ≤ b) (h₂ : ¬a < b) : a = b := h₁.eq_or_lt.resolve_right h₂
theorem eq_of_le_of_not_lt' (h₁ : a ≤ b) (h₂ : ¬a < b) : b = a := (eq_of_le_of_not_lt h₁ h₂).symm

alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt
alias LE.le.eq_of_not_lt' := eq_of_le_of_not_lt'

@[deprecated (since := "2025-06-08")] alias eq_of_ge_of_not_gt := eq_of_le_of_not_lt'
@[deprecated (since := "2025-06-08")] alias LE.le.eq_of_not_gt := LE.le.eq_of_not_lt'

theorem Ne.le_iff_lt (h : a ≠ b) : a ≤ b ↔ a < b := ⟨fun h' ↦ lt_of_le_of_ne h' h, fun h ↦ h.le⟩

theorem Ne.not_le_or_not_ge (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a := not_and_or.1 <| le_antisymm_iff.not.1 h

@[deprecated (since := "2025-06-07")] alias Ne.not_le_or_not_le := Ne.not_le_or_not_ge

-- See Note [decidable namespace]
protected theorem Decidable.ne_iff_lt_iff_le [DecidableEq α] : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h ↦ Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h ↦ ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[simp]
theorem ne_iff_lt_iff_le : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  haveI := Classical.dec
  Decidable.ne_iff_lt_iff_le

lemma eq_of_forall_le_iff (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

lemma eq_of_forall_ge_iff (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  ((H _).2 le_rfl).antisymm ((H _).1 le_rfl)

/-- To prove commutativity of a binary operation `○`, we only to check `a ○ b ≤ b ○ a` for all `a`,
`b`. -/
lemma commutative_of_le {f : β → β → α} (comm : ∀ a b, f a b ≤ f b a) : ∀ a b, f a b = f b a :=
  fun _ _ ↦ (comm _ _).antisymm <| comm _ _

/-- To prove associativity of a commutative binary operation `○`, we only to check
`(a ○ b) ○ c ≤ a ○ (b ○ c)` for all `a`, `b`, `c`. -/
lemma associative_of_commutative_of_le {f : α → α → α} (comm : Std.Commutative f)
    (assoc : ∀ a b c, f (f a b) c ≤ f a (f b c)) : Std.Associative f where
  assoc a b c :=
    le_antisymm (assoc _ _ _) <| by
      rw [comm.comm, comm.comm b, comm.comm _ c, comm.comm a]
      exact assoc ..

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b : α}

namespace LE.le

lemma gt_or_le (h : a ≤ b) (c : α) : a < c ∨ c ≤ b := (lt_or_ge a c).imp id h.trans'
lemma ge_or_lt (h : a ≤ b) (c : α) : a ≤ c ∨ c < b := (le_or_gt a c).imp id h.trans_lt'
lemma ge_or_le (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b := (h.gt_or_le c).imp le_of_lt id

@[deprecated (since := "2025-05-11")] alias lt_or_le := gt_or_le
@[deprecated (since := "2025-05-11")] alias le_or_lt := ge_or_lt
@[deprecated (since := "2025-05-11")] alias le_or_le := ge_or_le

end LE.le

namespace LT.lt

lemma gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b := (le_or_gt b c).imp h.trans_le id

@[deprecated (since := "2025-06-07")] alias lt_or_lt := gt_or_lt

end LT.lt

-- Variant of `min_def` with the branches reversed.
theorem min_def' (a b : α) : min a b = if b ≤ a then b else a := by
  rw [min_def]
  rcases lt_trichotomy a b with (lt | eq | gt)
  · rw [if_pos lt.le, if_neg (not_le.mpr lt)]
  · rw [if_pos eq.le, if_pos eq.ge, eq]
  · rw [if_neg (not_le.mpr gt.gt), if_pos gt.le]

-- Variant of `min_def` with the branches reversed.
-- This is sometimes useful as it used to be the default.
theorem max_def' (a b : α) : max a b = if b ≤ a then a else b := by
  rw [max_def]
  rcases lt_trichotomy a b with (lt | eq | gt)
  · rw [if_pos lt.le, if_neg (not_le.mpr lt)]
  · rw [if_pos eq.le, if_pos eq.ge, eq]
  · rw [if_neg (not_le.mpr gt.gt), if_pos gt.le]

@[deprecated (since := "2025-05-11")] alias lt_of_not_le := lt_of_not_ge
@[deprecated (since := "2025-05-11")] alias lt_iff_not_le := lt_iff_not_ge

theorem Ne.lt_or_gt (h : a ≠ b) : a < b ∨ b < a :=
  lt_or_gt_of_ne h

@[deprecated (since := "2025-06-07")] alias Ne.lt_or_lt := Ne.lt_or_gt

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[simp]
theorem lt_or_lt_iff_ne : a < b ∨ b < a ↔ a ≠ b :=
  ne_iff_lt_or_gt.symm

theorem not_lt_iff_eq_or_lt : ¬a < b ↔ a = b ∨ b < a :=
  not_lt.trans <| Decidable.le_iff_eq_or_lt.trans <| or_congr eq_comm Iff.rfl

theorem exists_ge_of_linear (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

lemma exists_forall_ge_and {p q : α → Prop} :
    (∃ i, ∀ j ≥ i, p j) → (∃ i, ∀ j ≥ i, q j) → ∃ i, ∀ j ≥ i, p j ∧ q j
  | ⟨a, ha⟩, ⟨b, hb⟩ =>
    let ⟨c, hac, hbc⟩ := exists_ge_of_linear a b
    ⟨c, fun _d hcd ↦ ⟨ha _ <| hac.trans hcd, hb _ <| hbc.trans hcd⟩⟩

theorem le_of_forall_lt (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_gt fun h ↦ lt_irrefl _ (H _ h)

theorem forall_lt_iff_le : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_lt, fun h _ hca ↦ lt_of_lt_of_le hca h⟩

theorem le_of_forall_gt (H : ∀ c, a < c → b < c) : b ≤ a :=
  le_of_not_gt fun h ↦ lt_irrefl _ (H _ h)

theorem forall_gt_iff_le : (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
  ⟨le_of_forall_gt, fun h _ hac ↦ lt_of_le_of_lt h hac⟩

@[deprecated (since := "2025-06-07")] alias le_of_forall_lt' := le_of_forall_gt
@[deprecated (since := "2025-06-07")] alias forall_lt_iff_le' := forall_gt_iff_le

theorem eq_of_forall_lt_iff (h : ∀ c, c < a ↔ c < b) : a = b :=
  (le_of_forall_lt fun _ ↦ (h _).1).antisymm <| le_of_forall_lt fun _ ↦ (h _).2

theorem eq_of_forall_gt_iff (h : ∀ c, a < c ↔ b < c) : a = b :=
  (le_of_forall_gt fun _ ↦ (h _).2).antisymm <| le_of_forall_gt fun _ ↦ (h _).1

section ltByCases
variable {P : Sort*} {x y : α}

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_lt (h : x < y) {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P} :
    ltByCases x y h₁ h₂ h₃ = h₁ h := dif_pos h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_gt (h : y < x) {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P} :
    ltByCases x y h₁ h₂ h₃ = h₃ h := (dif_neg h.not_gt).trans (dif_pos h)

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_eq (h : x = y) {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P} :
    ltByCases x y h₁ h₂ h₃ = h₂ h := (dif_neg h.not_lt).trans (dif_neg h.not_gt)

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_not_lt (h : ¬ x < y) {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P}
    (p : ¬ y < x → x = y := fun h' => (le_antisymm (le_of_not_gt h') (le_of_not_gt h))) :
    ltByCases x y h₁ h₂ h₃ = if h' : y < x then h₃ h' else h₂ (p h') := dif_neg h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_not_gt (h : ¬ y < x) {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P}
    (p : ¬ x < y → x = y := fun h' => (le_antisymm (le_of_not_gt h) (le_of_not_gt h'))) :
    ltByCases x y h₁ h₂ h₃ = if h' : x < y then h₁ h' else h₂ (p h') :=
  dite_congr rfl (fun _ => rfl) (fun _ => dif_neg h)

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_ne (h : x ≠ y) {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P}
    (p : ¬ x < y → y < x := fun h' => h.lt_or_gt.resolve_left h') :
    ltByCases x y h₁ h₂ h₃ = if h' : x < y then h₁ h' else h₃ (p h') :=
  dite_congr rfl (fun _ => rfl) (fun _ => dif_pos _)

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_comm {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P}
    (p : y = x → x = y := fun h' => h'.symm) :
    ltByCases x y h₁ h₂ h₃ = ltByCases y x h₃ (h₂ ∘ p) h₁ := by
  refine ltByCases x y (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · rw [ltByCases_lt h, ltByCases_gt h]
  · rw [ltByCases_eq h, ltByCases_eq h.symm, comp_apply]
  · rw [ltByCases_lt h, ltByCases_gt h]

lemma eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt {x' y' : α}
    (ltc : (x < y) ↔ (x' < y')) (gtc : (y < x) ↔ (y' < x')) :
    x = y ↔ x' = y' := by simp_rw [eq_iff_le_not_lt, ← not_lt, ltc, gtc]

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_rec {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P} (p : P)
    (hlt : (h : x < y) → h₁ h = p) (heq : (h : x = y) → h₂ h = p)
    (hgt : (h : y < x) → h₃ h = p) :
    ltByCases x y h₁ h₂ h₃ = p :=
  ltByCases x y
    (fun h => ltByCases_lt h ▸ hlt h)
    (fun h => ltByCases_eq h ▸ heq h)
    (fun h => ltByCases_gt h ▸ hgt h)

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_eq_iff {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P} {p : P} :
    ltByCases x y h₁ h₂ h₃ = p ↔ (∃ h, h₁ h = p) ∨ (∃ h, h₂ h = p) ∨ (∃ h, h₃ h = p) := by
  refine ltByCases x y (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · simp only [ltByCases_lt, exists_prop_of_true, h, h.not_gt, not_false_eq_true,
    exists_prop_of_false, or_false, h.ne]
  · simp only [h, lt_self_iff_false, ltByCases_eq, not_false_eq_true,
    exists_prop_of_false, exists_prop_of_true, or_false, false_or]
  · simp only [ltByCases_gt, exists_prop_of_true, h, h.not_gt, not_false_eq_true,
    exists_prop_of_false, false_or, h.ne']

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltByCases_congr {x' y' : α} {h₁ : x < y → P} {h₂ : x = y → P} {h₃ : y < x → P}
    {h₁' : x' < y' → P} {h₂' : x' = y' → P} {h₃' : y' < x' → P} (ltc : (x < y) ↔ (x' < y'))
    (gtc : (y < x) ↔ (y' < x')) (hh'₁ : ∀ (h : x' < y'), h₁ (ltc.mpr h) = h₁' h)
    (hh'₂ : ∀ (h : x' = y'), h₂ ((eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt ltc gtc).mpr h) = h₂' h)
    (hh'₃ : ∀ (h : y' < x'), h₃ (gtc.mpr h) = h₃' h) :
    ltByCases x y h₁ h₂ h₃ = ltByCases x' y' h₁' h₂' h₃' := by
  refine ltByCases_rec _ (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · rw [ltByCases_lt (ltc.mp h), hh'₁]
  · rw [eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt ltc gtc] at h
    rw [ltByCases_eq h, hh'₂]
  · rw [ltByCases_gt (gtc.mp h), hh'₃]

set_option linter.deprecated false in
/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order,
non-dependently. -/
@[deprecated lt_trichotomy (since := "2025-04-21")]
abbrev ltTrichotomy (x y : α) (p q r : P) := ltByCases x y (fun _ => p) (fun _ => q) (fun _ => r)

variable {p q r s : P}

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_lt (h : x < y) : ltTrichotomy x y p q r = p := ltByCases_lt h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_gt (h : y < x) : ltTrichotomy x y p q r = r := ltByCases_gt h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_eq (h : x = y) : ltTrichotomy x y p q r = q := ltByCases_eq h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_not_lt (h : ¬ x < y) :
    ltTrichotomy x y p q r = if y < x then r else q := ltByCases_not_lt h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_not_gt (h : ¬ y < x) :
    ltTrichotomy x y p q r = if x < y then p else q := ltByCases_not_gt h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_ne (h : x ≠ y) :
    ltTrichotomy x y p q r = if x < y then p else r := ltByCases_ne h

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_comm : ltTrichotomy x y p q r = ltTrichotomy y x r q p := ltByCases_comm

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_self {p : P} : ltTrichotomy x y p p p = p :=
  ltByCases_rec p (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_eq_iff : ltTrichotomy x y p q r = s ↔
    (x < y ∧ p = s) ∨ (x = y ∧ q = s) ∨ (y < x ∧ r = s) := by
  refine ltByCases x y (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · simp only [ltTrichotomy_lt, false_and, true_and, or_false, h, h.not_gt, h.ne]
  · simp only [ltTrichotomy_eq, false_and, true_and, or_false, false_or, h, lt_irrefl]
  · simp only [ltTrichotomy_gt, false_and, true_and, false_or, h, h.not_gt, h.ne']

set_option linter.deprecated false in
@[deprecated lt_trichotomy (since := "2025-04-21")]
lemma ltTrichotomy_congr {x' y' : α} {p' q' r' : P} (ltc : (x < y) ↔ (x' < y'))
    (gtc : (y < x) ↔ (y' < x')) (hh'₁ : x' < y' → p = p')
    (hh'₂ : x' = y' → q = q') (hh'₃ : y' < x' → r = r') :
    ltTrichotomy x y p q r = ltTrichotomy x' y' p' q' r' :=
  ltByCases_congr ltc gtc hh'₁ hh'₂ hh'₃

end ltByCases

/-! #### `min`/`max` recursors -/

section MinMaxRec
variable {p : α → Prop}

lemma min_rec (ha : a ≤ b → p a) (hb : b ≤ a → p b) : p (min a b) := by
  obtain hab | hba := le_total a b <;> simp [min_eq_left, min_eq_right, *]

lemma max_rec (ha : b ≤ a → p a) (hb : a ≤ b → p b) : p (max a b) := by
  obtain hab | hba := le_total a b <;> simp [max_eq_left, max_eq_right, *]

lemma min_rec' (p : α → Prop) (ha : p a) (hb : p b) : p (min a b) :=
  min_rec (fun _ ↦ ha) fun _ ↦ hb

lemma max_rec' (p : α → Prop) (ha : p a) (hb : p b) : p (max a b) :=
  max_rec (fun _ ↦ ha) fun _ ↦ hb

lemma min_def_lt (a b : α) : min a b = if a < b then a else b := by
  rw [min_comm, min_def, ← ite_not]; simp only [not_le]

lemma max_def_lt (a b : α) : max a b = if a < b then b else a := by
  rw [max_comm, max_def, ← ite_not]; simp only [not_le]

end MinMaxRec
end LinearOrder

/-! ### Implications -/

lemma lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
  lt_of_not_ge fun h' ↦ (H h').not_gt h

lemma le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

lemma lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_ge.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_ge.symm

lemma lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c := not_le.symm.trans <| (not_congr H).trans <| not_le

lemma le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_le, fun H ↦ not_lt.symm.trans <| (not_congr H).trans <| not_lt⟩

/-- A symmetric relation implies two values are equal, when it implies they're less-equal. -/
lemma rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α → α → Prop) [IsSymm α r] {f : α → β}
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} : r a b → f a = f b := fun hab ↦
  le_antisymm (h a b hab) (h b a <| symm hab)

/-! ### Extensionality lemmas -/

@[ext]
lemma Preorder.toLE_injective : Function.Injective (@Preorder.toLE α) :=
  fun
  | { lt := A_lt, lt_iff_le_not_ge := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_ge := B_iff, .. } => by
    rintro ⟨⟩
    have : A_lt = B_lt := by
      funext a b
      rw [A_iff, B_iff]
    cases this
    congr

@[ext]
lemma PartialOrder.toPreorder_injective : Function.Injective (@PartialOrder.toPreorder α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; congr

@[ext]
lemma LinearOrder.toPartialOrder_injective : Function.Injective (@LinearOrder.toPartialOrder α) :=
  fun
  | { le := A_le, lt := A_lt,
      toDecidableLE := A_decidableLE, toDecidableEq := A_decidableEq, toDecidableLT := A_decidableLT
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },
    { le := B_le, lt := B_lt,
      toDecidableLE := B_decidableLE, toDecidableEq := B_decidableEq, toDecidableLT := B_decidableLT
      min := B_min, max := B_max, min_def := B_min_def, max_def := B_max_def,
      compare := B_compare, compare_eq_compareOfLessAndEq := B_compare_canonical, .. } => by
    rintro ⟨⟩
    obtain rfl : A_decidableLE = B_decidableLE := Subsingleton.elim _ _
    obtain rfl : A_decidableEq = B_decidableEq := Subsingleton.elim _ _
    obtain rfl : A_decidableLT = B_decidableLT := Subsingleton.elim _ _
    have : A_min = B_min := by
      funext a b
      exact (A_min_def _ _).trans (B_min_def _ _).symm
    cases this
    have : A_max = B_max := by
      funext a b
      exact (A_max_def _ _).trans (B_max_def _ _).symm
    cases this
    have : A_compare = B_compare := by
      funext a b
      exact (A_compare_canonical _ _).trans (B_compare_canonical _ _).symm
    congr

lemma Preorder.ext {A B : Preorder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y; exact H x y

lemma PartialOrder.ext {A B : PartialOrder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by ext x y; exact H x y

lemma PartialOrder.ext_lt {A B : PartialOrder α} (H : ∀ x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := by ext x y; rw [le_iff_lt_or_eq, @le_iff_lt_or_eq _ A, H]

lemma LinearOrder.ext {A B : LinearOrder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by ext x y; exact H x y

lemma LinearOrder.ext_lt {A B : LinearOrder α} (H : ∀ x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := LinearOrder.toPartialOrder_injective (PartialOrder.ext_lt H)

/-! ### Order dual -/

/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
def OrderDual (α : Type*) : Type _ :=
  α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type*) [LE α] : LE αᵒᵈ :=
  ⟨fun x y : α ↦ y ≤ x⟩

instance (α : Type*) [LT α] : LT αᵒᵈ :=
  ⟨fun x y : α ↦ y < x⟩

instance instOrd (α : Type*) [Ord α] : Ord αᵒᵈ where
  compare := fun (a b : α) ↦ compare b a

instance instSup (α : Type*) [Min α] : Max αᵒᵈ :=
  ⟨((· ⊓ ·) : α → α → α)⟩

instance instInf (α : Type*) [Max α] : Min αᵒᵈ :=
  ⟨((· ⊔ ·) : α → α → α)⟩

instance instIsTransLE [LE α] [T : IsTrans α LE.le] : IsTrans αᵒᵈ LE.le where
  trans := fun _ _ _ hab hbc ↦ T.trans _ _ _ hbc hab

instance instIsTransLT [LT α] [T : IsTrans α LT.lt] : IsTrans αᵒᵈ LT.lt where
  trans := fun _ _ _ hab hbc ↦ T.trans _ _ _ hbc hab

instance instPreorder (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl := fun _ ↦ le_refl _
  le_trans := fun _ _ _ hab hbc ↦ hbc.trans hab
  lt_iff_le_not_ge := fun _ _ ↦ lt_iff_le_not_ge

instance instPartialOrder (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  __ := inferInstanceAs (Preorder αᵒᵈ)
  le_antisymm := fun a b hab hba ↦ @le_antisymm α _ a b hba hab

instance instLinearOrder (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  __ := inferInstanceAs (Ord αᵒᵈ)
  le_total := fun a b : α ↦ le_total b a
  max := fun a b ↦ (min a b : α)
  min := fun a b ↦ (max a b : α)
  min_def := fun a b ↦ show (max .. : α) = _ by rw [max_comm, max_def]; rfl
  max_def := fun a b ↦ show (min .. : α) = _ by rw [min_comm, min_def]; rfl
  toDecidableLE := (inferInstance : DecidableRel (fun a b : α ↦ b ≤ a))
  toDecidableLT := (inferInstance : DecidableRel (fun a b : α ↦ b < a))
  toDecidableEq := (inferInstance : DecidableEq α)
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, eq_comm]
    rfl

/-- The opposite linear order to a given linear order -/
def _root_.LinearOrder.swap (α : Type*) (_ : LinearOrder α) : LinearOrder α :=
  inferInstanceAs <| LinearOrder (OrderDual α)

instance : ∀ [Inhabited α], Inhabited αᵒᵈ := fun [x : Inhabited α] => x

theorem Ord.dual_dual (α : Type*) [H : Ord α] : OrderDual.instOrd αᵒᵈ = H :=
  rfl

theorem Preorder.dual_dual (α : Type*) [H : Preorder α] : OrderDual.instPreorder αᵒᵈ = H :=
  rfl

theorem instPartialOrder.dual_dual (α : Type*) [H : PartialOrder α] :
    OrderDual.instPartialOrder αᵒᵈ = H :=
  rfl

theorem instLinearOrder.dual_dual (α : Type*) [H : LinearOrder α] :
    OrderDual.instLinearOrder αᵒᵈ = H :=
  rfl

end OrderDual

/-! ### `HasCompl` -/


instance Prop.hasCompl : HasCompl Prop :=
  ⟨Not⟩

instance Pi.hasCompl [∀ i, HasCompl (π i)] : HasCompl (∀ i, π i) :=
  ⟨fun x i ↦ (x i)ᶜ⟩

theorem Pi.compl_def [∀ i, HasCompl (π i)] (x : ∀ i, π i) :
    xᶜ = fun i ↦ (x i)ᶜ :=
  rfl

@[simp]
theorem Pi.compl_apply [∀ i, HasCompl (π i)] (x : ∀ i, π i) (i : ι) :
    xᶜ i = (x i)ᶜ :=
  rfl

instance IsIrrefl.compl (r) [IsIrrefl α r] : IsRefl α rᶜ :=
  ⟨@irrefl α r _⟩

instance IsRefl.compl (r) [IsRefl α r] : IsIrrefl α rᶜ :=
  ⟨fun a ↦ not_not_intro (refl a)⟩

theorem compl_lt [LinearOrder α] : (· < · : α → α → _)ᶜ = (· ≥ ·) := by simp [compl]
theorem compl_le [LinearOrder α] : (· ≤ · : α → α → _)ᶜ = (· > ·) := by simp [compl]
theorem compl_gt [LinearOrder α] : (· > · : α → α → _)ᶜ = (· ≤ ·) := by simp [compl]
theorem compl_ge [LinearOrder α] : (· ≥ · : α → α → _)ᶜ = (· < ·) := by simp [compl]

instance Ne.instIsEquiv_compl : IsEquiv α (· ≠ ·)ᶜ := by
  convert eq_isEquiv α
  simp [compl]

/-! ### Order instances on the function space -/


instance Pi.hasLe [∀ i, LE (π i)] :
    LE (∀ i, π i) where le x y := ∀ i, x i ≤ y i

theorem Pi.le_def [∀ i, LE (π i)] {x y : ∀ i, π i} :
    x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl

instance Pi.preorder [∀ i, Preorder (π i)] : Preorder (∀ i, π i) where
  __ := inferInstanceAs (LE (∀ i, π i))
  le_refl := fun a i ↦ le_refl (a i)
  le_trans := fun _ _ _ h₁ h₂ i ↦ le_trans (h₁ i) (h₂ i)

theorem Pi.lt_def [∀ i, Preorder (π i)] {x y : ∀ i, π i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp +contextual [lt_iff_le_not_ge, Pi.le_def]

instance Pi.partialOrder [∀ i, PartialOrder (π i)] : PartialOrder (∀ i, π i) where
  __ := Pi.preorder
  le_antisymm := fun _ _ h1 h2 ↦ funext fun b ↦ (h1 b).antisymm (h2 b)

namespace Sum

variable {α₁ α₂ : Type*} [LE β]

@[simp]
lemma elim_le_elim_iff {u₁ v₁ : α₁ → β} {u₂ v₂ : α₂ → β} :
    Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂ :=
  Sum.forall

lemma const_le_elim_iff {b : β} {v₁ : α₁ → β} {v₂ : α₂ → β} :
    Function.const _ b ≤ Sum.elim v₁ v₂ ↔ Function.const _ b ≤ v₁ ∧ Function.const _ b ≤ v₂ :=
  elim_const_const b ▸ elim_le_elim_iff ..

lemma elim_le_const_iff {b : β} {u₁ : α₁ → β} {u₂ : α₂ → β} :
    Sum.elim u₁ u₂ ≤ Function.const _ b ↔ u₁ ≤ Function.const _ b ∧ u₂ ≤ Function.const _ b :=
  elim_const_const b ▸ elim_le_elim_iff ..

end Sum

section Pi

/-- A function `a` is strongly less than a function `b` if `a i < b i` for all `i`. -/
def StrongLT [∀ i, LT (π i)] (a b : ∀ i, π i) : Prop :=
  ∀ i, a i < b i

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

variable [∀ i, Preorder (π i)] {a b c : ∀ i, π i}

theorem le_of_strongLT (h : a ≺ b) : a ≤ b := fun _ ↦ (h _).le

theorem lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b := by
  inhabit ι
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩

theorem strongLT_of_strongLT_of_le (hab : a ≺ b) (hbc : b ≤ c) : a ≺ c := fun _ ↦
  (hab _).trans_le <| hbc _

theorem strongLT_of_le_of_strongLT (hab : a ≤ b) (hbc : b ≺ c) : a ≺ c := fun _ ↦
  (hab _).trans_lt <| hbc _

alias StrongLT.le := le_of_strongLT

alias StrongLT.lt := lt_of_strongLT

alias StrongLT.trans_le := strongLT_of_strongLT_of_le

alias LE.le.trans_strongLT := strongLT_of_le_of_strongLT

end Pi

section Function

variable [DecidableEq ι] [∀ i, Preorder (π i)] {x y : ∀ i, π i} {i : ι} {a b : π i}

theorem le_update_iff : x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ x j ≤ z

theorem update_le_iff : Function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ z ≤ y j

theorem update_le_update_iff :
    Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp +contextual [update_le_iff]

@[simp]
theorem update_le_update_iff' : update x i a ≤ update x i b ↔ a ≤ b := by
  simp [update_le_update_iff]

@[simp]
theorem update_lt_update_iff : update x i a < update x i b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'

@[simp]
theorem le_update_self_iff : x ≤ update x i a ↔ x i ≤ a := by simp [le_update_iff]

@[simp]
theorem update_le_self_iff : update x i a ≤ x ↔ a ≤ x i := by simp [update_le_iff]

@[simp]
theorem lt_update_self_iff : x < update x i a ↔ x i < a := by simp [lt_iff_le_not_ge]

@[simp]
theorem update_lt_self_iff : update x i a < x ↔ a < x i := by simp [lt_iff_le_not_ge]

end Function

instance Pi.sdiff [∀ i, SDiff (π i)] : SDiff (∀ i, π i) :=
  ⟨fun x y i ↦ x i \ y i⟩

theorem Pi.sdiff_def [∀ i, SDiff (π i)] (x y : ∀ i, π i) :
    x \ y = fun i ↦ x i \ y i :=
  rfl

@[simp]
theorem Pi.sdiff_apply [∀ i, SDiff (π i)] (x y : ∀ i, π i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl

namespace Function

variable [Preorder α] [Nonempty β] {a b : α}

@[simp]
theorem const_le_const : const β a ≤ const β b ↔ a ≤ b := by simp [Pi.le_def]

@[simp]
theorem const_lt_const : const β a < const β b ↔ a < b := by simpa [Pi.lt_def] using le_of_lt

end Function

/-! ### Pullbacks of order instances -/

/-- Pull back a `Preorder` instance along an injective function.

See note [reducible non-instances]. -/
abbrev Function.Injective.preorder [Preorder β] [LE α] [LT α] (f : α → β)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    Preorder α where
  le_refl _ := le.1 <| le_refl _
  le_trans _ _ _ h₁ h₂ := le.1 <| le_trans (le.2 h₁) (le.2 h₂)
  lt_iff_le_not_ge _ _ := by
    rw [← le, ← le, ← lt, lt_iff_le_not_ge]

/-- Pull back a `PartialOrder` instance along an injective function.

See note [reducible non-instances]. -/
abbrev Function.Injective.partialOrder [PartialOrder β] [LE α] [LT α] (f : α → β)
    (hf : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    PartialOrder α where
  __ := Function.Injective.preorder f le lt
  le_antisymm _ _ h₁ h₂ := hf <| le_antisymm (le.2 h₁) (le.2 h₂)

/-- Pull back a `LinearOrder` instance along an injective function.

See note [reducible non-instances]. -/
abbrev Function.Injective.linearOrder [LinearOrder β] [LE α] [LT α] [Max α] [Min α] [Ord α]
    [DecidableEq α] [DecidableLE α] [DecidableLT α] (f : α → β)
    (hf : Function.Injective f) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (min : ∀ x y, f (x ⊓ y) = f x ⊓ f y) (max : ∀ x y, f (x ⊔ y) = f x ⊔ f y)
    (compare : ∀ x y, compare (f x) (f y) = compare x y) :
    LinearOrder α where
  toPartialOrder := hf.partialOrder _ le lt
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total _ _ := by simp only [← le, le_total]
  min_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← min_def, min]
  max_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← max_def, max]
  compare_eq_compareOfLessAndEq _ _ := by
    simp_rw [← compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, ← lt,
      hf.eq_iff]

/-!
### Lifts of order instances

Unlike the constructions above, these construct new data fields.
They should be avoided if the types already define any order or decidability instances.
-/

/-- Transfer a `Preorder` on `β` to a `Preorder` on `α` using a function `f : α → β`.

See also `Function.Injective.preorder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
abbrev Preorder.lift [Preorder β] (f : α → β) : Preorder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLT : LT α := ⟨fun a b ↦ f a < f b⟩
  Function.Injective.preorder f .rfl .rfl

/-- Transfer a `PartialOrder` on `β` to a `PartialOrder` on `α` using an injective
function `f : α → β`.

See also `Function.Injective.partialOrder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
abbrev PartialOrder.lift [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLT : LT α := ⟨fun a b ↦ f a < f b⟩
  Function.Injective.partialOrder f inj .rfl .rfl

theorem compare_of_injective_eq_compareOfLessAndEq (a b : α) [LinearOrder β]
    [DecidableEq α] (f : α → β) (inj : Injective f)
    [Decidable (LT.lt (self := PartialOrder.lift f inj |>.toLT) a b)] :
    compare (f a) (f b) =
      @compareOfLessAndEq _ a b (PartialOrder.lift f inj |>.toLT) _ _ := by
  have h := LinearOrder.compare_eq_compareOfLessAndEq (f a) (f b)
  simp only [h, compareOfLessAndEq]
  split_ifs <;> try (first | rfl | contradiction)
  · have : ¬ f a = f b := by rename_i h; exact inj.ne h
    contradiction
  · grind

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, then uses
them for `max` and `min` fields. See `LinearOrder.lift'` for a version that autogenerates `min` and
`max` fields, and `LinearOrder.liftWithOrd` for one that does not auto-generate `compare`
fields.

See also `Function.Injective.linearOrder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
abbrev LinearOrder.lift [LinearOrder β] [Max α] [Min α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLT : LT α := ⟨fun a b ↦ f a < f b⟩
  letI _instOrdα : Ord α := ⟨fun a b ↦ compare (f a) (f b)⟩
  letI _decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI _decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  inj.linearOrder _ .rfl .rfl hinf hsup (fun _ _ => rfl)

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `LinearOrder.lift`
for a version that takes `[Max α]` and `[Min α]`, then uses them as `max` and `min`. See
`LinearOrder.liftWithOrd'` for a version which does not auto-generate `compare` fields.
See note [reducible non-instances]. -/
abbrev LinearOrder.lift' [LinearOrder β] (f : α → β) (inj : Injective f) : LinearOrder α :=
  @LinearOrder.lift α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ ↦
    (apply_ite f _ _ _).trans (min_def _ _).symm

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, then uses
them for `max` and `min` fields. It also takes `[Ord α]` as an argument and uses them for `compare`
fields. See `LinearOrder.lift` for a version that autogenerates `compare` fields, and
`LinearOrder.liftWithOrd'` for one that auto-generates `min` and `max` fields.
fields. See note [reducible non-instances]. -/
abbrev LinearOrder.liftWithOrd [LinearOrder β] [Max α] [Min α] [Ord α] (f : α → β)
    (inj : Injective f) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y))
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLE : LT α := ⟨fun a b ↦ f a < f b⟩
  letI _decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI _decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  inj.linearOrder _ .rfl .rfl hinf hsup (fun _ _ => (compare_f _ _).symm)

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version auto-generates `min` and `max` fields. It also takes `[Ord α]`
as an argument and uses them for `compare` fields. See `LinearOrder.lift` for a version that
autogenerates `compare` fields, and `LinearOrder.liftWithOrd` for one that doesn't auto-generate
`min` and `max` fields. fields. See note [reducible non-instances]. -/
abbrev LinearOrder.liftWithOrd' [LinearOrder β] [Ord α] (f : α → β)
    (inj : Injective f)
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  @LinearOrder.liftWithOrd α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ _ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ ↦ (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

/-! ### Subtype of an order -/


namespace Subtype

@[simp]
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[gcongr] alias ⟨_, GCongr.mk_le_mk⟩ := mk_le_mk

@[simp]
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[gcongr] alias ⟨_, GCongr.mk_lt_mk⟩ := mk_lt_mk

@[simp, norm_cast]
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl

@[gcongr] alias ⟨_, GCongr.coe_le_coe⟩ := coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl

@[gcongr] alias ⟨_, GCongr.coe_lt_coe⟩ := coe_lt_coe

instance preorder [Preorder α] (p : α → Prop) : Preorder (Subtype p) :=
  Preorder.lift (fun (a : Subtype p) ↦ (a : α))

instance partialOrder [PartialOrder α] (p : α → Prop) : PartialOrder (Subtype p) :=
  PartialOrder.lift (fun (a : Subtype p) ↦ (a : α)) Subtype.coe_injective

instance decidableLE [Preorder α] [h : DecidableLE α] {p : α → Prop} :
    DecidableLE (Subtype p) := fun a b ↦ h a b

instance decidableLT [Preorder α] [h : DecidableLT α] {p : α → Prop} :
    DecidableLT (Subtype p) := fun a b ↦ h a b

/-- A subtype of a linear order is a linear order. We explicitly give the proofs of decidable
equality and decidable order in order to ensure the decidability instances are all definitionally
equal. -/
instance instLinearOrder [LinearOrder α] (p : α → Prop) : LinearOrder (Subtype p) :=
  @LinearOrder.lift (Subtype p) _ _ ⟨fun x y ↦ ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y ↦ ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) ↦ (a : α))
    Subtype.coe_injective (fun _ _ ↦ rfl) fun _ _ ↦
    rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `Data.Prod.Lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod
section LE
variable [LE α] [LE β] {x y : α × β} {a a₁ a₂ : α} {b b₁ b₂ : β}

instance : LE (α × β) where le p q := p.1 ≤ q.1 ∧ p.2 ≤ q.2

instance instDecidableLE [Decidable (x.1 ≤ y.1)] [Decidable (x.2 ≤ y.2)] : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.1 ≤ y.1 ∧ x.2 ≤ y.2))

lemma le_def : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := .rfl

@[simp] lemma mk_le_mk : (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂ := .rfl

@[gcongr] lemma GCongr.mk_le_mk (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : (a₁, b₁) ≤ (a₂, b₂) := ⟨ha, hb⟩

@[simp] lemma swap_le_swap : x.swap ≤ y.swap ↔ x ≤ y := and_comm
@[simp] lemma swap_le_mk : x.swap ≤ (b, a) ↔ x ≤ (a, b) := and_comm
@[simp] lemma mk_le_swap : (b, a) ≤ x.swap ↔ (a, b) ≤ x := and_comm

end LE

section Preorder

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance : Preorder (α × β) where
  __ := inferInstanceAs (LE (α × β))
  le_refl := fun ⟨a, b⟩ ↦ ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ ↦ ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp]
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

@[simp] lemma swap_lt_mk : x.swap < (b, a) ↔ x < (a, b) := by rw [← swap_lt_swap]; simp
@[simp] lemma mk_lt_swap : (b, a) < x.swap ↔ (a, b) < x := by rw [← swap_lt_swap]; simp

theorem mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rfl

theorem mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rfl

@[gcongr] alias ⟨_, GCongr.mk_le_mk_left⟩ := mk_le_mk_iff_left
@[gcongr] alias ⟨_, GCongr.mk_le_mk_right⟩ := mk_le_mk_iff_right

theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases h₁ : y.1 ≤ x.1
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_ge h.1.2 fun h₂ ↦ h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_ge h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h ↦ h₁.not_ge h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, fun h ↦ h₂.not_ge h.2⟩

@[simp]
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

protected lemma lt_of_lt_of_le (h₁ : x.1 < y.1) (h₂ : x.2 ≤ y.2) : x < y := by simp [lt_iff, *]
protected lemma lt_of_le_of_lt (h₁ : x.1 ≤ y.1) (h₂ : x.2 < y.2) : x < y := by simp [lt_iff, *]

lemma mk_lt_mk_of_lt_of_le (h₁ : a₁ < a₂) (h₂ : b₁ ≤ b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

lemma mk_lt_mk_of_le_of_lt (h₁ : a₁ ≤ a₂) (h₂ : b₁ < b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

end Preorder

/-- The pointwise partial order on a product.
(The lexicographic ordering is defined in `Order.Lexicographic`, and the instances are
available via the type synonym `α ×ₗ β = α × β`.) -/
instance instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α × β) where
  __ := inferInstanceAs (Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ ↦ Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

end Prod

/-! ### Additional order classes -/

/-- An order is dense if there is an element between any pair of distinct comparable elements. -/
class DenselyOrdered (α : Type*) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

theorem exists_between [LT α] [DenselyOrdered α] : ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _

instance OrderDual.denselyOrdered (α : Type*) [LT α] [h : DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun _ _ ha ↦ (@exists_between α _ h _ _ ha).imp fun _ ↦ And.symm⟩

@[simp]
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α :=
  ⟨by convert @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩

/-- Any ordered subsingleton is densely ordered. Not an instance to avoid a heavy subsingleton
typeclass search. -/
lemma Subsingleton.instDenselyOrdered {X : Type*} [Subsingleton X] [LT X] :
    DenselyOrdered X :=
  ⟨fun _ _ h ↦ ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] : DenselyOrdered (α × β) :=
  ⟨fun a b ↦ by
    simp_rw [Prod.lt_iff]
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · obtain ⟨c, ha, hb⟩ := exists_between h₁
      exact ⟨(c, _), Or.inl ⟨ha, h₂⟩, Or.inl ⟨hb, le_rfl⟩⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h₂
      exact ⟨(_, c), Or.inr ⟨h₁, ha⟩, Or.inr ⟨le_rfl, hb⟩⟩⟩

instance [∀ i, Preorder (π i)] [∀ i, DenselyOrdered (π i)] :
    DenselyOrdered (∀ i, π i) :=
  ⟨fun a b ↦ by
    classical
      simp_rw [Pi.lt_def]
      rintro ⟨hab, i, hi⟩
      obtain ⟨c, ha, hb⟩ := exists_between hi
      exact
        ⟨Function.update a i c,
          ⟨le_update_iff.2 ⟨ha.le, fun _ _ ↦ le_rfl⟩, i, by rwa [update_self]⟩,
          update_le_iff.2 ⟨hb.le, fun _ _ ↦ hab _⟩, i, by rwa [update_self]⟩⟩

section LinearOrder
variable [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}

theorem le_of_forall_gt_imp_ge_of_dense (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma forall_gt_imp_ge_iff_le_of_dense : (∀ a, a₂ < a → a₁ ≤ a) ↔ a₁ ≤ a₂ :=
  ⟨le_of_forall_gt_imp_ge_of_dense, fun ha _a ha₂ ↦ ha.trans ha₂.le⟩

lemma eq_of_le_of_forall_lt_imp_le_of_dense (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

theorem le_of_forall_lt_imp_le_of_dense (h : ∀ a < a₁, a ≤ a₂) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma forall_lt_imp_le_iff_le_of_dense : (∀ a < a₁, a ≤ a₂) ↔ a₁ ≤ a₂ :=
  ⟨le_of_forall_lt_imp_le_of_dense, fun ha _a ha₁ ↦ ha₁.le.trans ha⟩

theorem eq_of_le_of_forall_gt_imp_ge_of_dense (h₁ : a₂ ≤ a₁) (h₂ : ∀ a < a₁, a ≤ a₂) : a₁ = a₂ :=
  (le_of_forall_lt_imp_le_of_dense h₂).antisymm h₁

end LinearOrder

theorem dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀ a < a₂, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h ↦
    ⟨fun a ha₁ ↦ le_of_not_gt fun ha₂ ↦ h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ ↦ le_of_not_gt fun ha₁ ↦ h ⟨a, ha₁, ha₂⟩⟩

/-- If a linear order has no elements `x < y < z`, then it has at most two elements. -/
lemma eq_or_eq_or_eq_of_forall_not_lt_lt [LinearOrder α]
    (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) (x y z : α) : x = y ∨ y = z ∨ x = z := by
  by_contra hne
  simp only [not_or, ← Ne.eq_def] at hne
  rcases hne.1.lt_or_gt with h₁ | h₁ <;>
  rcases hne.2.1.lt_or_gt with h₂ | h₂ <;>
  rcases hne.2.2.lt_or_gt with h₃ | h₃
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]

namespace PUnit

variable (a b : PUnit)

instance instLinearOrder : LinearOrder PUnit where
  le  := fun _ _ ↦ True
  lt  := fun _ _ ↦ False
  max := fun _ _ ↦ unit
  min := fun _ _ ↦ unit
  toDecidableEq := inferInstance
  toDecidableLE := fun _ _ ↦ Decidable.isTrue trivial
  toDecidableLT := fun _ _ ↦ Decidable.isFalse id
  le_refl     := by intros; trivial
  le_trans    := by intros; trivial
  le_total    := by intros; exact Or.inl trivial
  le_antisymm := by intros; rfl
  lt_iff_le_not_ge := by simp only [not_true, and_false, forall_const]

theorem max_eq : max a b = unit :=
  rfl

theorem min_eq : min a b = unit :=
  rfl

protected theorem le : a ≤ b :=
  trivial

theorem not_lt : ¬a < b :=
  not_false

instance : DenselyOrdered PUnit :=
  ⟨fun _ _ ↦ False.elim⟩

end PUnit

section «Prop»

/-- Propositions form a complete Boolean algebra, where the `≤` relation is given by implication. -/
instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩

@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = (· → ·) :=
  rfl

theorem subrelation_iff_le {r s : α → α → Prop} : Subrelation r s ↔ r ≤ s :=
  Iff.rfl

instance Prop.partialOrder : PartialOrder Prop where
  __ := Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := propext ⟨Hab, Hba⟩

end «Prop»

/-! ### Linear order from a total partial order -/


/-- Type synonym to create an instance of `LinearOrder` from a `PartialOrder` and `IsTotal α (≤)` -/
def AsLinearOrder (α : Type*) :=
  α

instance [Inhabited α] : Inhabited (AsLinearOrder α) :=
  ⟨(default : α)⟩

noncomputable instance AsLinearOrder.linearOrder [PartialOrder α] [IsTotal α (· ≤ ·)] :
    LinearOrder (AsLinearOrder α) where
  __ := inferInstanceAs (PartialOrder α)
  le_total := @total_of α (· ≤ ·) _
  toDecidableLE := Classical.decRel _
