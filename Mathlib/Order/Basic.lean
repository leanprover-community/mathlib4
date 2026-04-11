/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Subtype
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.FastInstance
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Inhabit
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.GCongr.Core

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

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

## Tags

preorder, order, partial order, poset, linear order, chain
-/

@[expose] public section


open Function

variable {ι α β : Type*} {π : ι → Type*}

/-! ### Bare relations -/

attribute [ext] LE

section LE

variable [LE α] {a b c : α}

@[to_dual self] protected lemma LE.le.ge (h : a ≤ b) : b ≥ a := h
@[to_dual self] protected lemma GE.ge.le (h : a ≥ b) : b ≤ a := h

@[deprecated le_of_eq_of_le (since := "2025-11-29")]
theorem le_of_le_of_eq' : b ≤ c → a = b → a ≤ c := flip le_of_eq_of_le

@[deprecated le_of_le_of_eq (since := "2025-11-29")]
theorem le_of_eq_of_le' : b = c → a ≤ b → a ≤ c := flip le_of_le_of_eq

@[to_dual trans_eq'] alias LE.le.trans_eq := le_of_le_of_eq
@[to_dual trans_ge] alias Eq.trans_le := le_of_eq_of_le

end LE

section LT

variable [LT α] {a b c : α}

@[to_dual self] protected lemma LT.lt.gt (h : a < b) : b > a := h
@[to_dual self] protected lemma GT.gt.lt (h : a > b) : b < a := h

@[deprecated lt_of_eq_of_lt (since := "2025-11-29")]
theorem lt_of_lt_of_eq' : b < c → a = b → a < c := flip lt_of_eq_of_lt

@[deprecated lt_of_lt_of_eq (since := "2025-11-29")]
theorem lt_of_eq_of_lt' : b = c → a < b → a < c := flip lt_of_lt_of_eq

@[to_dual trans_eq'] alias LT.lt.trans_eq := lt_of_lt_of_eq
@[to_dual trans_gt] alias Eq.trans_lt := lt_of_eq_of_lt

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

@[to_dual self]
theorem not_lt_iff_not_le_or_ge : ¬a < b ↔ ¬a ≤ b ∨ b ≤ a := by
  rw [lt_iff_le_not_ge, Classical.not_and_iff_not_or_not, Classical.not_not]

-- Unnecessary brackets are here for readability
@[to_dual self]
lemma not_lt_iff_le_imp_ge : ¬ a < b ↔ (a ≤ b → b ≤ a) := by
  simp [not_lt_iff_not_le_or_ge, or_iff_not_imp_left]

@[simp]
lemma lt_self_iff_false (x : α) : x < x ↔ False := ⟨lt_irrefl x, False.elim⟩

@[to_dual ge_trans'] alias le_trans' := ge_trans
@[to_dual gt_trans'] alias lt_trans' := gt_trans
@[to_dual trans'] alias LE.le.trans := le_trans
@[to_dual trans'] alias LT.lt.trans := lt_trans
@[to_dual trans_lt'] alias LE.le.trans_lt := lt_of_le_of_lt
@[to_dual trans_le'] alias LT.lt.trans_le := lt_of_lt_of_le

@[to_dual self] alias LE.le.lt_of_not_ge := lt_of_le_not_ge
@[to_dual self] alias LT.lt.le := le_of_lt
@[to_dual self] alias LT.lt.asymm := lt_asymm
@[to_dual self] alias LT.lt.not_gt := lt_asymm

@[to_dual ne'] alias LT.lt.ne := ne_of_lt
@[to_dual ge] alias Eq.le := le_of_eq

protected lemma LT.lt.false : a < a → False := lt_irrefl a

@[to_dual not_gt] protected lemma Eq.not_lt (hab : a = b) : ¬a < b := fun h' ↦ h'.ne hab

@[to_dual ne_of_not_ge]
theorem ne_of_not_le (h : ¬a ≤ b) : a ≠ b := fun hab ↦ h (le_of_eq hab)

@[simp, to_dual self]
lemma le_of_subsingleton [Subsingleton α] : a ≤ b := (Subsingleton.elim a b).le

-- Making this a @[simp] lemma causes confluence problems downstream.
@[nontriviality, to_dual self]
lemma not_lt_of_subsingleton [Subsingleton α] : ¬a < b := (Subsingleton.elim a b).not_lt

@[to_dual le_of_forall_ge]
theorem le_of_forall_le (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b := H _ le_rfl

@[to_dual forall_ge_iff_le]
theorem forall_le_iff_le : (∀ ⦃c⦄, c ≤ a → c ≤ b) ↔ a ≤ b :=
  ⟨le_of_forall_le, fun h _ hca ↦ le_trans hca h⟩

/-- monotonicity of `≤` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
theorem le_imp_le_of_le_of_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a ≤ b → c ≤ d :=
  fun hab ↦ (h₁.trans hab).trans h₂

/-- monotonicity of `<` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
theorem lt_imp_lt_of_le_of_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a < b → c < d :=
  fun hab ↦ (h₁.trans_lt hab).trans_le h₂

namespace Mathlib.Tactic.GCongr

/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[gcongr_forward] meta def exactLeOfLt : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``le_of_lt #[h])

end Mathlib.Tactic.GCongr

end Preorder

/-! ### Partial order -/

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual lt_of_le'] -- TODO: should be called `gt_of_ge`
theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_ne

namespace LE.le

@[to_dual antisymm'] alias antisymm := le_antisymm
@[to_dual lt_of_ne'] alias lt_of_ne := lt_of_le_of_ne

@[to_dual lt_iff_ne']
theorem lt_iff_ne (h : a ≤ b) : a < b ↔ a ≠ b := ⟨ne_of_lt, h.lt_of_ne⟩

@[to_dual not_lt_iff_eq']
theorem not_lt_iff_eq (h : a ≤ b) : ¬a < b ↔ a = b := h.lt_iff_ne.not_left

@[to_dual ge_iff_eq']
theorem ge_iff_eq (h : a ≤ b) : b ≤ a ↔ a = b := ⟨h.antisymm, Eq.ge⟩

end LE.le

-- Unnecessary brackets are here for readability
@[to_dual le_imp_eq_iff_le_imp_ge']
lemma le_imp_eq_iff_le_imp_ge : (a ≤ b → a = b) ↔ (a ≤ b → b ≤ a) where
  mp h hab := (h hab).ge
  mpr h hab := hab.antisymm (h hab)

-- See Note [decidable namespace]
@[to_dual le_iff_eq_or_lt']
protected theorem Decidable.le_iff_eq_or_lt [DecidableLE α] : a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eq.trans or_comm

@[to_dual le_iff_eq_or_lt']
theorem le_iff_eq_or_lt : a ≤ b ↔ a = b ∨ a < b := le_iff_lt_or_eq.trans or_comm

@[to_dual lt_iff_le_and_ne']
theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ ↦ h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
@[to_dual eq_iff_ge_not_gt]
protected theorem Decidable.eq_iff_le_not_lt [DecidableLE α] : a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h ↦ ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ ↦
    h₁.antisymm <| Decidable.byContradiction fun h₃ ↦ h₂ (h₁.lt_of_not_ge h₃)⟩

@[to_dual eq_iff_ge_not_gt]
theorem eq_iff_le_not_lt : a = b ↔ a ≤ b ∧ ¬a < b := open scoped Classical in
  Decidable.eq_iff_le_not_lt

-- See Note [decidable namespace]
@[to_dual eq_or_lt_of_le']
protected theorem Decidable.eq_or_lt_of_le [DecidableLE α] (h : a ≤ b) : a = b ∨ a < b :=
  (Decidable.lt_or_eq_of_le h).symm

@[to_dual eq_or_lt_of_le']
theorem eq_or_lt_of_le (h : a ≤ b) : a = b ∨ a < b := (lt_or_eq_of_le h).symm

@[to_dual lt_or_eq_dec'] alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le
@[to_dual eq_or_lt_dec'] alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le
@[to_dual lt_or_eq'] alias LE.le.lt_or_eq := lt_or_eq_of_le
@[to_dual eq_or_lt'] alias LE.le.eq_or_lt := eq_or_lt_of_le

@[to_dual eq_of_le_of_not_lt']
theorem eq_of_le_of_not_lt (h₁ : a ≤ b) (h₂ : ¬a < b) : a = b := h₁.eq_or_lt.resolve_right h₂

@[to_dual eq_of_not_lt'] alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt

@[to_dual ge_iff_gt]
theorem Ne.le_iff_lt (h : a ≠ b) : a ≤ b ↔ a < b := ⟨fun h' ↦ lt_of_le_of_ne h' h, fun h ↦ h.le⟩

@[to_dual not_ge_or_not_le]
theorem Ne.not_le_or_not_ge (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a := not_and_or.1 <| le_antisymm_iff.not.1 h

-- See Note [decidable namespace]
@[to_dual ne_iff_gt_iff_ge]
protected theorem Decidable.ne_iff_lt_iff_le [DecidableEq α] : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h ↦ Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h ↦ ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[to_dual (attr := simp) ne_iff_gt_iff_ge]
theorem ne_iff_lt_iff_le : (a ≠ b ↔ a < b) ↔ a ≤ b := open scoped Classical in
  Decidable.ne_iff_lt_iff_le

@[to_dual eq_of_forall_ge_iff]
lemma eq_of_forall_le_iff (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

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

@[to_dual lt_or_ge]
lemma gt_or_le (h : a ≤ b) (c : α) : a < c ∨ c ≤ b := (lt_or_ge a c).imp id h.trans'

@[to_dual le_or_gt]
lemma ge_or_lt (h : a ≤ b) (c : α) : a ≤ c ∨ c < b := (le_or_gt a c).imp id h.trans_lt'

@[to_dual le_or_ge]
lemma ge_or_le (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b := (h.gt_or_le c).imp le_of_lt id

end LE.le

namespace LT.lt

@[to_dual lt_or_gt]
lemma gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b := (le_or_gt b c).imp h.trans_le id

end LT.lt

@[to_dual gt_or_lt]
theorem Ne.lt_or_gt (h : a ≠ b) : a < b ∨ b < a :=
  lt_or_gt_of_ne h

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[to_dual lt_or_gt_iff_ne', simp]
theorem lt_or_lt_iff_ne : a < b ∨ b < a ↔ a ≠ b :=
  ne_iff_lt_or_gt.symm

@[to_dual not_lt_iff_eq_or_lt']
theorem not_lt_iff_eq_or_lt : ¬a < b ↔ a = b ∨ b < a :=
  not_lt.trans <| Decidable.le_iff_eq_or_lt.trans <| or_congr eq_comm Iff.rfl

@[to_dual exists_le_of_linear]
theorem exists_ge_of_linear (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

@[to_dual exists_forall_le_and]
lemma exists_forall_ge_and {p q : α → Prop} :
    (∃ i, ∀ j ≥ i, p j) → (∃ i, ∀ j ≥ i, q j) → ∃ i, ∀ j ≥ i, p j ∧ q j
  | ⟨a, ha⟩, ⟨b, hb⟩ =>
    let ⟨c, hac, hbc⟩ := exists_ge_of_linear a b
    ⟨c, fun _d hcd ↦ ⟨ha _ <| hac.trans hcd, hb _ <| hbc.trans hcd⟩⟩

@[to_dual le_of_forall_gt]
theorem le_of_forall_lt (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_gt fun h ↦ lt_irrefl _ (H _ h)

@[to_dual forall_gt_iff_le]
theorem forall_lt_iff_le : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_lt, fun h _ hca ↦ lt_of_lt_of_le hca h⟩

@[to_dual le_of_forall_gt_imp_ne]
theorem le_of_forall_lt_imp_ne (H : ∀ c < a, c ≠ b) : a ≤ b :=
  le_of_not_gt fun hb ↦ H b hb rfl

@[to_dual lt_of_forall_ge_imp_ne]
theorem lt_of_forall_le_imp_ne (H : ∀ c ≤ a, c ≠ b) : a < b :=
  lt_of_not_ge fun hb ↦ H b hb rfl

@[to_dual forall_gt_imp_ne_iff_le]
theorem forall_lt_imp_ne_iff_le : (∀ c < a, c ≠ b) ↔ a ≤ b :=
  ⟨le_of_forall_lt_imp_ne, fun ha _ hc ↦ (hc.trans_le ha).ne⟩

@[to_dual forall_ge_imp_ne_iff_lt]
theorem forall_le_imp_ne_iff_lt : (∀ c ≤ a, c ≠ b) ↔ a < b :=
  ⟨lt_of_forall_le_imp_ne, fun ha _ hc ↦ (hc.trans_lt ha).ne⟩

@[to_dual eq_of_forall_gt_iff]
theorem eq_of_forall_lt_iff (h : ∀ c, c < a ↔ c < b) : a = b :=
  (le_of_forall_lt fun _ ↦ (h _).1).antisymm <| le_of_forall_lt fun _ ↦ (h _).2

@[to_dual self (reorder := ltc gtc)]
lemma eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt {x y x' y' : α}
    (ltc : x < y ↔ x' < y') (gtc : y < x ↔ y' < x') :
    x = y ↔ x' = y' := by grind

/-! #### `min`/`max` recursors -/

section MinMaxRec
variable {p : α → Prop}

@[to_dual]
lemma min_rec (ha : a ≤ b → p a) (hb : b ≤ a → p b) : p (min a b) := by
  obtain hab | hba := le_total a b <;> simp [min_eq_left, min_eq_right, *]

@[to_dual]
lemma min_rec' (p : α → Prop) (ha : p a) (hb : p b) : p (min a b) :=
  min_rec (fun _ ↦ ha) fun _ ↦ hb

@[to_dual max_def_lt']
lemma min_def_lt (a b : α) : min a b = if a < b then a else b := by
  rw [min_comm, min_def, ← ite_not]; simp only [not_le]

@[to_dual min_def_lt']
lemma max_def_lt (a b : α) : max a b = if a < b then b else a := by
  rw [max_comm, max_def, ← ite_not]; simp only [not_le]

end MinMaxRec
end LinearOrder

/-! ### Implications -/

@[to_dual self]
lemma lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
  lt_of_not_ge fun h' ↦ (H h').not_gt h

@[to_dual self]
lemma le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

@[to_dual self]
lemma lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_ge.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_ge.symm

@[to_dual self]
lemma lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c := not_le.symm.trans <| (not_congr H).trans <| not_le

@[to_dual self]
lemma le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_le, fun H ↦ not_lt.symm.trans <| (not_congr H).trans <| not_lt⟩

/-- A symmetric relation implies two values are equal, when it implies they're less-equal. -/
lemma rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α → α → Prop) [Std.Symm r] {f : α → β}
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

@[to_dual self]
lemma Preorder.ext {A B : Preorder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y; exact H x y

@[to_dual self]
lemma PartialOrder.ext {A B : PartialOrder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by ext x y; exact H x y

@[to_dual self]
lemma PartialOrder.ext_lt {A B : PartialOrder α} (H : ∀ x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := by ext x y; rw [le_iff_lt_or_eq, @le_iff_lt_or_eq _ A, H]

@[to_dual self]
lemma LinearOrder.ext {A B : LinearOrder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by ext x y; exact H x y

@[to_dual self]
lemma LinearOrder.ext_lt {A B : LinearOrder α} (H : ∀ x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := LinearOrder.toPartialOrder_injective (PartialOrder.ext_lt H)

/-! ### `Compl` -/


instance Prop.instCompl : Compl Prop :=
  ⟨Not⟩

instance Pi.instCompl [∀ i, Compl (π i)] : Compl (∀ i, π i) :=
  ⟨fun x i ↦ (x i)ᶜ⟩

@[push ←]
theorem Pi.compl_def [∀ i, Compl (π i)] (x : ∀ i, π i) :
    xᶜ = fun i ↦ (x i)ᶜ :=
  rfl

@[simp]
theorem Pi.compl_apply [∀ i, Compl (π i)] (x : ∀ i, π i) (i : ι) :
    xᶜ i = (x i)ᶜ :=
  rfl

instance Std.Irrefl.compl (r : α → α → Prop) [Std.Irrefl r] : Std.Refl rᶜ :=
  ⟨@irrefl α r _⟩

instance Std.Refl.compl (r : α → α → Prop) [Std.Refl r] : Std.Irrefl rᶜ :=
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
  __ := (inferInstance : LE (∀ i, π i))
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
@[to_dual self (reorder := a b)]
def StrongLT [∀ i, LT (π i)] (a b : ∀ i, π i) : Prop :=
  ∀ i, a i < b i

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

variable [∀ i, Preorder (π i)] {a b c : ∀ i, π i}

@[to_dual self]
theorem le_of_strongLT (h : a ≺ b) : a ≤ b := fun _ ↦ (h _).le

@[to_dual self]
theorem lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b := by
  inhabit ι
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩

@[to_dual (reorder := hab hbc) strongLT_of_le_of_strongLT]
theorem strongLT_of_strongLT_of_le (hab : a ≺ b) (hbc : b ≤ c) : a ≺ c := fun _ ↦
  (hab _).trans_le <| hbc _

@[to_dual self] alias StrongLT.le := le_of_strongLT

@[to_dual self] alias StrongLT.lt := lt_of_strongLT

@[to_dual (reorder := hab hbc) LE.le.trans_strongLT]
alias StrongLT.trans_le := strongLT_of_strongLT_of_le

end Pi

section Function

variable [DecidableEq ι] [∀ i, Preorder (π i)] {x y : ∀ i, π i} {i : ι} {a b : π i}

@[to_dual update_le_iff]
theorem le_update_iff : x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ x j ≤ z

@[to_dual self]
theorem update_le_update_iff :
    Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp +contextual [update_le_iff]

@[simp, to_dual self]
theorem update_le_update_iff' : update x i a ≤ update x i b ↔ a ≤ b := by
  simp [update_le_update_iff]

@[simp, to_dual self]
theorem update_lt_update_iff : update x i a < update x i b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'

@[to_dual (attr := simp) update_le_self_iff]
theorem le_update_self_iff : x ≤ update x i a ↔ x i ≤ a := by simp [le_update_iff]

@[to_dual (attr := simp) update_lt_self_iff]
theorem lt_update_self_iff : x < update x i a ↔ x i < a := by simp [lt_iff_le_not_ge]

end Function

instance Pi.sdiff [∀ i, SDiff (π i)] : SDiff (∀ i, π i) :=
  ⟨fun x y i ↦ x i \ y i⟩

@[push ←]
theorem Pi.sdiff_def [∀ i, SDiff (π i)] (x y : ∀ i, π i) :
    x \ y = fun i ↦ x i \ y i :=
  rfl

@[simp]
theorem Pi.sdiff_apply [∀ i, SDiff (π i)] (x y : ∀ i, π i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl

namespace Function

variable [Preorder α] [Nonempty β] {a b : α}

@[simp, to_dual self]
theorem const_le_const : const β a ≤ const β b ↔ a ≤ b := by simp [Pi.le_def]

@[simp, to_dual self]
theorem const_lt_const : const β a < const β b ↔ a < b := by simpa [Pi.lt_def] using le_of_lt

end Function

/-! ### Pullbacks of order instances -/

/-- Pull back a `Preorder` instance along an injective function.

See note [reducible non-instances]. -/
@[to_dual self]
abbrev Function.Injective.preorder [Preorder β] [LE α] [LT α] (f : α → β)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    Preorder α where
  le_refl _ := le.1 <| le_refl _
  le_trans _ _ _ h₁ h₂ := le.1 <| le_trans (le.2 h₁) (le.2 h₂)
  lt_iff_le_not_ge _ _ := by
    rw [← le, ← le, ← lt, lt_iff_le_not_ge]

/-- Pull back a `PartialOrder` instance along an injective function.

See note [reducible non-instances]. -/
@[to_dual self]
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
  fast_instance% Function.Injective.partialOrder f inj .rfl .rfl

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
@[to_dual self (reorder := 4 5, hsup hinf)]
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
@[to_dual self (reorder := 4 5, hsup hinf)]
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

@[simp, gcongr, to_dual self]
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[simp, gcongr, to_dual self]
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl

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

@[to_dual self]
instance instDecidableLE [Decidable (x.1 ≤ y.1)] [Decidable (x.2 ≤ y.2)] : Decidable (x ≤ y) :=
  inferInstanceAs <| Decidable (x.1 ≤ y.1 ∧ x.2 ≤ y.2)

@[to_dual self] lemma le_def : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := .rfl

@[simp, to_dual self] lemma mk_le_mk : (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂ := .rfl

@[gcongr, to_dual self]
lemma GCongr.mk_le_mk (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : (a₁, b₁) ≤ (a₂, b₂) := ⟨ha, hb⟩

@[simp, to_dual self] lemma swap_le_swap : x.swap ≤ y.swap ↔ x ≤ y := and_comm

@[to_dual (attr := simp) mk_le_swap]
lemma swap_le_mk : x.swap ≤ (b, a) ↔ x ≤ (a, b) := and_comm

end LE

section Preorder

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance : Preorder (α × β) where
  __ := (inferInstance : LE (α × β))
  le_refl := fun ⟨a, b⟩ ↦ ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ ↦ ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp, to_dual self]
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

@[to_dual (attr := simp) mk_lt_swap]
lemma swap_lt_mk : x.swap < (b, a) ↔ x < (a, b) := by rw [← swap_lt_swap]; simp

@[gcongr, to_dual self]
theorem mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rfl

@[gcongr, to_dual self]
theorem mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rfl

@[gcongr, to_dual self]
theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

@[gcongr, to_dual self]
theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

@[to_dual self]
theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases h₁ : y.1 ≤ x.1
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_ge h.1.2 fun h₂ ↦ h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_ge h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h ↦ h₁.not_ge h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, fun h ↦ h₂.not_ge h.2⟩

@[simp, to_dual self]
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

@[to_dual self]
protected lemma lt_of_lt_of_le (h₁ : x.1 < y.1) (h₂ : x.2 ≤ y.2) : x < y := by simp [lt_iff, *]

@[to_dual self]
protected lemma lt_of_le_of_lt (h₁ : x.1 ≤ y.1) (h₂ : x.2 < y.2) : x < y := by simp [lt_iff, *]

@[to_dual self]
lemma mk_lt_mk_of_lt_of_le (h₁ : a₁ < a₂) (h₂ : b₁ ≤ b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

@[to_dual self]
lemma mk_lt_mk_of_le_of_lt (h₁ : a₁ ≤ a₂) (h₂ : b₁ < b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

end Preorder

/-- The pointwise partial order on a product.
(The lexicographic ordering is defined in `Order.Lexicographic`, and the instances are
available via the type synonym `α ×ₗ β = α × β`.) -/
instance instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α × β) where
  __ := (inferInstance : Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ ↦ Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

end Prod

/-! ### Additional order classes -/

/-- An order is dense if there is an element between any pair of distinct comparable elements. -/
class DenselyOrdered (α : Type*) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

@[to_dual existing dense]
theorem DenselyOrdered.dense' [LT α] [DenselyOrdered α] :
    ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a < a₂ ∧ a₁ < a := by
  simp_rw [and_comm]; exact dense

@[to_dual exists_between']
theorem exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _


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

@[to_dual le_of_forall_lt_imp_le_of_dense]
theorem le_of_forall_gt_imp_ge_of_dense (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

@[to_dual forall_lt_imp_le_iff_le_of_dense]
lemma forall_gt_imp_ge_iff_le_of_dense : (∀ a, a₂ < a → a₁ ≤ a) ↔ a₁ ≤ a₂ :=
  ⟨le_of_forall_gt_imp_ge_of_dense, fun ha _a ha₂ ↦ ha.trans ha₂.le⟩

-- TODO: these two lemma names are the wrong way around
@[to_dual eq_of_le_of_forall_gt_imp_ge_of_dense]
lemma eq_of_le_of_forall_lt_imp_le_of_dense (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

end LinearOrder

@[to_dual dense_or_discrete']
theorem dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀ a < a₂, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h ↦
    ⟨fun a ha₁ ↦ le_of_not_gt fun ha₂ ↦ h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ ↦ le_of_not_gt fun ha₁ ↦ h ⟨a, ha₁, ha₂⟩⟩

/-- If a linear order has no elements `x < y < z`, then it has at most two elements. -/
@[to_dual self (reorder := h (x z, 4 5))]
lemma eq_or_eq_or_eq_of_forall_not_lt_lt [LinearOrder α]
    (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) (x y z : α) : x = y ∨ y = z ∨ x = z := by
  by_contra hne
  simp only [not_or, ← Ne.eq_def] at hne
  rcases hne.1.lt_or_gt with h₁ | h₁ <;>
  rcases hne.2.1.lt_or_gt with h₂ | h₂ <;>
  rcases hne.2.2.lt_or_gt with h₃ | h₃
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]

/-- Construct the trivial linear order on any type with at most one element. -/
abbrev LinearOrder.ofSubsingleton {α : Type*} [Subsingleton α] : LinearOrder α where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans x y z _ _ := trivial
  le_antisymm x y _ _ := Subsingleton.elim x y
  le_total _ _ := .inl trivial
  lt_iff_le_not_ge _ _ := by simp
  toDecidableLE _ _ := instDecidableTrue

instance : LinearOrder Empty := .ofSubsingleton
instance : LinearOrder PEmpty := .ofSubsingleton

namespace PUnit

variable (a b : PUnit)

instance instLinearOrder : LinearOrder PUnit := .ofSubsingleton

@[to_dual]
theorem max_eq : max a b = unit :=
  rfl

@[to_dual self]
protected theorem le : a ≤ b :=
  trivial

@[to_dual self]
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

/-- Type synonym to create an instance of `LinearOrder` from a `PartialOrder` and `IsTotal α (≤)`.

**Do not use this**: instead, build a `LinearOrder` instance directly. -/
@[deprecated "build a `LinearOrder` instance directly instead" (since := "2025-10-28")]
def AsLinearOrder (α : Type*) :=
  α

set_option linter.deprecated false in
@[deprecated "`AsLinearOrder` is deprecated" (since := "2025-10-28")]
instance [Inhabited α] : Inhabited (AsLinearOrder α) :=
  ⟨(default : α)⟩

set_option linter.deprecated false in
@[deprecated "`AsLinearOrder` is deprecated" (since := "2025-10-28")]
noncomputable instance AsLinearOrder.linearOrder [PartialOrder α] [IsTotal α (· ≤ ·)] :
    LinearOrder (AsLinearOrder α) where
  __ := (inferInstance : PartialOrder α)
  le_total := @total_of α (· ≤ ·) _
  toDecidableLE := Classical.decRel _
