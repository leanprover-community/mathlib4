/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module order.basic
! leanprover-community/mathlib commit 70d50ecfd4900dd6d328da39ab7ebd516abe4025
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Subtype
import Mathlib.Tactic.Spread

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `OrderDual α` : A type synonym reversing the meaning of all inequalities, with notation `αᵒᵈ`.
* `AsLinearOrder α`: A type synonym to promote `PartialOrder α` to `LinearOrder α` using
  `IsTotal α (≤)`.

### Transfering orders

- `Order.Preimage`, `Preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `PartialOrder.lift`, `LinearOrder.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `HasSup`: type class for the `⊔` notation
* `HasInf`: type class for the `⊓` notation
* `HasCompl`: type class for the `ᶜ` notation
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

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

section Preorder

variable [Preorder α] {a b c : α}

theorem le_trans' : b ≤ c → a ≤ b → a ≤ c :=
  flip le_trans

theorem lt_trans' : b < c → a < b → a < c :=
  flip lt_trans

theorem lt_of_le_of_lt' : b ≤ c → a < b → a < c :=
  flip lt_of_lt_of_le

theorem lt_of_lt_of_le' : b < c → a ≤ b → a < c :=
  flip lt_of_le_of_lt

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem ge_antisymm : a ≤ b → b ≤ a → b = a :=
  flip le_antisymm

theorem lt_of_le_of_ne' : a ≤ b → b ≠ a → a < b := fun h₁ h₂ ↦ lt_of_le_of_ne h₁ h₂.symm

theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_ne

theorem Ne.lt_of_le' : b ≠ a → a ≤ b → a < b :=
  flip lt_of_le_of_ne'

end PartialOrder

attribute [simp] le_refl

attribute [ext] LE

alias le_trans ← LE.le.trans

alias le_trans' ← LE.le.trans'

alias lt_of_le_of_lt ← LE.le.trans_lt

alias lt_of_le_of_lt' ← LE.le.trans_lt'

alias le_antisymm ← LE.le.antisymm

alias ge_antisymm ← LE.le.antisymm'

alias lt_of_le_of_ne ← LE.le.lt_of_ne

alias lt_of_le_of_ne' ← LE.le.lt_of_ne'

alias lt_of_le_not_le ← LE.le.lt_of_not_le

alias lt_or_eq_of_le ← LE.le.lt_or_eq

alias Decidable.lt_or_eq_of_le ← LE.le.lt_or_eq_dec

alias le_of_lt ← LT.lt.le

alias lt_trans ← LT.lt.trans

alias lt_trans' ← LT.lt.trans'

alias lt_of_lt_of_le ← LT.lt.trans_le

alias lt_of_lt_of_le' ← LT.lt.trans_le'

alias ne_of_lt ← LT.lt.ne
#align has_lt.lt.ne LT.lt.ne

alias lt_asymm ← LT.lt.asymm LT.lt.not_lt

alias le_of_eq ← Eq.le

-- Porting note: no `decidable_classical` linter
-- attribute [nolint decidable_classical] LE.le.lt_or_eq_dec

section

variable [Preorder α] {a b c : α}

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rfl : a ≤ a :=
  le_refl a

@[simp]
theorem lt_self_iff_false (x : α) : x < x ↔ False :=
  ⟨lt_irrefl x, False.elim⟩

theorem le_of_le_of_eq (hab : a ≤ b) (hbc : b = c) : a ≤ c :=
  hab.trans hbc.le

theorem le_of_eq_of_le (hab : a = b) (hbc : b ≤ c) : a ≤ c :=
  hab.le.trans hbc

theorem lt_of_lt_of_eq (hab : a < b) (hbc : b = c) : a < c :=
  hab.trans_le hbc.le

theorem lt_of_eq_of_lt (hab : a = b) (hbc : b < c) : a < c :=
  hab.le.trans_lt hbc

theorem le_of_le_of_eq' : b ≤ c → a = b → a ≤ c :=
  flip le_of_eq_of_le

theorem le_of_eq_of_le' : b = c → a ≤ b → a ≤ c :=
  flip le_of_le_of_eq

theorem lt_of_lt_of_eq' : b < c → a = b → a < c :=
  flip lt_of_eq_of_lt

theorem lt_of_eq_of_lt' : b = c → a < b → a < c :=
  flip lt_of_lt_of_eq

alias le_of_le_of_eq ← LE.le.trans_eq

alias le_of_le_of_eq' ← LE.le.trans_eq'

alias lt_of_lt_of_eq ← LT.lt.trans_eq

alias lt_of_lt_of_eq' ← LT.lt.trans_eq'

alias le_of_eq_of_le ← Eq.trans_le

alias le_of_eq_of_le' ← Eq.trans_ge

alias lt_of_eq_of_lt ← Eq.trans_lt

alias lt_of_eq_of_lt' ← Eq.trans_gt

end

namespace Eq

variable [Preorder α] {x y z : α}

/-- If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`, because `le` is used
almost exclusively in mathlib. -/
protected theorem ge (h : x = y) : y ≤ x :=
  h.symm.le

theorem not_lt (h : x = y) : ¬x < y := fun h' ↦ h'.ne h

theorem not_gt (h : x = y) : ¬y < x :=
  h.symm.not_lt

end Eq

namespace LE.le

protected theorem ge [LE α] {x y : α} (h : x ≤ y) : y ≥ x :=
  h

section partial_order
variable [PartialOrder α] {a b : α}

lemma lt_iff_ne (h : a ≤ b) : a < b ↔ a ≠ b := ⟨fun h ↦ h.ne, h.lt_of_ne⟩
lemma gt_iff_ne (h : a ≤ b) : a < b ↔ b ≠ a := ⟨fun h ↦ h.ne.symm, h.lt_of_ne'⟩
lemma not_lt_iff_eq (h : a ≤ b) : ¬ a < b ↔ a = b := h.lt_iff_ne.not_left
lemma not_gt_iff_eq (h : a ≤ b) : ¬ a < b ↔ b = a := h.gt_iff_ne.not_left

lemma le_iff_eq (h : a ≤ b) : b ≤ a ↔ b = a := ⟨fun h' ↦ h'.antisymm h, Eq.le⟩
lemma ge_iff_eq (h : a ≤ b) : b ≤ a ↔ a = b := ⟨h.antisymm, Eq.ge⟩

end partial_order

theorem lt_or_le [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
  ((lt_or_ge a c).imp id) fun hc ↦ le_trans hc h

theorem le_or_lt [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
  ((le_or_gt a c).imp id) fun hc ↦ lt_of_lt_of_le hc h

theorem le_or_le [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
  (h.le_or_lt c).elim Or.inl fun h ↦ Or.inr <| le_of_lt h

end LE.le

namespace LT.lt

protected theorem gt [LT α] {x y : α} (h : x < y) : y > x :=
  h

protected theorem false [Preorder α] {x : α} : x < x → False :=
  lt_irrefl x

theorem ne' [Preorder α] {x y : α} (h : x < y) : y ≠ x :=
  h.ne.symm

theorem lt_or_lt [LinearOrder α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
  (lt_or_ge z y).elim Or.inr fun hz ↦ Or.inl <| h.trans_le hz

end LT.lt

protected theorem ge.le [LE α] {x y : α} (h : x ≥ y) : y ≤ x :=
  h

protected theorem gt.lt [LT α] {x y : α} (h : x > y) : y < x :=
  h

theorem ge_of_eq [Preorder α] {a b : α} (h : a = b) : a ≥ b :=
  h.ge

theorem ge_iff_le [LE α] {a b : α} : a ≥ b ↔ b ≤ a :=
  Iff.rfl

theorem gt_iff_lt [LT α] {a b : α} : a > b ↔ b < a :=
  Iff.rfl

theorem not_le_of_lt [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a :=
  (le_not_le_of_lt h).right

alias not_le_of_lt ← LT.lt.not_le

theorem not_lt_of_le [Preorder α] {a b : α} (h : a ≤ b) : ¬b < a := fun hba ↦ hba.not_le h

alias not_lt_of_le ← LE.le.not_lt

theorem ne_of_not_le [Preorder α] {a b : α} (h : ¬a ≤ b) : a ≠ b := fun hab ↦ h (le_of_eq hab)

-- See Note [decidable namespace]
protected theorem Decidable.le_iff_eq_or_lt [PartialOrder α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eq.trans or_comm

theorem le_iff_eq_or_lt [PartialOrder α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
  le_iff_lt_or_eq.trans or_comm

theorem lt_iff_le_and_ne [PartialOrder α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ ↦ h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
protected theorem Decidable.eq_iff_le_not_lt [PartialOrder α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h ↦ ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ ↦
    h₁.antisymm <| Decidable.by_contradiction fun h₃ ↦ h₂ (h₁.lt_of_not_le h₃)⟩

theorem eq_iff_le_not_lt [PartialOrder α] {a b : α} : a = b ↔ a ≤ b ∧ ¬a < b :=
  haveI := Classical.dec
  Decidable.eq_iff_le_not_lt

theorem eq_or_lt_of_le [PartialOrder α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
  h.lt_or_eq.symm

theorem eq_or_gt_of_le [PartialOrder α] {a b : α} (h : a ≤ b) : b = a ∨ a < b :=
  h.lt_or_eq.symm.imp Eq.symm id

alias Decidable.eq_or_lt_of_le ← LE.le.eq_or_lt_dec

alias eq_or_lt_of_le ← LE.le.eq_or_lt

alias eq_or_gt_of_le ← LE.le.eq_or_gt

-- Porting note: no `decidable_classical` linter
-- attribute [nolint decidable_classical] LE.le.eq_or_lt_dec

theorem eq_of_le_of_not_lt [PartialOrder α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : a = b :=
  hab.eq_or_lt.resolve_right hba

theorem eq_of_ge_of_not_gt [PartialOrder α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : b = a :=
  (hab.eq_or_lt.resolve_right hba).symm

alias eq_of_le_of_not_lt ← LE.le.eq_of_not_lt

alias eq_of_ge_of_not_gt ← LE.le.eq_of_not_gt

theorem Ne.le_iff_lt [PartialOrder α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
  ⟨fun h' ↦ lt_of_le_of_ne h' h, fun h ↦ h.le⟩

theorem Ne.not_le_or_not_le [PartialOrder α] {a b : α} (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a :=
  not_and_or.1 <| le_antisymm_iff.not.1 h

protected theorem Decidable.ne_iff_lt_iff_le [PartialOrder α] [DecidableEq α] {a b : α} :
    (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h ↦ Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h ↦ ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[simp]
theorem ne_iff_lt_iff_le [PartialOrder α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  haveI := Classical.dec
  Decidable.ne_iff_lt_iff_le

theorem lt_of_not_le [LinearOrder α] {a b : α} (h : ¬b ≤ a) : a < b :=
  ((le_total _ _).resolve_right h).lt_of_not_le h

theorem lt_iff_not_le [LinearOrder α] {x y : α} : x < y ↔ ¬y ≤ x :=
  ⟨not_le_of_lt, lt_of_not_le⟩

theorem Ne.lt_or_lt [LinearOrder α] {x y : α} (h : x ≠ y) : x < y ∨ y < x :=
  lt_or_gt_of_ne h

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[simp]
theorem lt_or_lt_iff_ne [LinearOrder α] {x y : α} : x < y ∨ y < x ↔ x ≠ y :=
  ne_iff_lt_or_gt.symm

theorem not_lt_iff_eq_or_lt [LinearOrder α] {a b : α} : ¬a < b ↔ a = b ∨ b < a :=
  not_lt.trans <| Decidable.le_iff_eq_or_lt.trans <| or_congr eq_comm Iff.rfl

theorem exists_ge_of_linear [LinearOrder α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

theorem lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
  lt_of_not_le fun h' ↦ (H h').not_lt h

theorem le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

theorem lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_le.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_le.symm

theorem lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
  not_le.symm.trans <| (not_congr H).trans <| not_le

theorem le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_le, fun H ↦ not_lt.symm.trans <| (not_congr H).trans <| not_lt⟩

theorem eq_of_forall_le_iff [PartialOrder α] {a b : α} (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

theorem le_of_forall_le [Preorder α] {a b : α} (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
  H _ le_rfl

theorem le_of_forall_le' [Preorder α] {a b : α} (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
  H _ le_rfl

theorem le_of_forall_lt [LinearOrder α] {a b : α} (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_lt fun h ↦ lt_irrefl _ (H _ h)

theorem forall_lt_iff_le [LinearOrder α] {a b : α} : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_lt, fun h _ hca ↦ lt_of_lt_of_le hca h⟩

theorem le_of_forall_lt' [LinearOrder α] {a b : α} (H : ∀ c, a < c → b < c) : b ≤ a :=
  le_of_not_lt fun h ↦ lt_irrefl _ (H _ h)

theorem forall_lt_iff_le' [LinearOrder α] {a b : α} : (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
  ⟨le_of_forall_lt', fun h _ hac ↦ lt_of_le_of_lt h hac⟩

theorem eq_of_forall_ge_iff [PartialOrder α] {a b : α} (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  ((H _).2 le_rfl).antisymm ((H _).1 le_rfl)

theorem eq_of_forall_lt_iff [LinearOrder α] {a b : α} (h : ∀ c, c < a ↔ c < b) : a = b :=
  (le_of_forall_lt fun _ ↦ (h _).1).antisymm <| le_of_forall_lt fun _ ↦ (h _).2

theorem eq_of_forall_gt_iff [LinearOrder α] {a b : α} (h : ∀ c, a < c ↔ b < c) : a = b :=
  (le_of_forall_lt' fun _ ↦ (h _).2).antisymm <| le_of_forall_lt' fun _ ↦ (h _).1

/-- A symmetric relation implies two values are equal, when it implies they're less-equal.  -/
theorem rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α → α → Prop) [IsSymm α r] {f : α → β}
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} : r a b → f a = f b := fun hab ↦
  le_antisymm (h a b hab) (h b a <| symm hab)

/-- monotonicity of `≤` with respect to `→` -/
theorem le_implies_le_of_le_of_le {a b c d : α} [Preorder α] (hca : c ≤ a) (hbd : b ≤ d) :
    a ≤ b → c ≤ d :=
  fun hab ↦ (hca.trans hab).trans hbd

section PartialOrder
variable [PartialOrder α]

/-- To prove commutativity of a binary operation `○`, we only to check `a ○ b ≤ b ○ a` for all `a`,
`b`. -/
lemma commutative_of_le {f : β → β → α} (comm : ∀ a b, f a b ≤ f b a) : ∀ a b, f a b = f b a :=
fun _ _ ↦ (comm _ _).antisymm $ comm _ _

/-- To prove associativity of a commutative binary operation `○`, we only to check
`(a ○ b) ○ c ≤ a ○ (b ○ c)` for all `a`, `b`, `c`. -/
lemma associative_of_commutative_of_le  {f : α → α → α} (comm : Commutative f)
  (assoc : ∀ a b c, f (f a b) c ≤ f a (f b c)) :
  Associative f :=
fun a b c ↦ le_antisymm (assoc _ _ _) $ by rw [comm, comm b, comm _ c, comm a]; exact assoc _ _ _

end PartialOrder

@[ext]
theorem Preorder.toLE_injective {α : Type _} : Function.Injective (@Preorder.toLE α) :=
  fun A B h ↦ match A, B with
  | { lt := A_lt, lt_iff_le_not_le := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_le := B_iff, .. } => by
    cases h
    have : A_lt = B_lt := by
      funext a b
      show (LT.mk A_lt).lt a b = (LT.mk B_lt).lt a b
      rw [A_iff, B_iff]
    cases this
    congr
#align preorder.to_has_le_injective Preorder.toLE_injective

@[ext]
theorem PartialOrder.toPreorder_injective {α : Type _} :
    Function.Injective (@PartialOrder.toPreorder α) :=
  fun A B h ↦ by
  cases A
  cases B
  cases h
  congr
#align partial_order.to_preorder_injective PartialOrder.toPreorder_injective

@[ext]
theorem LinearOrder.toPartialOrder_injective {α : Type _} :
    Function.Injective (@LinearOrder.toPartialOrder α) :=
  fun A B h ↦ match A, B with
  | { le := A_le, lt := A_lt, decidable_le := A_decidable_le,
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def, .. },
    { le := B_le, lt := B_lt, decidable_le := B_decidable_le,
      min := B_min, max := B_max, min_def := B_min_def, max_def := B_max_def, .. } => by
    cases h
    obtain rfl : A_decidable_le = B_decidable_le := Subsingleton.elim _ _
    have : A_min = B_min := by
      funext a b
      exact (A_min_def _ _).trans (B_min_def _ _).symm
    cases this
    have : A_max = B_max := by
      funext a b
      exact (A_max_def _ _).trans (B_max_def _ _).symm
    cases this
    congr <;> exact Subsingleton.elim _ _
#align linear_order.to_partial_order_injective LinearOrder.toPartialOrder_injective

theorem Preorder.ext {α} {A B : Preorder α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y
  exact H x y

theorem PartialOrder.ext {α} {A B : PartialOrder α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y
  exact H x y

theorem LinearOrder.ext {α} {A B : LinearOrder α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y
  exact H x y

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `RelEmbedding` (assuming `f`
is injective). -/
@[simp]
def Order.Preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop :=
  s (f x) (f y)

@[inherit_doc]
infixl:80 " ⁻¹'o " => Order.Preimage

/-- The preimage of a decidable order is decidable. -/
instance Order.Preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : DecidableRel s] :
    DecidableRel (f ⁻¹'o s) :=
  fun _ _ ↦ H _ _

/-! ### Order dual -/


/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
def OrderDual (α : Type _) : Type _ :=
  α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type _) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type _) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type _) [LE α] : LE αᵒᵈ :=
  ⟨fun a b => @LE.le α _ b a⟩

instance (α : Type _) [LT α] : LT αᵒᵈ :=
  ⟨fun a b => @LT.lt α _ b a⟩

instance preorder (α : Type _) [Preorder α] : Preorder αᵒᵈ where
  le_refl := fun _ ↦ le_refl _
  le_trans := fun _ _ _ hab hbc ↦ hbc.trans hab
  lt_iff_le_not_le := fun _ _ ↦ lt_iff_le_not_le

instance partialOrder (α : Type _) [PartialOrder α] : PartialOrder αᵒᵈ where
  __ := inferInstanceAs (Preorder αᵒᵈ)
  le_antisymm := fun a b hab hba ↦ @le_antisymm α _ a b hba hab

instance linearOrder (α : Type _) [LinearOrder α] : LinearOrder αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  le_total     := λ a b : α => le_total b a
  max := fun a b ↦ (min a b : α)
  min := fun a b ↦ (max a b : α)
  min_def := fun a b ↦ show (max .. : α) = _ by rw [max_comm, max_def]; rfl
  max_def := fun a b ↦ show (min .. : α) = _ by rw [min_comm, min_def]; rfl
  decidable_le := (inferInstance : DecidableRel (λ a b : α => b ≤ a))
  decidable_lt := (inferInstance : DecidableRel (λ a b : α => b < a))
#align order_dual.linear_order OrderDual.linearOrder

instance : ∀ [Inhabited α], Inhabited αᵒᵈ := λ [x: Inhabited α] => x


theorem Preorder.dual_dual (α : Type _) [H : Preorder α] : OrderDual.preorder αᵒᵈ = H :=
  Preorder.ext fun _ _ ↦ Iff.rfl

theorem partialOrder.dual_dual (α : Type _) [H : PartialOrder α] :
    OrderDual.partialOrder αᵒᵈ = H :=
  PartialOrder.ext fun _ _ ↦ Iff.rfl

theorem linearOrder.dual_dual (α : Type _) [H : LinearOrder α] : OrderDual.linearOrder αᵒᵈ = H :=
  LinearOrder.ext fun _ _ ↦ Iff.rfl

end OrderDual

/-! ### `HasCompl` -/


/-- Set / lattice complement -/
@[notation_class]
class HasCompl (α : Type _) where
  /-- Set / lattice complement -/
  compl : α → α

export HasCompl (compl)

@[inherit_doc]
postfix:999 "ᶜ" => compl

instance : HasCompl Prop :=
  ⟨Not⟩

instance {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] : HasCompl (∀ i, α i) :=
  ⟨fun x i ↦ x iᶜ⟩

theorem Pi.compl_def {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) :
    xᶜ = fun i ↦ x iᶜ :=
  rfl

@[simp]
theorem Pi.compl_apply {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) (i : ι) :
    (xᶜ) i = x iᶜ :=
  rfl

instance (r) [IsIrrefl α r] : IsRefl α (rᶜ) :=
  ⟨@irrefl α r _⟩

instance (r) [IsRefl α r] : IsIrrefl α (rᶜ) :=
  ⟨fun a ↦ not_not_intro (refl a)⟩

/-! ### Order instances on the function space -/


instance {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] : LE (∀ i, α i) where
  le x y := ∀ i, x i ≤ y i

theorem Pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] {x y : ∀ i, α i} :
    x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl

instance {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] : Preorder (∀ i, α i) where
  __ := inferInstanceAs (LE (∀ i, α i))
  le_refl := fun a i ↦ le_refl (a i)
  le_trans := fun a b c h₁ h₂ i ↦ le_trans (h₁ i) (h₂ i)

theorem Pi.lt_def {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] {x y : ∀ i, α i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp (config := { contextual := true }) [lt_iff_le_not_le, Pi.le_def]

theorem le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] [DecidableEq ι]
    {x y : ∀ i, α i} {i : ι} {a : α i} :
    x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ x j ≤ z

theorem update_le_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] [DecidableEq ι]
    {x y : ∀ i, α i} {i : ι} {a : α i} :
    Function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ z ≤ y j

theorem update_le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] [DecidableEq ι]
    {x y : ∀ i, α i} {i : ι} {a b : α i} :
    Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp (config := { contextual := true }) [update_le_iff]

instance {ι : Type u} {α : ι → Type v} [∀ i, PartialOrder (α i)] :
    PartialOrder (∀ i, α i) where
  __ := inferInstanceAs (Preorder (∀ i, α i))
  le_antisymm := fun _ _ h1 h2 ↦ funext fun b ↦ (h1 b).antisymm (h2 b)

instance Pi.sdiff {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] : SDiff (∀ i, α i) :=
  ⟨fun x y i ↦ x i \ y i⟩

theorem Pi.sdiff_def {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] (x y : ∀ i, α i) :
    x \ y = fun i ↦ x i \ y i :=
  rfl

@[simp]
theorem Pi.sdiff_apply {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] (x y : ∀ i, α i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl

namespace Function
variable [Preorder α] [Nonempty β] {a b : α}

@[simp] lemma const_le_const : const β a ≤ const β b ↔ a ≤ b := by simp [Pi.le_def]
@[simp] lemma const_lt_const : const β a < const β b ↔ a < b := by
  simpa [Pi.lt_def] using le_of_lt (α := α)

end Function

/-! ### `min`/`max` recursors -/


section MinMaxRec

variable [LinearOrder α] {p : α → Prop} {x y : α}

theorem min_rec (hx : x ≤ y → p x) (hy : y ≤ x → p y) : p (min x y) :=
  (le_total x y).rec (fun h ↦ (min_eq_left h).symm.subst (hx h))
    fun h ↦ (min_eq_right h).symm.subst (hy h)

theorem max_rec (hx : y ≤ x → p x) (hy : x ≤ y → p y) : p (max x y) :=
  @min_rec αᵒᵈ _ _ _ _ hx hy

theorem min_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (min x y) :=
  min_rec (fun _ ↦ hx) fun _ ↦ hy

theorem max_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (max x y) :=
  max_rec (fun _ ↦ hx) fun _ ↦ hy

theorem min_def' (x y : α) : min x y = if x < y then x else y := by
  rw [min_comm, min_def, ← ite_not]
  simp only [not_le]

theorem max_def' (x y : α) : max x y = if y < x then x else y := by
  rw [max_def, ← ite_not]
  simp only [not_le]

end MinMaxRec

/-! ### `HasSup` and `HasInf` -/


/-- Typeclass for the `⊔` (`\lub`) notation -/
@[notation_class, ext]
class HasSup (α : Type u) where
  /-- Least upper bound (`\lub` notation) -/
  sup : α → α → α

/-- Typeclass for the `⊓` (`\glb`) notation -/
@[notation_class, ext]
class HasInf (α : Type u) where
  /-- Greatest lower bound (`\glb` notation) -/
  inf : α → α → α

@[inherit_doc]
infixl:68 " ⊔ " => HasSup.sup

@[inherit_doc]
infixl:69 " ⊓ " => HasInf.inf

/-! ### Lifts of order instances -/


/-- Transfer a `Preorder` on `β` to a `Preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible]
def Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α where
  le x y := f x ≤ f y
  le_refl _ := le_rfl
  le_trans _ _ _ := _root_.le_trans
  lt x y := f x < f y
  lt_iff_le_not_le _ _ := _root_.lt_iff_le_not_le

/-- Transfer a `PartialOrder` on `β` to a `PartialOrder` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible]
def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  { Preorder.lift f with le_antisymm := fun _ _ h₁ h₂ ↦ inj (h₁.antisymm h₂) }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[HasSup α]` and `[HasInf α]` as arguments, then uses
them for `max` and `min` fields. See `LinearOrder.lift'` for a version that autogenerates `min` and
`max` fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.lift {α β} [LinearOrder β] [HasSup α] [HasInf α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrder α :=
  { PartialOrder.lift f inj with
      le_total := fun x y ↦ le_total (f x) (f y)
      decidable_le := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
      decidable_lt := fun x y ↦ (inferInstance : Decidable (f x < f y))
      decidable_eq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff,
      min := (· ⊓ ·), max := (· ⊔ ·),
      min_def := by
        intros x y
        apply inj
        rw [apply_ite f]
        exact (hinf _ _).trans (min_def _ _)
      max_def := by
        intros x y
        apply inj
        rw [apply_ite f]
        exact (hsup _ _).trans (max_def _ _) }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `LinearOrder.lift`
for a version that takes `[HasSup α]` and `[HasInf α]`, then uses them as `max` and `min`.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.lift' {α β} [LinearOrder β] (f : α → β) (inj : Injective f) : LinearOrder α :=
  { PartialOrder.lift f inj with
      le_total     := λ x y => le_total (f x) (f y),
      toMin := minOfLe
      toMax := maxOfLe
      decidable_le := λ x y => (inferInstance : Decidable (f x ≤ f y))
      decidable_lt := λ x y => (inferInstance : Decidable (f x < f y))
      decidable_eq := λ _ _ => decidable_of_iff _ inj.eq_iff
  }

/-! ### Subtype of an order -/


namespace Subtype

instance le [LE α] {p : α → Prop} : LE (Subtype p) :=
  ⟨fun x y ↦ (x : α) ≤ y⟩

instance lt [LT α] {p : α → Prop} : LT (Subtype p) :=
  ⟨fun x y ↦ (x : α) < y⟩

@[simp]
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[simp]
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

-- Porting note: no `norm_cast` due to eagerly elaborated coercions
@[simp]
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl

-- Porting note: no `norm_cast` due to eagerly elaborated coercions
@[simp]
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl

instance preorder [Preorder α] (p : α → Prop) : Preorder (Subtype p) :=
  Preorder.lift (fun (a : Subtype p) ↦ (a : α))

instance partialOrder [PartialOrder α] (p : α → Prop) : PartialOrder (Subtype p) :=
  PartialOrder.lift (fun (a : Subtype p) ↦ (a : α)) Subtype.coe_injective

instance decidableLE [Preorder α] [h : @DecidableRel α (· ≤ ·)] {p : α → Prop} :
    @DecidableRel (Subtype p) (· ≤ ·) :=
  fun a b ↦ h a b

instance decidableLT [Preorder α] [h : @DecidableRel α (· < ·)] {p : α → Prop} :
    @DecidableRel (Subtype p) (· < ·) :=
  fun a b ↦ h a b

/-- A subtype of a linear order is a linear order. We explicitly give the proofs of decidable
equality and decidable order in order to ensure the decidability instances are all definitionally
equal. -/
instance linearOrder [LinearOrder α] (p : α → Prop) : LinearOrder (Subtype p) :=
  @LinearOrder.lift (Subtype p) _ _ ⟨fun x y ↦ ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y ↦ ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) ↦ (a : α))
    Subtype.coe_injective (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `Data.Prod.Lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod

instance (α : Type u) (β : Type v) [LE α] [LE β] : LE (α × β) :=
  ⟨fun p q ↦ p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

theorem le_def [LE α] [LE β] {x y : α × β} : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 :=
  Iff.rfl

@[simp]
theorem mk_le_mk [LE α] [LE β] {x₁ x₂ : α} {y₁ y₂ : β} : (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
  Iff.rfl

@[simp]
theorem swap_le_swap [LE α] [LE β] {x y : α × β} : x.swap ≤ y.swap ↔ x ≤ y :=
  and_comm

section Preorder

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance (α : Type u) (β : Type v) [Preorder α] [Preorder β] : Preorder (α × β) where
  __ := inferInstanceAs (LE (α × β))
  le_refl := fun ⟨a, b⟩ ↦ ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ ↦ ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp]
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

theorem mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rfl

theorem mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rfl

theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine' ⟨fun h ↦ _, _⟩
  · by_cases h₁:y.1 ≤ x.1
    · refine Or.inr ⟨h.1.1, LE.le.lt_of_not_le h.1.2 fun h₂ ↦ h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_le h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h ↦ h₁.not_le h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, fun h ↦ h₂.not_le h.2⟩

@[simp]
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

end Preorder

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in `Order.Lexicographic`, and the instances are
    available via the type synonym `α ×ₗ β = α × β`.) -/
instance (α : Type u) (β : Type v) [PartialOrder α] [PartialOrder β] : PartialOrder (α × β) where
  __ := inferInstanceAs (Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ ↦ Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

end Prod

/-! ### Additional order classes -/


/-- An order is dense if there is an element between any pair of distinct elements. -/
class DenselyOrdered (α : Type u) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

theorem exists_between [LT α] [DenselyOrdered α] : ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _

instance (α : Type u) [LT α] [h : DenselyOrdered α] : DenselyOrdered αᵒᵈ :=
  ⟨fun _ _ ha ↦ (@exists_between α _ h _ _ ha).imp fun _ ↦ And.symm⟩

theorem le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
    (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

theorem eq_of_le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_le_of_dense h₂) h₁

theorem le_of_forall_ge_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
    (h : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

theorem eq_of_le_of_forall_ge_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ = a₂ :=
  (le_of_forall_ge_of_dense h₂).antisymm h₁

theorem dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀ a < a₂, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h ↦
    ⟨fun a ha₁ ↦ le_of_not_gt fun ha₂ ↦ h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ ↦ le_of_not_gt fun ha₁ ↦ h ⟨a, ha₁, ha₂⟩⟩

namespace PUnit

variable (a b : PUnit.{u + 1})

-- Porting note: no `refine_struct` at time of port
instance : LinearOrder PUnit where
  le  := fun _ _ ↦ True
  lt  := fun _ _ ↦ False
  max := fun _ _ ↦ unit
  min := fun _ _ ↦ unit
  decidable_eq := inferInstance
  decidable_le := fun _ _ ↦ Decidable.isTrue trivial
  decidable_lt := fun _ _ ↦ Decidable.isFalse id
  le_refl     := by intros; trivial
  le_trans    := by intros; trivial
  le_total    := by intros; exact Or.inl trivial
  le_antisymm := by intros; rfl
  lt_iff_le_not_le := by simp only [not_true, and_false, iff_self, forall_const]

theorem max_eq : max a b = star :=
  rfl

theorem min_eq : min a b = star :=
  rfl

protected theorem le : a ≤ b :=
  le_refl _

theorem not_lt : ¬a < b := by
  simp only [lt_self_iff_false]



instance : DenselyOrdered PUnit :=
  ⟨fun _ _ h ↦ (not_lt _ _ h).elim⟩

end PUnit

section «Prop»

/-- Propositions form a complete boolean algebra, where the `≤` relation is given by implication. -/
instance : LE Prop :=
  ⟨fun p q ↦ p → q⟩

@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = (fun p q ↦ p → q) :=
  rfl

theorem subrelation_iff_le {r s : α → α → Prop} : Subrelation r s ↔ r ≤ s :=
  Iff.rfl

instance : PartialOrder Prop where
  __ := inferInstanceAs (LE Prop)
  le_refl := fun _ ↦ id
  le_trans := fun a b c f g ↦ g ∘ f
  le_antisymm := fun a b Hab Hba ↦ propext ⟨Hab, Hba⟩

end «Prop»

variable {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Linear order from a total partial order -/


/-- Type synonym to create an instance of `LinearOrder` from a `PartialOrder` and `IsTotal α (≤)` -/
def AsLinearOrder (α : Type u) :=
  α

instance {α} [Inhabited α] : Inhabited (AsLinearOrder α) :=
  ⟨(default : α)⟩

noncomputable instance {α} [PartialOrder α] [IsTotal α (· ≤ ·)] :
    LinearOrder (AsLinearOrder α) where
  __ := inferInstanceAs (PartialOrder α)
  le_total := @total_of α (· ≤ ·) _
  decidable_le := Classical.decRel _
  toMin := @minOfLe α _ (Classical.decRel _)
  toMax := @maxOfLe α _ (Classical.decRel _)
