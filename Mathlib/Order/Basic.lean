/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Prod
import Mathlib.Data.Subtype
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Zero
import Mathlib.Logic.Basic
import Mathlib.Tactic.Alias

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `order_dual α` : A type synonym reversing the meaning of all inequalities, with notation `αᵒᵈ`.
* (TODO) `as_linear_order α`: A type synonym to promote `PartialOrder α` to `LinearOrder α` using
  `is_total α (·≤·)`.

### Transfering orders

- `order.preimage`, `Preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `PartialOrder.lift`, `LinearOrder.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `Sup`: type class for the `⊔` notation
* `Inf`: type class for the `⊓` notation
* `ᶜ` notation for the Complement type class
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

section preorder
variable [Preorder α] {a b c : α}

lemma le_trans' : b ≤ c → a ≤ b → a ≤ c := flip le_trans
lemma lt_trans' : b < c → a < b → a < c := flip lt_trans
lemma lt_of_le_of_lt' : b ≤ c → a < b → a < c := flip lt_of_lt_of_le
lemma lt_of_lt_of_le' : b < c → a ≤ b → a < c := flip lt_of_le_of_lt

end preorder

section partial_order
variable [PartialOrder α] {a b : α}

lemma ge_antisymm : a ≤ b → b ≤ a → b = a := flip le_antisymm
lemma lt_of_le_of_ne' : a ≤ b → b ≠ a → a < b := λ h₁ h₂ => lt_of_le_of_ne h₁ h₂.symm
lemma NE.lt_of_le : a ≠ b → a ≤ b → a < b := flip lt_of_le_of_ne
lemma NE.lt_of_le' : b ≠ a → a ≤ b → a < b := flip lt_of_le_of_ne'

end partial_order

attribute [simp] le_refl
attribute [ext] LE

alias le_trans        ← LE.le.trans
alias le_trans'       ← LE.le.trans'
alias lt_of_le_of_lt  ← LE.le.trans_lt
alias lt_of_le_of_lt' ← LE.le.trans_lt'
alias le_antisymm     ← LE.le.antisymm
alias ge_antisymm     ← LE.le.antisymm'
alias lt_of_le_of_ne  ← LE.le.lt_of_ne
alias lt_of_le_of_ne' ← LE.le.lt_of_ne'
alias lt_of_le_not_le ← LE.le.lt_of_not_le
alias lt_or_eq_of_le  ← LE.le.lt_or_eq
alias Decidable.lt_or_eq_of_le ← LE.le.lt_or_eq_dec

alias le_of_lt        ← LT.lt.le
alias lt_trans        ← LT.lt.trans
alias lt_trans'       ← LT.lt.trans'
alias lt_of_lt_of_le  ← LT.lt.trans_le
alias lt_of_lt_of_le' ← LT.lt.trans_le'
alias ne_of_lt        ← LT.lt.ne
alias lt_asymm        ← LT.lt.asymm LT.lt.not_lt

alias le_of_eq        ← Eq.le

attribute [nolint decidable_classical] LE.le.lt_or_eq_dec

section
variable [Preorder α] {a b c : α}

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

@[simp] lemma lt_self_iff_false (x : α) : x < x ↔ False := ⟨lt_irrefl x, False.elim⟩

lemma le_of_le_of_eq (hab : a ≤ b) (hbc : b = c) : a ≤ c := hab.trans hbc.le
lemma le_of_eq_of_le (hab : a = b) (hbc : b ≤ c) : a ≤ c := hab.le.trans hbc
lemma lt_of_lt_of_eq (hab : a < b) (hbc : b = c) : a < c := hab.trans_le hbc.le
lemma lt_of_eq_of_lt (hab : a = b) (hbc : b < c) : a < c := hab.le.trans_lt hbc
lemma le_of_le_of_eq' : b ≤ c → a = b → a ≤ c := flip le_of_eq_of_le
lemma le_of_eq_of_le' : b = c → a ≤ b → a ≤ c := flip le_of_le_of_eq
lemma lt_of_lt_of_eq' : b < c → a = b → a < c := flip lt_of_eq_of_lt
lemma lt_of_eq_of_lt' : b = c → a < b → a < c := flip lt_of_lt_of_eq

alias le_of_le_of_eq  ← LE.le.trans_eq
alias le_of_le_of_eq' ← LE.le.trans_eq'
alias lt_of_lt_of_eq  ← LT.lt.trans_eq
alias lt_of_lt_of_eq' ← LT.lt.trans_eq'
alias le_of_eq_of_le  ← Eq.trans_le
alias le_of_eq_of_le' ← Eq.trans_ge
alias lt_of_eq_of_lt  ← Eq.trans_lt
alias lt_of_eq_of_lt' ← Eq.trans_gt

end

namespace Eq
variable [Preorder α] {x y z : α}

/-- If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`, because `le` is used
almost exclusively in mathlib. -/
protected lemma ge (h : x = y) : y ≤ x := h.symm.le

lemma not_lt (h : x = y) : ¬ x < y := λ h' => h'.ne h
lemma not_gt (h : x = y) : ¬ y < x := h.symm.not_lt

end Eq

namespace LE.le

protected lemma ge [LE α] {x y : α} (h : x ≤ y) : y ≥ x := h

lemma lt_iff_ne [PartialOrder α] {x y : α} (h : x ≤ y) : x < y ↔ x ≠ y := ⟨λ h => h.ne, h.lt_of_ne⟩

lemma le_iff_eq [PartialOrder α] {x y : α} (h : x ≤ y) : y ≤ x ↔ y = x :=
⟨λ h' => h'.antisymm h, Eq.le⟩

lemma lt_or_le [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
(lt_or_ge a c).imp id $ λ hc => le_trans hc h

lemma le_or_lt [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
(le_or_gt a c).imp id $ λ hc => lt_of_lt_of_le hc h

lemma le_or_le [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
(h.le_or_lt c).elim Or.inl (λ h => Or.inr $ le_of_lt h)

end LE.le

namespace LT.lt

protected lemma gt [LT α] {x y : α} (h : x < y) : y > x := h
protected lemma false [Preorder α] {x : α} : x < x → False := lt_irrefl x

lemma ne' [Preorder α] {x y : α} (h : x < y) : y ≠ x := h.ne.symm

lemma lt_or_lt [LinearOrder α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
(lt_or_ge z y).elim Or.inr (λ hz => Or.inl $ h.trans_le hz)

end LT.lt

protected lemma ge.le [LE α] {x y : α} (h : x ≥ y) : y ≤ x := h

protected lemma gt.lt [LT α] {x y : α} (h : x > y) : y < x := h

theorem ge_of_eq [Preorder α] {a b : α} (h : a = b) : a ≥ b := le_of_eq h.symm

@[simp]
lemma ge_iff_le [Preorder α] {a b : α} : a ≥ b ↔ b ≤ a := Iff.rfl

@[simp]
lemma gt_iff_lt [Preorder α] {a b : α} : a > b ↔ b < a := Iff.rfl

lemma not_le_of_lt [Preorder α] {a b : α} (h : a < b) : ¬ b ≤ a := (le_not_le_of_lt h).right

alias not_le_of_lt ← LT.lt.not_le

lemma not_lt_of_le [Preorder α] {a b : α} (h : a ≤ b) : ¬ b < a := λ hba => not_le_of_lt hba h

alias not_lt_of_le ← LE.le.not_lt

-- See Note [decidable namespace]
protected lemma Decidable.le_iff_eq_or_lt [PartialOrder α] [@DecidableRel α (·≤·)]
  {a b : α} : a ≤ b ↔ a = b ∨ a < b := Decidable.le_iff_lt_or_eq.trans Or.comm

lemma le_iff_eq_or_lt [PartialOrder α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
le_iff_lt_or_eq.trans Or.comm

lemma lt_iff_le_and_ne [PartialOrder α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
⟨λ h => ⟨le_of_lt h, ne_of_lt h⟩, λ ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2⟩

-- See Note [decidable namespace]
protected lemma Decidable.eq_iff_le_not_lt [PartialOrder α] [@DecidableRel α (·≤·)]
  {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
⟨λ h => ⟨le_of_eq h, h ▸ lt_irrefl _⟩, λ ⟨h₁, h₂⟩=> le_antisymm h₁ $
  Decidable.by_contradiction $ λ h₃ => h₂ (lt_of_le_not_le h₁ h₃)⟩

lemma eq_iff_le_not_lt [PartialOrder α] {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
  have := Classical.dec
  Decidable.eq_iff_le_not_lt

lemma eq_or_lt_of_le [PartialOrder α] {a b : α} (h : a ≤ b) : a = b ∨ a < b := h.lt_or_eq.symm

alias Decidable.eq_or_lt_of_le ← LE.le.eq_or_lt_dec
alias eq_or_lt_of_le ← LE.le.eq_or_lt

attribute [nolint decidable_classical] LE.le.eq_or_lt_dec

lemma NE.le_iff_lt [PartialOrder α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
⟨λ h' => lt_of_le_of_ne h' h, λ h => h.le⟩

-- See Note [decidable namespace]
protected lemma Decidable.ne_iff_lt_iff_le [PartialOrder α] [@DecidableRel α (·≤·)]
  {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
⟨λ h => Decidable.by_cases le_of_eq (le_of_lt ∘ h.mp), λ h => ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[simp] lemma ne_iff_lt_iff_le [PartialOrder α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
   have := Classical.dec
   Decidable.ne_iff_lt_iff_le

lemma lt_of_not_ge' [LinearOrder α] {a b : α} (h : ¬ b ≤ a) : a < b :=
((le_total _ _).resolve_right h).lt_of_not_le h

lemma lt_iff_not_ge' [LinearOrder α] {x y : α} : x < y ↔ ¬ y ≤ x := ⟨not_le_of_gt, lt_of_not_ge'⟩

lemma ne.lt_or_lt [LinearOrder α] {x y : α} (h : x ≠ y) : x < y ∨ y < x := lt_or_gt_of_ne h

lemma not_lt_iff_eq_or_lt [LinearOrder α] {a b : α} : ¬ a < b ↔ a = b ∨ b < a :=
not_lt.trans $ Decidable.le_iff_eq_or_lt.trans $ or_congr eq_comm Iff.rfl

lemma exists_ge_of_linear [LinearOrder α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
match le_total a b with
| Or.inl h => ⟨_, h, le_rfl⟩
| Or.inr h => ⟨_, le_rfl, h⟩

lemma lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
  (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
lt_of_not_ge' $ λ h' => (H h').not_lt h

lemma le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
  (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

lemma lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
lt_iff_le_not_le.trans $ (and_congr H' (not_congr H)).trans lt_iff_le_not_le.symm

lemma lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
not_le.symm.trans $ (not_congr H).trans $ not_le

lemma le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
  (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨lt_iff_lt_of_le_iff_le, λ H => not_lt.symm.trans $ (not_congr H).trans $ not_lt⟩

lemma eq_of_forall_le_iff [PartialOrder α] {a b : α}
  (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

lemma le_of_forall_le [Preorder α] {a b : α}
  (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
H _ le_rfl

lemma le_of_forall_le' [Preorder α] {a b : α}
  (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
H _ le_rfl

lemma le_of_forall_lt [LinearOrder α] {a b : α}
  (H : ∀ c, c < a → c < b) : a ≤ b :=
le_of_not_lt $ λ h => lt_irrefl _ (H _ h)

lemma forall_lt_iff_le [LinearOrder α] {a b : α} :
  (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
⟨le_of_forall_lt, λ h _ hca => lt_of_lt_of_le hca h⟩

lemma le_of_forall_lt' [LinearOrder α] {a b : α}
  (H : ∀ c, a < c → b < c) : b ≤ a :=
le_of_not_lt $ λ h => lt_irrefl _ (H _ h)

lemma forall_lt_iff_le' [LinearOrder α] {a b : α} :
  (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
⟨le_of_forall_lt', λ h _ hac => lt_of_le_of_lt h hac⟩

lemma eq_of_forall_ge_iff [PartialOrder α] {a b : α}
  (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
((H _).2 le_rfl).antisymm ((H _).1 le_rfl)

/-- monotonicity of `≤` with respect to `→` -/
lemma le_implies_le_of_le_of_le {a b c d : α} [Preorder α] (hca : c ≤ a) (hbd : b ≤ d) :
  a ≤ b → c ≤ d :=
λ hab => (hca.trans hab).trans hbd

@[ext]
theorem Preorder.to_le_injective {α : Type _} : Function.injective (@Preorder.toLE α) := λ A B h => by
  cases A with | @mk A_toLE A_toLT A_le_refl A_le_trans A_lt_iff_le_not_le =>
  cases B with | @mk B_toLE B_toLT B_le_refl B_le_trans B_lt_iff_le_not_le =>
  subst h
  have hlt : A_toLT = B_toLT := by
    cases A_toLT with | @mk Alt =>
    cases B_toLT with | @mk Blt =>
    have hlt' : Alt = Blt := by
      funext a b
      have ha := A_lt_iff_le_not_le a b
      have hb := B_lt_iff_le_not_le a b
      have hha : @LT.lt α (@LT.mk α Alt) a b = Alt a b := rfl
      have hhb : @LT.lt α (@LT.mk α Blt) a b = Blt a b := rfl
      rw [hha] at ha
      rw [hhb] at hb
      rw [ha, hb]
    subst hlt'
    rfl
  subst hlt
  rfl

@[ext]
lemma PartialOrder.to_preorder_injective {α : Type _} :
  Function.injective (@PartialOrder.toPreorder α) := λ A B h => by
    cases A
    cases B
    subst h
    rfl

@[ext]
lemma LinearOrder.to_partial_order_injective {α : Type _} :
  Function.injective (@LinearOrder.toPartialOrder α) := by
  intros A B h
  cases A with | @mk A_toPartialOrder A_le_total A_decidable_le A_decidable_eq A_decidable_lt =>
  cases B with | @mk B_toPartialOrder B_le_total B_decidable_le B_decidable_eq B_decidable_lt =>
  subst h
  have h_dle : A_decidable_le = B_decidable_le := Subsingleton.elim _ _
  have h_dleq : A_decidable_eq = B_decidable_eq := Subsingleton.elim _ _
  have h_dlt : A_decidable_lt = B_decidable_lt := Subsingleton.elim _ _
  rw [h_dle, h_dleq, h_dlt]

theorem Preorder.ext {α} {A B : Preorder α}
    (H : ∀ x y : α, (A.toLE.le x y ↔ B.toLE.le x y)) : A = B := by
  ext x y
  exact H x y

theorem PartialOrder.ext {α} {A B : PartialOrder α}
    (H : ∀ x y : α, (A.toLE.le x y ↔ B.toLE.le x y)) : A = B := by
  ext x y
  exact H x y

open Mathlib.Tactic.Ext
theorem LinearOrder.ext {α} {A B : LinearOrder α}
    (H : ∀ x y : α, A.toLE.le x y ↔ B.toLE.le x y) : A = B := by
  ext x y
  exact H x y

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `rel_embedding` (assuming `f`
is injective). -/
@[simp] def Order.preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop := s (f x) (f y)

/-- If `f : α → β` and `s` is an order on `β`, then `f ⁻¹'o s` is an order on `α`.-/
infix:80 " ⁻¹'o " => Order.preimage

/-- The preimage of a decidable order is decidable. -/
instance Order.preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : DecidableRel s] :
  DecidableRel (f ⁻¹'o s) :=
λ _x _y => H _ _

/-! ### Order dual -/

/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type _) : Type _ := α

/--  If `α` has an order, then `αᵒᵈ` has the dual order.  -/
notation:max α "ᵒᵈ" => order_dual α

namespace order_dual

instance (α : Type _) [h : Nonempty α] : Nonempty αᵒᵈ := h
instance (α : Type _) [h : Subsingleton α] : Subsingleton αᵒᵈ := h
instance order_dual_le (α : Type _) [LE α] : LE αᵒᵈ := ⟨λ x y : α => y ≤ x⟩
instance order_dual_lt (α : Type _) [LT α] : LT αᵒᵈ := ⟨λ x y : α => y < x⟩
instance (α : Type _) [Zero α] : Zero αᵒᵈ := ⟨(0 : α)⟩

instance order_dual_preorder (α : Type _) [Preorder α] : Preorder αᵒᵈ :=
{  toLE := order_dual_le α
   toLT := order_dual_lt α
   le_refl          := λ a => @_root_.le_refl α _ a
   le_trans         := λ _ _ _ hab hbc => hbc.trans hab
   lt_iff_le_not_le := λ _ _ => lt_iff_le_not_le
}

instance order_dual_partial_order (α : Type _) [PartialOrder α] : PartialOrder αᵒᵈ :=
{ order_dual_preorder α with
    le_antisymm := λ a b hab hba => @le_antisymm α _ a b hba hab
}

instance order_dual_linear_order (α : Type _) [LinearOrder α] : LinearOrder αᵒᵈ :=
{ order_dual_partial_order α with
    le_total     := λ a b : α => le_total b a
    decidable_le := (inferInstance : DecidableRel (λ a b : α => b ≤ a))
    decidable_lt := (inferInstance : DecidableRel (λ a b : α => b < a))
}

instance : ∀ [Inhabited α], Inhabited αᵒᵈ := λ [x: Inhabited α] => x

theorem Preorder.dual_dual (α : Type _) [H : Preorder α] :
  order_dual_preorder αᵒᵈ = H :=
Preorder.ext $ λ _ _ => Iff.rfl

theorem partial_order.dual_dual (α : Type _) [H : PartialOrder α] :
  order_dual_partial_order αᵒᵈ = H :=
PartialOrder.ext $ λ _ _ => Iff.rfl

theorem linear_order.dual_dual (α : Type _) [H : LinearOrder α] :
  order_dual_linear_order αᵒᵈ = H :=
LinearOrder.ext $ λ _ _ => Iff.rfl

end order_dual

/-- Notation for set/lattice complement -/
postfix:max "ᶜ" => Complement.complement

instance Prop.complement : Complement Prop := ⟨Not⟩

instance Pi.complement {ι : Type u} {α : ι → Type v} [∀ i, Complement (α i)] :
  Complement (∀ i, α i) := ⟨λ x i => (x i)ᶜ⟩

lemma Pi.compl_def {ι : Type u} {α : ι → Type v} [∀ i, Complement (α i)] (x : ∀ i, α i) :
   xᶜ = λ i => (x i)ᶜ := rfl

@[simp]
lemma Pi.compl_apply {ι : Type u} {α : ι → Type v} [∀ i, Complement (α i)] (x : ∀ i, α i) (i : ι)  :
  xᶜ i = (x i)ᶜ := rfl

-- TODO is_irrefl.compl is_refl.compl

/-! ### Order instances on the function space -/

instance Pi.hasLe {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] : LE (∀ i, α i) where le := fun x y => ∀ i, x i ≤ y i

lemma Pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] {x y : ∀ i, α i} : x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl

instance Pi.preorder {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] : Preorder (∀ i, α i) :=
  { Pi.hasLe with le_refl := fun a i => le_refl (a i)
                  le_trans := fun a b c h₁ h₂ i => le_trans (h₁ i) (h₂ i)
                  lt_iff_le_not_le := by intros a b
                                         apply Iff.refl }

theorem Pi.lt_def {ι : Type u} {α: ι → Type v} [∀ i, Preorder (α i)] {x y : ∀ i, α i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp ( config := { contextual := true } ) [lt_iff_le_not_le, Pi.le_def]

lemma le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] [DecidableEq ι]
  {x y : ∀ i, α i} {i : ι} {a : α i} :
  x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ j, j ≠ i → x j ≤ y j :=
Function.forall_update_iff _ (λ j z => x j ≤ z)

lemma update_le_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] [DecidableEq ι]
  {x y : ∀ i, α i} {i : ι} {a : α i} :
  Function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ j, j ≠ i → x j ≤ y j :=
Function.forall_update_iff _ (λ j z => z ≤ y j)

lemma update_le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] [DecidableEq ι]
  {x y : ∀ i, α i} {i : ι} {a b : α i} :
  Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ j, j ≠ i → x j ≤ y j :=
by simp (config := {contextual := true}) [update_le_iff]

instance Pi.partial_order {ι : Type u} {α : ι → Type v} [∀ i, PartialOrder (α i)] :
  PartialOrder (∀ i, α i) :=
{ Pi.preorder with
              le_antisymm := λ _ _ h1 h2 => funext (λ b => (h1 b).antisymm (h2 b))
}

/-
TODO: section min_max_rec

This is awkward because Lean 4 defines `min` and `max` as toplevel functions in the prelude,
while mathlib3 defines them as part of the `linear_order` typeclass.
-/

/-- Typeclass for the `⊔` (`\lub`) notation -/
class Sup (α : Type u) where
  /-- Supremum, i.e. the least upper bound. -/
  sup : α → α → α

/-- Typeclass for the `⊓` (`\glb`) notation -/
class Inf (α : Type u) where
  /-- Infimum, i.e. the greatest lower bound. -/
  inf : α → α → α

/-- Syntax for write the supremum of `a` and `b` as `a ⊔ b`. -/
infix:68 " ⊔ " => Sup.sup

/-- Syntax for write the infinum of `a` and `b` as `a ⊓ b`. -/
infix:68 " ⊓ " => Inf.inf

/-! ### Lifts of order instances -/

/-- Transfer a `Preorder` on `β` to a `Preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible] def Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α :=
{ le               := λ x y => f x ≤ f y
  le_refl          := λ _ => le_rfl
  le_trans         := λ _ _ _ => _root_.le_trans
  lt               := λ x y => f x < f y
  lt_iff_le_not_le := λ _ _ => _root_.lt_iff_le_not_le
}

/-- Transfer a `PartialOrder` on `β` to a `PartialOrder` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) (inj : injective f) :
  PartialOrder α :=
{ Preorder.lift f with le_antisymm := λ _ _ h₁ h₂ => inj (h₁.antisymm h₂) }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def LinearOrder.lift {α β} [LinearOrder β] (f : α → β) (inj : injective f) :
  LinearOrder α :=
{ PartialOrder.lift f inj with
    le_total     := λ x y => le_total (f x) (f y),
    decidable_le := λ x y => (inferInstance : Decidable (f x ≤ f y))
    decidable_lt := λ x y => (inferInstance : Decidable (f x < f y))
    decidable_eq := λ _ _ => decidable_of_iff _ inj.eq_iff
}

namespace Subtype

instance [LE α] {p : α → Prop} : LE (Subtype p) := ⟨λ x y => (x : α) ≤ y⟩
instance [LT α] {p : α → Prop} : LT (Subtype p) := ⟨λ x y => (x : α) < y⟩

@[simp] lemma mk_le_mk {α} [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
Iff.rfl

@[simp] lemma mk_lt_mk {α} [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
Iff.rfl

--@[norm_cast]
@[simp] lemma coe_le_coe {α} [LE α] {p : α → Prop} {x y : Subtype p} :
  (x : α) ≤ y ↔ x ≤ y :=
Iff.rfl

--@[norm_cast]
@[simp] lemma coe_lt_coe {α} [LT α] {p : α → Prop} {x y : Subtype p} :
  (x : α) < y ↔ x < y :=
Iff.rfl

instance preorder [Preorder α] (p : α → Prop) : Preorder (Subtype p) :=
Preorder.lift Subtype.val

instance partial_order {α} [PartialOrder α] (p : α → Prop) :
  PartialOrder (Subtype p) :=
PartialOrder.lift Subtype.val Subtype.val_injective

instance decidable_le [Preorder α] [h : @DecidableRel α (·≤·)] {p : α → Prop} :
  @DecidableRel (Subtype p) (·≤·) :=
λ a b => h a b

instance decidable_lt [Preorder α] [h : @DecidableRel α (·<·)] {p : α → Prop} :
  @DecidableRel (Subtype p) (·<·) :=
λ a b => h a b

/-
TODO: In the following instance, explicitly give the proofs of decidable equality
and decidable order in order to ensure the decidability instances are all
definitionally equal.
-/
instance linear_order {α} [LinearOrder α] (p : α → Prop) : LinearOrder (Subtype p) :=
LinearOrder.lift Subtype.val Subtype.val_injective

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `data.prod.lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/

namespace Prod

instance has_le (α : Type u) (β : Type v) [LE α] [LE β] : LE (α × β) :=
⟨λ p q => p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

lemma le_def {α β : Type _} [LE α] [LE β] {x y : α × β} :
  x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := Iff.rfl

@[simp] lemma mk_le_mk {α β : Type _} [LE α] [LE β] {x₁ x₂ : α} {y₁ y₂ : β} :
  (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
Iff.rfl

@[simp] lemma swap_le_swap [LE α] [LE β] {x y : α × β} : x.swap ≤ y.swap ↔ x ≤ y :=
and_comm _ _

section preorder
variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance instPreorderProd (α : Type u) (β : Type v) [Preorder α] [Preorder β] : Preorder (α × β) :=
{  toLE := Prod.has_le α β
   toLT := ⟨λ a b => a ≤ b ∧ ¬ b ≤ a⟩ -- this is the default, why do I need to explicitly set it?
   le_refl  := λ ⟨a, b⟩ => ⟨le_refl a, le_refl b⟩
   le_trans := λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ =>
     ⟨le_trans hac hce, le_trans hbd hdf⟩
   lt_iff_le_not_le := λ _ _ => Iff.intro id id
}

/-
Port note: Below, we need to specify `(instPreorderProd _ _).lt` rather than just `<`, to
disambiguate from the prelude's `instLTProd`, which uses the lexicographic order on `α × β`.
-/

@[simp] lemma swap_lt_swap : (instPreorderProd _ _).lt x.swap y.swap ↔ (instPreorderProd _ _).lt x y :=
and_congr swap_le_swap (not_congr swap_le_swap)

lemma mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ := and_iff_left le_rfl
lemma mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ := and_iff_right le_rfl

lemma mk_lt_mk_iff_left : (instPreorderProd _ _).lt (a₁, b) (a₂, b) ↔ a₁ < a₂ :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

lemma mk_lt_mk_iff_right : (instPreorderProd _ _).lt (a, b₁) (a, b₂) ↔ b₁ < b₂ :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

lemma lt_iff : (instPreorderProd _ _).lt x y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 :=
by
  refine Iff.intro ?_ ?_
  · intro h
    cases em (y.1 ≤ x.1) with
    | inl h₁ => exact Or.inr ⟨h.1.1, h.1.2.lt_of_not_le $ λ h₂ => h.2 ⟨h₁, h₂⟩⟩
    | inr h₁ => exact Or.inl ⟨h.1.1.lt_of_not_le h₁, h.1.2⟩
  · intro h
    cases h with
    | inl p => exact ⟨⟨p.1.le, p.2⟩, λ h => p.1.not_le h.1⟩
    | inr p => exact ⟨⟨p.1, p.2.le⟩, λ h => p.2.not_le h.2⟩

@[simp] lemma mk_lt_mk :
  (instPreorderProd _ _).lt (a₁, b₁) (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

end preorder

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `lex α β = α × β`.) -/
instance (α : Type u) (β : Type v) [PartialOrder α] [PartialOrder β] :
  PartialOrder (α × β) :=
{ toPreorder := instPreorderProd α β
  le_antisymm := λ _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ =>
    Prod.ext' (hac.antisymm hca) (hbd.antisymm hdb)
}

end Prod

/-! ### Additional order classes -/

/-- An order is dense if there is an element between any pair of distinct elements. -/
class DenselyOrdered (α : Type u) [LT α] : Prop where
  /-- For any two distinct elements, there exists a third element strictly between them. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

lemma exists_between [LT α] [DenselyOrdered α] :
  ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
λ {a₁ a₂} h => @DenselyOrdered.dense α _ _ a₁ a₂ h

instance order_dual.densely_ordered (α : Type u) [hlt: LT α] [hdo: DenselyOrdered α] :
  DenselyOrdered αᵒᵈ :=
⟨λ _ _ ha => (@exists_between α hlt hdo _ _ ha).imp $ λ _ => And.symm⟩

lemma le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
  (h : ∀ a, a₂ < a → a₁ ≤ a) :
  a₁ ≤ a₂ :=
le_of_not_gt $ λ ha =>
  let ⟨a, ha₁, ha₂⟩ := exists_between ha
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
le_antisymm (le_of_forall_le_of_dense h₂) h₁

lemma le_of_forall_ge_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
  (h : ∀ a₃ < a₁, a₃ ≤ a₂) :
  a₁ ≤ a₂ :=
le_of_not_gt $ λ ha =>
  let ⟨a, ha₁, ha₂⟩ := exists_between ha
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ = a₂ :=
(le_of_forall_ge_of_dense h₂).antisymm h₁

lemma dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
  (∃ a, a₁ < a ∧ a < a₂) ∨ ((∀ a, a₁ < a → a₂ ≤ a) ∧ (∀ a < a₂, a ≤ a₁)) :=
or_iff_not_imp_left.2 $ λ h =>
  ⟨λ a ha₁ => le_of_not_gt $ λ ha₂ => h ⟨a, ha₁, ha₂⟩,
    λ a ha₂ => le_of_not_gt $ λ ha₁ => h ⟨a, ha₁, ha₂⟩⟩

-- TODO namespace PUnit
-- TODO linear order from a total partial order
