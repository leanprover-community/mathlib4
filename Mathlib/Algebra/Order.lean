/-
Ported by Deniz Aydin from the lean3 prelude:
https://github.com/leanprover-community/lean/blob/master/library/init/algebra/order.lean

Original file's license:
  Copyright (c) 2016 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Leonardo de Moura
-/
import Mathlib.Logic.Basic -- Only for Or.elim

/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

/-
TODO: Does Lean4 have an equivalent for this:
  Make sure instances defined in this file have lower priority than the ones
  defined for concrete structures
set_option default_priority 100
-/

universe u
variable {α : Type u}

-- set_option auto_param.check_exists false

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(lt := λ a b => a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)) -- . order_laws_tac)

variable [Preorder α]

/-- The relation `≤` on a preorder is reflexive. -/
theorem le_refl : ∀ (a : α), a ≤ a :=
Preorder.le_refl

/-- The relation `≤` on a preorder is transitive. -/
theorem le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
Preorder.le_trans _ _ _

theorem lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
Preorder.lt_iff_le_not_le _ _

theorem lt_of_le_not_le : ∀ {a b : α}, a ≤ b → ¬ b ≤ a → a < b
| a, b, hab, hba => lt_iff_le_not_le.mpr ⟨hab, hba⟩

theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬ b ≤ a
| a, b, hab => lt_iff_le_not_le.mp hab

theorem le_of_eq {a b : α} : a = b → a ≤ b :=
λ h => h ▸ le_refl a

theorem ge_trans : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c :=
λ h₁ h₂ => le_trans h₂ h₁

theorem lt_irrefl : ∀ a : α, ¬ a < a
| a, haa => match le_not_le_of_lt haa with
  | ⟨h1, h2⟩ => h2 h1

theorem gt_irrefl : ∀ a : α, ¬ a > a :=
lt_irrefl

theorem lt_trans : ∀ {a b c : α}, a < b → b < c → a < c
| a, b, c, hab, hbc =>
  match le_not_le_of_lt hab, le_not_le_of_lt hbc with
  | ⟨hab, hba⟩, ⟨hbc, hcb⟩ => lt_of_le_not_le (le_trans hab hbc) (λ hca => hcb (le_trans hca hab))

theorem gt_trans : ∀ {a b c : α}, a > b → b > c → a > c :=
λ h₁ h₂ => lt_trans h₂ h₁

theorem ne_of_lt {a b : α} (h : a < b) : a ≠ b :=
λ he => absurd h (he ▸ lt_irrefl a)

theorem ne_of_gt {a b : α} (h : b < a) : a ≠ b :=
λ he => absurd h (he ▸ lt_irrefl a)

theorem lt_asymm {a b : α} (h : a < b) : ¬ b < a :=
λ h1 : b < a => lt_irrefl a (lt_trans h h1)

theorem le_of_lt : ∀ {a b : α}, a < b → a ≤ b
| a, b, hab => (le_not_le_of_lt hab).left

theorem lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
| a, b, c, hab, hbc =>
  let ⟨hab, hba⟩ := le_not_le_of_lt hab
  lt_of_le_not_le (le_trans hab hbc) $ λ hca => hba (le_trans hbc hca)

theorem lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c
| a, b, c, hab, hbc =>
  let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc
  lt_of_le_not_le (le_trans hab hbc) $ λ hca => hcb (le_trans hca hab)

theorem gt_of_gt_of_ge {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
lt_of_le_of_lt h₂ h₁

theorem gt_of_ge_of_gt {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
lt_of_lt_of_le h₂ h₁

theorem not_le_of_gt {a b : α} (h : a > b) : ¬ a ≤ b :=
(le_not_le_of_lt h).right

theorem not_lt_of_ge {a b : α} (h : a ≥ b) : ¬ a < b :=
λ hab => not_le_of_gt hab h

theorem le_of_lt_or_eq : ∀ {a b : α}, (a < b ∨ a = b) → a ≤ b
| a, b, (Or.inl hab) => le_of_lt hab
| a, b, (Or.inr hab) => hab ▸ le_refl _

theorem le_of_eq_or_lt {a b : α} (h : a = b ∨ a < b) : a ≤ b := match h with
| (Or.inl h) => le_of_eq h
| (Or.inr h) => le_of_lt h

instance decidableLt_of_decidableLe [DecidableRel (. ≤ . : α → α → Prop)] :
  DecidableRel (. < . : α → α → Prop)
| a, b =>
  if hab : a ≤ b then
    if hba : b ≤ a then
      isFalse $ λ hab' => not_le_of_gt hab' hba
    else
      isTrue $ lt_of_le_not_le hab hba
  else
    isFalse $ λ hab' => hab (le_of_lt hab')

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type u) extends Preorder α :=
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

variable [PartialOrder α]

theorem le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
PartialOrder.le_antisymm _ _

theorem le_antisymm_iff {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
⟨λ e => ⟨le_of_eq e, le_of_eq e.symm⟩, λ ⟨h1, h2⟩ => le_antisymm h1 h2⟩

theorem lt_of_le_of_ne {a b : α} : a ≤ b → a ≠ b → a < b :=
λ h₁ h₂ => lt_of_le_not_le h₁ $ mt (le_antisymm h₁) h₂

instance decidableEq_of_decidableLe [DecidableRel (. ≤ . : α → α → Prop)] :
  DecidableEq α
| a, b =>
  if hab : a ≤ b then
    if hba : b ≤ a then
      isTrue (le_antisymm hab hba)
    else
      isFalse (λ heq => hba (heq ▸ le_refl _))
  else
    isFalse (λ heq => hab (heq ▸ le_refl _))

namespace Decidable

variable [@DecidableRel α (. ≤ .)]

theorem lt_or_eq_of_le {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
if hba : b ≤ a then Or.inr (le_antisymm hab hba)
else Or.inl (lt_of_le_not_le hab hba)

theorem eq_or_lt_of_le {a b : α} (hab : a ≤ b) : a = b ∨ a < b :=
(lt_or_eq_of_le hab).symm

theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

end Decidable

attribute [local instance] Classical.propDecidable

theorem lt_or_eq_of_le {a b : α} : a ≤ b → a < b ∨ a = b := Decidable.lt_or_eq_of_le

theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b := Decidable.le_iff_lt_or_eq

end PartialOrder

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrder (α : Type u) extends PartialOrder α :=
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)
(decidableLe : DecidableRel (. ≤ . : α → α → Prop))
(decidableEq : DecidableEq α := @decidableEq_of_decidableLe _ _ decidableLe)
(decidableLt : DecidableRel (. < . : α → α → Prop) :=
    @decidableLt_of_decidableLe _ _ decidableLe)

variable [LinearOrder α]

attribute [local instance] LinearOrder.decidableLe

theorem le_total : ∀ a b : α, a ≤ b ∨ b ≤ a :=
LinearOrder.le_total

theorem le_of_not_ge {a b : α} : ¬ a ≥ b → a ≤ b :=
Or.resolve_left (le_total b a)

theorem le_of_not_le {a b : α} : ¬ a ≤ b → b ≤ a :=
Or.resolve_left (le_total a b)

theorem not_lt_of_gt {a b : α} (h : a > b) : ¬ a < b :=
lt_asymm h

theorem lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
Or.elim
  (λ h : a ≤ b   => Or.elim
    (λ h : a < b => Or.inl h)
    (λ h : a = b => Or.inr (Or.inl h))
    (Decidable.lt_or_eq_of_le h))
  (λ h : b ≤ a   => Or.elim
    (λ h : b < a => Or.inr (Or.inr h))
    (λ h : b = a => Or.inr (Or.inl h.symm))
    (Decidable.lt_or_eq_of_le h))
  (le_total a b)

theorem le_of_not_lt {a b : α} (h : ¬ b < a) : a ≤ b :=
match lt_trichotomy a b with
| Or.inl hlt          => le_of_lt hlt
| Or.inr (Or.inl heq) => heq ▸ le_refl a
| Or.inr (Or.inr hgt) => absurd hgt h


theorem le_of_not_gt {a b : α} : ¬ a > b → a ≤ b := le_of_not_lt

theorem lt_of_not_ge {a b : α} (h : ¬ a ≥ b) : a < b :=
lt_of_le_not_le ((le_total _ _).resolve_right h) h

theorem lt_or_le (a b : α) : a < b ∨ b ≤ a :=
if hba : b ≤ a then Or.inr hba else Or.inl $ lt_of_not_ge hba

theorem le_or_lt (a b : α) : a ≤ b ∨ b < a :=
(lt_or_le b a).symm

theorem lt_or_ge : ∀ (a b : α), a < b ∨ a ≥ b := lt_or_le
theorem le_or_gt : ∀ (a b : α), a ≤ b ∨ a > b := le_or_lt

theorem lt_or_gt_of_ne {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
match lt_trichotomy a b with
| Or.inl hlt          => Or.inl hlt
| Or.inr (Or.inl heq) => absurd heq h
| Or.inr (Or.inr hgt) => Or.inr hgt

theorem ne_iff_lt_or_gt {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
⟨lt_or_gt_of_ne, λ o => match o with
  | Or.inl ol => ne_of_lt ol
  | Or.inr or => ne_of_gt or
⟩

theorem lt_iff_not_ge (x y : α) : x < y ↔ ¬ x ≥ y :=
⟨not_le_of_gt, lt_of_not_ge⟩

@[simp] theorem not_lt {a b : α} : ¬ a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

@[simp] theorem not_le {a b : α} : ¬ a ≤ b ↔ b < a := (lt_iff_not_ge _ _).symm

instance (a b : α) : Decidable (a < b) :=
LinearOrder.decidableLt a b

instance (a b : α) : Decidable (a ≤ b) :=
LinearOrder.decidableLe a b

instance (a b : α) : Decidable (a = b) :=
LinearOrder.decidableEq a b

theorem eq_or_lt_of_not_lt {a b : α} (h : ¬ a < b) : a = b ∨ b < a :=
if h₁ : a = b then Or.inl h₁
else Or.inr (lt_of_not_ge (λ hge => h (lt_of_le_of_ne hge h₁)))

/- TODO: instances of classes that haven't been defined.

instance : is_total_preorder α (≤) :=
{trans := @le_trans _ _, total := le_total}

instance is_strict_weak_order_of_linear_order : is_strict_weak_order α (<) :=
is_strict_weak_order_of_is_total_preorder lt_iff_not_ge

instance is_strict_total_order_of_linear_order : is_strict_total_order α (<) :=
{ trichotomous := lt_trichotomy }
-/

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def lt_by_cases (x y : α) {P : Sort _}
 (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
if h : x < y then h₁ h else
if h' : y < x then h₃ h' else
h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))

theorem le_imp_le_of_lt_imp_lt {β} [Preorder α] [LinearOrder β]
  {a b : α} {c d : β} (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
le_of_not_lt $ λ h' => not_le_of_gt (H h') h

end LinearOrder
