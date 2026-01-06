/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Types.Defs
public import Mathlib.Order.Interval.Set.Basic

/-!

## Main definitions

* `OrderType.card o`: the cardinality of an OrderType `o`.
* `o₁ + o₂`: the lexicographic sum of order types, which forms an `AddMonoid`.
* `o₁ * o₂`: the lexicographic product of order types, which forms a `MonoidWithZero`.

## Notation

The following are notations in the `OrderType` namespace:

* `η` is a notation for the order type of `ℚ` with its natural order.
* `θ` is a notation for the order type of `ℝ` with its natural order.

## References

* <https://en.wikipedia.org/wiki/Order_type>
* Dauben, J. W. Georg Cantor: His Mathematics and Philosophy of the Infinite. Princeton,
  NJ: Princeton University Press, 1990.
* Enderton, Herbert B. Elements of Set Theory. United Kingdom: Academic Press, 1977.

## Tags

order type, order isomorphism, linear order
-/

public noncomputable section

namespace OrderType

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'}

instance : ZeroLEOneClass OrderType :=
  ⟨OrderType.zero_le _⟩

instance : Add OrderType.{u} where
  add := Quotient.map₂ (fun r s ↦ ⟨(r ⊕ₗ s)⟩)
    fun _ _ ha _ _ hb ↦ ⟨OrderIso.sumLexCongr (Classical.choice ha) (Classical.choice hb)⟩

instance : HAdd OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hAdd := Quotient.map₂ (fun r s ↦ ⟨(r ⊕ₗ s)⟩)
   fun _ _ ha _ _ hb ↦ ⟨OrderIso.sumLexCongr (Classical.choice ha) (Classical.choice hb)⟩

instance : AddMonoid OrderType where
  add_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ ↦ (OrderIso.sumLexAssoc α β γ).orderType_eq
  zero_add o :=
    inductionOn o (fun α _ ↦ RelIso.orderType_eq (OrderIso.emptySumLex α _))
  add_zero o :=
   inductionOn o (fun α _ ↦ RelIso.orderType_eq (OrderIso.sumLexEmpty α _))
  nsmul := nsmulRec

instance (n : Nat) : OfNat OrderType n where
 ofNat := Fin n |> type

@[simp]
lemma type_add (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ⊕ₗ β) = type α + type β := rfl

instance : Mul OrderType where
  mul := Quotient.map₂ (fun r s ↦ ⟨(s ×ₗ r)⟩)
   fun _ _ ha _ _ hb ↦ ⟨Prod.Lex.prodCongr (Classical.choice hb) (Classical.choice ha)⟩

instance : HMul OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hMul := Quotient.map₂ (fun r s ↦ ⟨(s ×ₗ r)⟩)
   fun _ _ ha _ _ hb ↦ ⟨Prod.Lex.prodCongr (Classical.choice hb) (Classical.choice ha)⟩

@[simp]
lemma type_mul (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ×ₗ β) = type β * type α := rfl

instance : Monoid OrderType where
  mul_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ (fun α _ β _ γ _ ↦
    RelIso.orderType_eq (Prod.Lex.prodAssoc γ β α).symm)
  one_mul o := inductionOn o (fun α _ ↦ RelIso.orderType_eq (Prod.Lex.prodUnique α PUnit))
  mul_one o := inductionOn o (fun α _ ↦ RelIso.orderType_eq (Prod.Lex.uniqueProd PUnit α)) --6

instance : LeftDistribClass OrderType where
  left_distrib a b c := by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ ↦ ?_)
    simp only [←type_mul,←type_add]
    exact RelIso.orderType_eq (Prod.Lex.sumProdDistrib _ _ _)

/-- The order type of the rational numbers. -/
def eta : OrderType := type ℚ

/-- The order type of the real numbers. -/
def theta : OrderType := type ℝ

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]

section Cardinal

open Cardinal

/-- The cardinal of an `OrderType` is the cardinality of any type on which a relation
with that order type is defined. -/
@[expose]
def card : OrderType → Cardinal :=
  Quotient.map _ fun _ _ ⟨e⟩ ↦ ⟨e.toEquiv⟩

@[simp]
theorem card_type [LinearOrder α] : card (type α) = #α :=
  rfl

@[gcongr]
theorem card_le_card {o₁ o₂ : OrderType} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun _ ↦ inductionOn o₂ fun _ _ ⟨f⟩ ↦ ⟨f.toEmbedding⟩

theorem card_mono : Monotone card := by
 rw [Monotone]; exact @card_le_card

@[simp]
theorem card_zero : card 0 = 0 := mk_eq_zero _

@[simp]
theorem card_one : card 1 = 1 := mk_eq_one _

end Cardinal

end OrderType
