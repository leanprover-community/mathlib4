/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Order types

Order types are defined as the quotient of linear orders under order isomorphism. They are endowed
with a preorder, where an OrderType is smaller than another one there is an order embedding
into it.

## Main definitions

* `OrderType`: the type of OrderTypes (in a given universe)
* `OrderType.type α`: given a type `α` with a linear order, this is the corresponding OrderType,
* `OrderType.card o`: the cardinality of an OrderType `o`.
* `o₁ + o₂`: the lexicographic sum of order types, which forms an `AddMonoid`.
* `o₁ * o₂`: the lexicographic product of order types, which forms a `MonoidWithZero`.
* `OrderType.mul o₁ o₂`: the product of two OrderTypes `o₁` and `o₂`.

A preorder with a bottom element is registered on order types, where `⊥` is
`0`, the order type corresponding to the empty type.

## Notation

The following are scoped notations in the `OrderType` namespace:

* `ω` is a notation for the order type of `ℕ` with its natural order.
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

noncomputable section

open Function Cardinal Set Equiv Order

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'}

instance {α : Type*} [IsEmpty α] : Subsingleton α where
 allEq a _ := (IsEmpty.false a).elim

instance {α : Type*} [IsEmpty α] : LinearOrder α := .ofSubsingleton

/-- An auxiliary structure representing a linearly ordered type. -/
@[ext]
structure LinearOrderedType : Type (u + 1) where
  carrier : Type u
  le : LE carrier
  isLinearOrder_carrier : Std.IsLinearOrder carrier

instance (x : LinearOrderedType) : LE x.carrier := x.le

instance (x : LinearOrderedType) : LinearOrder x.carrier where
  le_refl := x.isLinearOrder_carrier.le_refl
  le_trans := x.isLinearOrder_carrier.le_trans
  le_antisymm := x.isLinearOrder_carrier.le_antisymm
  le_total := x.isLinearOrder_carrier.le_total
  toDecidableLE := Classical.decRel LE.le

/-- Equivalence relation on linear orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance OrderType.instSetoid : Setoid LinearOrderedType where
  r := fun lin_ord₁ lin_ord₂ ↦
    Nonempty (@OrderIso lin_ord₁.carrier lin_ord₂.carrier lin_ord₁.le lin_ord₂.le)
  iseqv :=
    ⟨fun l ↦ ⟨@OrderIso.refl _ l.le⟩, fun ⟨e⟩ ↦ ⟨@e.symm⟩,
      fun {x y z} ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨@OrderIso.trans _ _ _  x.le y.le z.le e₁ e₂⟩⟩

/-- `OrderType.{u}` is the type of linear orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
public def OrderType : Type (u + 1) :=
  Quotient OrderType.instSetoid

namespace OrderType

/-- A "canonical" type order-isomorphic to the order type `o`, living in the same universe.
This is defined through the axiom of choice. -/
def ToType (o : OrderType) : Type u :=
  o.out.carrier

def toisLinearOrder (o : OrderType) := o.out.isLinearOrder_carrier

def totype_def (o : OrderType) : o.ToType = o.out.carrier := rfl

instance (o : OrderType) : LE o.ToType := ⟨o.out.le.le⟩

instance (o : OrderType) : Std.IsLinearOrder o.ToType := o.out.isLinearOrder_carrier

instance (o : OrderType) : LinearOrder o.ToType where
  le_refl := o.toisLinearOrder.le_refl
  le_antisymm := o.toisLinearOrder.le_antisymm
  le_trans := o.toisLinearOrder.le_trans
  le_total := o.toisLinearOrder.le_total
  toDecidableLE := Classical.decRel LE.le

/-! ### Basic properties of the order type -/

/-- The order type of the linear order on `α`. -/
def type (α : Type u) [h₁ : LE α] [h₂ : Std.IsLinearOrder α] : OrderType :=
  ⟦⟨α, h₁, h₂⟩⟧

instance zero : Zero OrderType where
  zero := type PEmpty

instance instCoe : Coe LinearOrderedType (Type u) where
 coe x := x.carrier

instance (α : Type u) [inst : LinearOrder α] : Std.IsLinearOrder α := ⟨inst.le_total⟩

instance (α : Type*) [inst : LinearOrder α] (x : α) : CoeT α x LinearOrderedType where
 coe := ⟨α, inst.toLE, inferInstance⟩

instance inhabited : Inhabited OrderType :=
  ⟨0⟩

instance : One OrderType where
  one := type PUnit

lemma one_def : (1 : OrderType) = type PUnit := rfl

@[simp]
theorem type_ordtoType (o : OrderType) : type o.ToType = o := surjInv_eq Quot.exists_rep o

theorem type_eq {α β} [LinearOrder α] [LinearOrder β] :
    type α = type β ↔ Nonempty (α ≃o β) :=
  Quotient.eq'

theorem _root_.RelIso.ordertype_eq {α β} [LinearOrder α]
    [LinearOrder β] (h : α ≃o β) : type α = type β :=
  type_eq.2 ⟨h⟩

@[simp]
theorem type_eq_zero [LinearOrder α] [IsEmpty α] : type α = 0 :=
  (OrderIso.ofIsEmpty α PEmpty).ordertype_eq

@[simp]
theorem type_eq_zero_iff [LinearOrder α] : type α = 0 ↔ IsEmpty α :=
  ⟨fun h ↦
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero α _⟩

theorem type_ne_zero_iff [LinearOrder α] : type α ≠ 0 ↔ Nonempty α := by simp

theorem type_ne_zero [LinearOrder α] [h : Nonempty α] : type α ≠ 0 :=
  type_ne_zero_iff.2 h

theorem type_empty : type Empty = 0 :=
  type_eq_zero

@[simp]
theorem type_eq_one [LinearOrder α] [Nonempty α] [Subsingleton α] : type α = 1 := by
  cases nonempty_unique α
  exact (OrderIso.ofUnique α _).ordertype_eq

@[simp]
theorem type_eq_one_iff [LinearOrder α] : type α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_eq_one⟩

@[simp]
theorem isEmpty_toType_iff {o : OrderType} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero_iff o.ToType, type_ordtoType]

instance isEmpty_toType_zero : IsEmpty (ToType 0) :=
 isEmpty_toType_iff.2 rfl

@[simp]
theorem nonempty_toType_iff {o : OrderType} : Nonempty o.ToType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff o.ToType, type_ordtoType]

protected theorem one_ne_zero : (1 : OrderType) ≠ 0 :=
  type_ne_zero

instance nontrivial : Nontrivial OrderType.{u} :=
  ⟨⟨1, 0, OrderType.one_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to `OrderType`. -/
@[elab_as_elim]
theorem inductionOn {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  Quot.inductionOn o (fun α ↦ H α.carrier)

/-- `Quotient.inductionOn₂` specialized to OrderTypes. -/
@[elab_as_elim]
theorem inductionOn₂ {C : OrderType → OrderType → Prop} (o₁ o₂ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β], C (type α) (type β)) : C o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun α β ↦ H α β

/-- `Quotient.inductionOn₃` specialized to OrderTypes. -/
@[elab_as_elim]
theorem inductionOn₃ {C : OrderType → OrderType → OrderType → Prop} (o₁ o₂ o₃ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β] γ [LinearOrder γ],
      C (type α) (type β) (type γ)) : C o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ ↦
    H α β γ

/-- To define a function on `OrderType`, it suffices to define it on all linear orders.
-/
def liftOn {δ : Sort v} (o : OrderType) (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) : δ :=
  Quotient.liftOn o (fun w ↦ f w)
    fun w₁ w₂ h ↦ c w₁ w₂ (Quotient.sound h)

@[simp]
theorem liftOnLinOrd_type {δ : Sort v} (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) {γ} [inst : LinearOrder γ] :
    liftOn (type γ) f c = f γ := by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
  grind

/-! ### The order on `OrderType` -/

/--
The order is defined so that `type α ≤ type β` iff there exists an order embedding `α ↪o β`.
-/
instance : Preorder OrderType where
  le a b :=
    Quotient.liftOn₂ a b (fun r s ↦ Nonempty (r ↪o s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ ↦ propext
      ⟨fun ⟨h⟩ ↦ ⟨(f.symm.toOrderEmbedding.trans h).trans g.toOrderEmbedding⟩, fun ⟨h⟩ ↦
        ⟨(f.toOrderEmbedding.trans h).trans g.symm.toOrderEmbedding⟩⟩
  le_refl := Quot.ind fun _ ↦ ⟨(OrderIso.refl _).toOrderEmbedding⟩
  le_trans a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩

instance instNeZeroOne : NeZero (1 : OrderType) :=
  ⟨OrderType.one_ne_zero⟩

theorem type_le_iff {α β} [LinearOrder α]
    [LinearOrder β] : type α ≤ type β ↔ Nonempty (α ↪o β) :=
  Iff.rfl
theorem type_le {α β}
    [LinearOrder α] [LinearOrder β] (h : α ↪o β) : type α ≤ type β :=
  ⟨h⟩

theorem _root_.RelEmbedding.type_le {α β}
    [LinearOrder α] [LinearOrder β] (h : α ↪o β) : type α ≤ type β :=
  ⟨h⟩

protected theorem zero_le (o : OrderType) : 0 ≤ o :=
  inductionOn o (fun _ ↦ OrderEmbedding.ofIsEmpty.type_le)

instance : OrderBot OrderType where
  bot := 0
  bot_le := OrderType.zero_le

@[simp]
theorem bot_eq_zero : (⊥ : OrderType) = 0 :=
  rfl

instance instIsEmptyIioZero : IsEmpty (Iio (0 : OrderType)) := by
  simp [← bot_eq_zero]

@[simp]
protected theorem not_lt_zero (o : OrderType) : ¬o < 0 :=
  not_lt_bot

instance : ZeroLEOneClass OrderType :=
  ⟨OrderType.zero_le _⟩

section Cardinal
/-- The cardinal of an OrderType is the cardinality of any type on which a relation with that order
type is defined. -/
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

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
public def omega0 : OrderType := type ℕ

/-- The order type of the rational numbers. -/
public def eta : OrderType := type ℚ

/-- The order type of the real numbers. -/
public def theta : OrderType := type ℝ

@[inherit_doc]
scoped notation "ω" => OrderType.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]

instance : Add OrderType.{u} where
  add := Quotient.map₂ (fun r s ↦ ⟨(r ⊕ₗ s), inferInstance, inferInstance⟩)
   fun _ _ ha _ _ hb ↦ ⟨OrderIso.sumLexCongr (Classical.choice ha) (Classical.choice hb)⟩

instance : HAdd OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hAdd := Quotient.map₂ (fun r s ↦ ⟨(r ⊕ₗ s), inferInstance, inferInstance⟩)
   fun _ _ ha _ _ hb ↦ ⟨OrderIso.sumLexCongr (Classical.choice ha) (Classical.choice hb)⟩

lemma OrderIso.sumLexEmpty (α : Type u) {β : Type v} [LinearOrder α] [IsEmpty β] :
    Nonempty (Lex (α ⊕ β) ≃o α) :=
  ⟨OrderIso.ofRelIsoLT ((Sum.Lex.toLexRelIsoLT (α := α) (β := β)).symm.trans
    (RelIso.sumLexEmpty (β := β) (α := α) (r := (· < ·)) (s := (· < ·))))⟩

lemma OrderIso.emptySumLex (α : Type u) {β : Type v} [LinearOrder α] [IsEmpty β] :
    Nonempty (Lex (β ⊕ α) ≃o α) :=
  ⟨OrderIso.ofRelIsoLT ((Sum.Lex.toLexRelIsoLT (α := β) (β := α)).trans
    (RelIso.emptySumLex (β := α) (α := β) (r := (· < ·)) (s := (· < ·))))⟩

instance : AddMonoid OrderType where
  add_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ (fun α _ β _ γ _ ↦ RelIso.ordertype_eq (OrderIso.sumLexAssoc α β γ))
  zero_add o :=
    inductionOn o (fun α _ ↦ RelIso.ordertype_eq (Classical.choice (OrderIso.emptySumLex α)))
  add_zero o :=
   inductionOn o (fun α _ ↦ RelIso.ordertype_eq (Classical.choice (OrderIso.sumLexEmpty α)))
  nsmul := nsmulRec

instance (n : Nat) : OfNat OrderType n where
 ofNat := Fin n |> type

@[simp]
lemma type_add (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ⊕ₗ β) = type α + type β := rfl

instance : Mul OrderType where
  mul := Quotient.map₂ (fun r s ↦ ⟨(s ×ₗ r), inferInstance, inferInstance⟩)
   fun _ _ ha _ _ hb ↦ ⟨Prod.Lex.prodCongr (Classical.choice hb) (Classical.choice ha)⟩

instance : HMul OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hMul := Quotient.map₂ (fun r s ↦ ⟨(s ×ₗ r), inferInstance, inferInstance⟩)
   fun _ _ ha _ _ hb ↦ ⟨Prod.Lex.prodCongr (Classical.choice hb) (Classical.choice ha)⟩

@[simp]
lemma type_mul (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ×ₗ β) = type β * type α := by
      simp only [OrderType.type]
      congr; ext; simp only [instLinearOrderCarrier]

instance : Monoid OrderType where
  mul_assoc o₁ o₂ o₃ := by
    refine inductionOn₃ o₁ o₂ o₃ (fun α _ β _ γ _ ↦ ?_)
    simp only [←type_mul]
    exact RelIso.ordertype_eq ( Prod.Lex.prodAssoc _ _ _ |> OrderIso.symm )
  one_mul o := by
    rcases o with ⟨l⟩
    exact Quot.sound ⟨Prod.Lex.prodUnique _ PUnit⟩
  mul_one o := by
    refine inductionOn o (fun α hα ↦ ?_)
    rw [one_def, ←type_mul ]
    exact RelIso.ordertype_eq (Prod.Lex.uniqueProd PUnit _)

instance : LeftDistribClass OrderType where
  left_distrib a b c := by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ ↦ ?_)
    simp only [←type_mul,←type_add]
    exact RelIso.ordertype_eq (Prod.Lex.sumProdDistrib _ _ _)

end OrderType
