/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Category.LinOrd
import Mathlib.SetTheory.Ordinal.Basic

/-!
# OrderTypes

Order types are defined as the quotient of linear orders under order isomorphism. They are endowed
with a preorder, where an OrderType is smaller than another one there is an order embedding
into it.

## Main definitions

* `OrderType`: the type of OrderTypes (in a given universe)
* `OrderType.type α`: given a type `α` with a linear order, this is the corresponding OrderType,
* `OrderType.card o`: the cardinality of an OrderType `o`.
* `o₁ + o₂`: the lexicographic sum of order types, which forms an `AddMonoid`
* `o₁ * o₂`: the lexicographic product of order types (which surely forms a monoid as well?)
* `OrderType.mul o₁ o₂`: the product of two OrderTypes `o₁` and `o₂`.

A preorder with a bottom element is registered on order types, where `⊥` is
`0`, the order type corresponding to the empty type.

## Notation

* `ω` is a notation for the order type of `ℕ` with its natural order.
* `η` is a notation for the order type of `ℚ` with its natural order.
* `θ` is a notation for the order type of the real numbers on the interval `(0,1)`.

## References

* <https://en.wikipedia.org/wiki/Order_type>
* Dauben, J. W. Georg Cantor: His Mathematics and Philosophy of the Infinite. Princeton,
  NJ: Princeton University Press, 1990.
* Enderton, Herbert B.. Elements of Set Theory. United Kingdom: Academic Press, 1977.

## Tags

order type, order isomorphism, linear order
-/

noncomputable section

open Function Cardinal Set Equiv Order

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'}

def ordIsoOfIsEmpty (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β]
    [IsEmpty β] [IsEmpty α] : α ≃o β :=
  ⟨Equiv.equivOfIsEmpty α β, @fun a ↦ isEmptyElim a⟩

def OrderType.ofUniqueOfIrrefl [LinearOrder α]
    [LinearOrder β] [Unique α] [Unique β] : α ≃o β :=
  ⟨Equiv.ofUnique α β, by simp⟩

/-- Equivalence relation on linear orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance OrderType.instSetoid : Setoid LinOrd where
  r := fun lin_ord₁ lin_ord₂ ↦ Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ ↦ ⟨.refl _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩⟩

/-- `OrderType.{u}` is the type of linear orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
def OrderType : Type (u + 1) :=
  Quotient OrderType.instSetoid

namespace OrderType

/-- A "canonical" type order-isomorphic to the order type o, living in the same universe.
This is defined through the axiom of choice. -/
def ToType (o : OrderType) : Type u :=
  o.out.carrier

instance (o : OrderType) : LinearOrder o.ToType :=
  o.out.str

/-! ### Basic properties of the order type -/

/-- The order type of a linear order on α. -/
def type (α : Type u) [LinearOrder α] : OrderType :=
  ⟦⟨α⟩⟧

instance zero : Zero OrderType where
  zero := type PEmpty

lemma zero_def : (0 : OrderType) = type PEmpty := rfl


instance inhabited : Inhabited OrderType :=
  ⟨0⟩

instance : One OrderType where
 one := ⟦LinOrd.of PUnit⟧

lemma one_def : (1 : OrderType) = type PUnit := rfl

@[simp]
theorem type_ordtoType (o : OrderType) : type o.ToType = o :=
  o.out_eq

theorem type_eq {α β} [LinearOrder α] [LinearOrder β] :
    type α = type β ↔ Nonempty (α ≃o β) :=
  Quotient.eq'

theorem _root_.RelIso.ordertype_congr {α β} [LinearOrder α]
    [LinearOrder β] (h : α ≃o β) : type α = type β :=
  type_eq.2 ⟨h⟩

@[simp]
theorem type_eq_zero [LinearOrder α] [IsEmpty α] : type α = 0 := by
 convert (ordIsoOfIsEmpty α PEmpty).ordertype_congr

@[simp]
theorem type_eq_zero_iff [LinearOrder α] : type α = 0 ↔ IsEmpty α :=
  ⟨fun h ↦
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero α _⟩

theorem type_ne_zero_iff [LinearOrder α] : type α ≠ 0 ↔ Nonempty α := by simp

theorem type_ne_zero [LinearOrder α] [h : Nonempty α] : type α ≠ 0 :=
  type_ne_zero_iff.2 h

theorem type_pEmpty : type PEmpty = 0 :=
  rfl

theorem type_empty : type Empty = 0 :=
  type_eq_zero

@[simp]
theorem type_eq_one [LinearOrder α] [Nonempty α] [Subsingleton α] : type α = 1 := by
  cases nonempty_unique α
  exact (@ofUniqueOfIrrefl _).ordertype_congr

@[simp]
theorem type_eq_one_iff [LinearOrder α] : type α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_eq_one⟩

theorem type_pUnit : type PUnit = 1 :=
  rfl

theorem type_unit : type Unit = 1 :=
  rfl

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

/-- `Quotient.inductionOn` specialized to OrderTypes. -/
@[elab_as_elim]
theorem inductionOn {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  Quot.inductionOn o (fun α ↦ H α)

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

open Classical in
/-- To prove a result on OrderTypes, it suffices to prove it for order types of linear orders. -/
@[elab_as_elim]
theorem inductionOnLinOrd {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  inductionOn o fun α ↦ H α

open Classical in
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
      type α = type β → f α = f β) {γ} [LinearOrder γ] :
    liftOn (type γ) f c = f γ := by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]

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

instance instNeZeroOne : NeZero (1 : OrderType) :=
  ⟨OrderType.one_ne_zero⟩

theorem type_le_iff {α β} [LinearOrder α]
    [LinearOrder β] : type α ≤ type β ↔ Nonempty (α ↪o β) :=
  Iff.rfl

theorem type_le_iff' {α β} [inst1 : LinearOrder α]
    [inst2 : LinearOrder β] : type α ≤ type β ↔ Nonempty (inst1.le ↪r inst2.le) :=
  ⟨fun f ↦ f, fun f ↦ f⟩

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

theorem ord_card_mono {o₁ o₂ : OrderType} (h : o₁ ≤ o₂) : (card o₁).ord ≤ (card o₂).ord :=
  Cardinal.ord_mono (OrderType.card_le_card h)

@[simp]
theorem card_zero : card 0 = 0 := mk_eq_zero _

@[simp]
theorem card_one : card 1 = 1 := mk_eq_one _

end Cardinal
/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega0 : OrderType := type ℕ

/-- The order type of the rational numbers. -/
def eta : OrderType := type ℚ

/-- The order type of the real numbers on the interval `(0,1)`. -/
def theta : OrderType := type (Set.Ioo (0 : ℝ) 1)

@[inherit_doc]
scoped notation "ω" => OrderType.omega0

@[inherit_doc]
scoped notation "η" => OrderType.eta

@[inherit_doc]
scoped notation "θ" => OrderType.theta

open Classical
in instance : Add OrderType.{u} where
  add := Quotient.map₂ (fun r s ↦ ⟨(r ⊕ₗ s)⟩)
   (fun _ _ ha _ _ hb ↦ ⟨OrderIso.sumLexCongr (choice ha) (choice hb)⟩)

open Classical
in instance : HAdd OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hAdd := Quotient.map₂ (fun r s ↦ ⟨(r ⊕ₗ s)⟩)
   (fun _ _ ha _ _ hb ↦ ⟨OrderIso.sumLexCongr (choice ha) (choice hb)⟩)

@[simp]
lemma type_add (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ⊕ₗ β) = (type α) + (type β) := rfl

lemma OrderIso.sumLexEmpty (α : Type u) [LinearOrder α] : Nonempty (Lex (α ⊕ PEmpty) ≃o α) :=
  ⟨OrderIso.ofRelIsoLT ((Sum.Lex.toLexRelIsoLT (α := α) (β := PEmpty)).symm.trans
    (RelIso.sumLexEmpty (β := PEmpty) (α := α) (r := (· < ·)) (s := (· < ·))))⟩

lemma OrderIso.emptySumLex (α : Type u) [LinearOrder α] : Nonempty (Lex (PEmpty ⊕ α) ≃o α) :=
   ⟨OrderIso.ofRelIsoLT ((Sum.Lex.toLexRelIsoLT (α := PEmpty) (β := α)).trans
     (RelIso.emptySumLex (β := α) (α := PEmpty) (r := (· < ·)) (s := (· < ·))))⟩

open Classical in
lemma add_zero (o : OrderType.{u}) : o + 0 = o :=
  inductionOn o (fun α _ ↦ RelIso.ordertype_congr (choice (OrderIso.sumLexEmpty α)))

open Classical in
lemma zero_add (o : OrderType.{u}) : 0 + o = o :=
  inductionOn o (fun α _ ↦ RelIso.ordertype_congr (choice (OrderIso.emptySumLex α)))

open Classical in
lemma add_assoc (o₁ o₂ o₃ : OrderType.{u}) : o₁ + o₂ + o₃ = o₁ + (o₂ + o₃) :=
  inductionOn₃ o₁ o₂ o₃ (fun α _ β _ γ _ ↦ RelIso.ordertype_congr (OrderIso.sumLexAssoc α β γ))

instance : AddMonoid OrderType where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- `Equiv.prodCongr` promoted to an order isomorphism between lexicographic products. -/
@[simps! apply]
def OrderIso.prodLexCongr [LinearOrder α] [LinearOrder β]
    [LinearOrder γ] [LinearOrder δ] (ea : α ≃o β) (eb : γ ≃o δ) : α ×ₗ γ ≃o β ×ₗ δ where
  toEquiv := ofLex.trans ((Equiv.prodCongr ea eb).trans toLex)
  map_rel_iff' := by
    intro a b
    simp [Prod.Lex.le_iff, OrderIso.lt_iff_lt]

open Classical in
instance : Mul OrderType where
  mul := Quotient.map₂ (fun r s ↦ ⟨(s ×ₗ r)⟩)
   (fun _ _ ha _ _ hb ↦ ⟨OrderIso.prodLexCongr (choice hb) (choice ha)⟩)

open Classical in
instance : HMul OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hMul := Quotient.map₂ (fun r s ↦ ⟨(s ×ₗ r)⟩)
   (fun _ _ ha _ _ hb ↦ ⟨OrderIso.prodLexCongr (choice hb) (choice ha)⟩)

@[simp]
lemma type_mul (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ×ₗ β) = type β * type α := rfl

def Prod.Lex.unique_prod_symm_equiv [PartialOrder α] [Preorder β] [Unique β] : (β ×ₗ α) ≃o α ×ₗ β :=
   (Prod.Lex.uniqueProd β α).trans (Prod.Lex.prodUnique α β).symm

/-- `Equiv.prodAssoc` promoted to an order isomorphism. -/
@[simps! (attr := grind =)]
def OrderIso.prodAssoc (α : Type u) (β : Type v) (γ : Type w) [LE α] [LE β] [LE γ] :
    (α × β) × γ ≃o α × (β × γ) :=
  { Equiv.prodAssoc α β γ with
    map_rel_iff' := fun {a b} ↦ by
      rcases a with ⟨⟨_ , _⟩ , _⟩ ; rcases b with ⟨⟨_, _⟩ , _⟩ ;
      simp [Equiv.prodAssoc, and_assoc] }

/-- `Equiv.prodAssoc` promoted to an order isomorphism of lexicographic products. -/
def OrderIso.prodLexAssoc (α : Type u) (β : Type v) (γ : Type w)
    [LinearOrder α] [LinearOrder β] [LinearOrder γ] : (α ×ₗ β) ×ₗ γ ≃o α ×ₗ β ×ₗ γ :=
  { OrderIso.prodAssoc α β γ with
    map_rel_iff' := fun {a b} ↦
      ⟨fun h ↦ match a,b with
      | ⟨ ⟨ _, _ ⟩, _ ⟩ , ⟨ ⟨ _, _ ⟩, _ ⟩ => by
        simp only [Prod.Lex.le_iff, Prod.Lex.lt_iff] at *
        aesop,
      fun h ↦ match a, b with
      | ⟨ ⟨ _, _ ⟩, _ ⟩ , ⟨ ⟨ _, _ ⟩, _ ⟩  => by
         simp only [Prod.Lex.le_iff] at *
         match h with
         | Or.inl h => cases h <;> aesop
         | Or.inr ⟨ h₁, h₂ ⟩ => cases h₁ ; aesop
      ⟩
   }

/-- `Equiv.sumProdDistrib` promoted to an order isomorphism of lexicographic products. -/
def OrderIso.sumProdDistrib (α : Type u) (β : Type v) (γ : Type w)
    [LinearOrder α] [LinearOrder β] [LinearOrder γ] : (α ⊕ₗ β) ×ₗ γ ≃o α ×ₗ γ ⊕ₗ β ×ₗ γ :=
  { Equiv.sumProdDistrib α β γ with
    map_rel_iff' := fun {a b} ↦ ⟨
    fun h ↦ match a, b with
    | ⟨.inlₗ a, c₁⟩ , ⟨.inlₗ b, c₂⟩ => by
      cases h;
      cases (by assumption);
      · exact Prod.Lex.left _ _ (Sum.Lex.inl ‹a < b›)
      · exact Prod.Lex.right _ ‹(Sum.inlₗ a, c₁).2 ≤ (Sum.inlₗ a, c₂).2›
    | ⟨.inlₗ a, c₁⟩ , ⟨.inrₗ b, c₂⟩ => Prod.Lex.left _ _ ( Sum.Lex.sep _ _ )
    | ⟨.inrₗ a, c₁⟩ , ⟨.inlₗ b, c₂⟩ => by cases h
    | ⟨.inrₗ a, c₁⟩ , ⟨.inrₗ b, c₂⟩ => by
      cases h;
      cases (by assumption);
      · exact Prod.Lex.left _ _ ( Sum.Lex.inr ‹a < b› )
      · exact Prod.Lex.right _ ‹(Sum.inrₗ a, c₁).2 ≤ (Sum.inrₗ a, c₂).2›
    , fun h ↦ by
      cases h;
      · cases (by assumption)
        · exact Sum.Lex.inl ( Prod.Lex.left _ _ ‹_ < _›)
        · exact Sum.Lex.inr ( Prod.Lex.left _ _ ‹_ < _›)
        · exact Sum.Lex.sep _ _
      · cases ‹Lex ( α ⊕ β )›
        cases ‹α ⊕ β› <;> simp only [ge_iff_le]
        · exact Sum.Lex.inl ( Prod.Lex.right _ ‹_ ≤ _› )
        · exact Sum.Lex.inr ( Prod.Lex.right _ ‹_ ≤ _› )⟩
    }

instance : Monoid OrderType where
  mul_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ (fun α _ β _ γ _ ↦
      RelIso.ordertype_congr (OrderIso.prodLexAssoc γ β α).symm)
  one_mul o := inductionOn o (fun α _ ↦ RelIso.ordertype_congr (Prod.Lex.prodUnique α PUnit))
  mul_one o := inductionOn o (fun α _ ↦ RelIso.ordertype_congr (Prod.Lex.uniqueProd PUnit α))

instance : LeftDistribClass OrderType where
  left_distrib := fun o₁ o₂ o₃ ↦
    inductionOn₃ o₁ o₂ o₃ (fun α _ β _ γ _ ↦ RelIso.ordertype_congr (OrderIso.sumProdDistrib β γ α))

end OrderType
