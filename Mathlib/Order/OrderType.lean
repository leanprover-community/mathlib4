/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Sum.Order
import Mathlib.Order.IsNormal
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.PPWithUniv
import Mathlib.Order.Category.LinOrd
/-!
# OrderTypes

OrderTypes are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an OrderType is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `OrderType`: the type of OrderTypes (in a given universe)
* `OrderType.type α`: given a well-founded order `r`, this is the corresponding OrderType
* `OrderType.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the OrderType
  corresponding to all elements smaller than `a`.
* `enum r ⟨o, h⟩`: given a well-order `r` on a type `α`, and an OrderType `o` strictly smaller than
  the OrderType corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using OrderTypes up to `type α`.
* `OrderType.card o`: the cardinality of an OrderType `o`.
* `OrderType.lift` lifts an OrderType in universe `u` to an OrderType in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `OrderType.liftInitialSeg`.
  For a version registering that it is a principal segment embedding if `u < v`, see
  `OrderType.liftPrincipalSeg`.
* `OrderType.omega0` or `ω` is the order type of `ℕ`. It is called this to match `Cardinal.aleph0`
  and so that the omega function can be named `OrderType.omega`. This definition is universe
  polymorphic: `OrderType.omega0.{u} : OrderType.{u}` (contrast with `ℕ : Type`, which lives in
  a specific universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
  The main properties of addition (and the other operations on OrderTypes) are stated and proved in
  `Mathlib/SetTheory/OrderType/Arithmetic.lean`.
  Here, we only introduce it and prove its basic properties to deduce the fact that the order on
  OrderTypes is total (and well founded).
* `succ o` is the successor of the OrderType `o`.
* `Cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest OrderType with this cardinality.
  It is the canonical way to represent a cardinal with an OrderType.

A conditionally complete linear order with bot structure is registered on OrderTypes, where `⊥` is
`0`, the OrderType corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notation

* `ω` is a notation for the first infinite OrderType in the scope `OrderType`.
-/

assert_not_exists Module Field

noncomputable section

open Function Cardinal Set Equiv Order
open scoped Cardinal InitialSeg

universe u v w



instance : LE PEmpty where
 le x y := False


instance : LE Empty where
 le x y := False

instance : LinearOrder PEmpty where
 le_refl x := x.elim
 le_trans x y z := x.elim
 le_antisymm x := x.elim
 le_total x y := x.elim
 toDecidableLE := Classical.decRel LE.le

instance : LinearOrder Empty where
 le x y := False
 le_refl x := x.elim
 le_trans x y z := x.elim
 le_antisymm x := x.elim
 le_total x y := x.elim
 toDecidableLE := Classical.decRel LE.le


def PEmpty_iso : PEmpty ≃o PEmpty := by trivial

structure OrdInitialSeg {α β : Type*} [LinearOrder α] [LinearOrder β] extends α ↪o β where
  /-- The order embedding is an initial segment -/
  mem_range_of_rel' : ∀ a b, b = (toEmbedding a) → b ∈ Set.range toEmbedding

variable {α : Type u} {β : Type v} {γ : Type w}



def ordIsoOfIsEmpty (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β]
    [IsEmpty β] [IsEmpty α] : α ≃o β :=
  ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩

def OrderType.ofUniqueOfIrrefl [r : LinearOrder α]
    [l : LinearOrder β] [Unique α] [Unique β] : α ≃o β :=
  ⟨Equiv.ofUnique α β, by simp⟩

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance OrderType.isEquivalent : Setoid LinOrd where
  r := fun lin_ord₁ lin_ord₂ ↦ Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `OrderType.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
def OrderType : Type (u + 1) :=
  Quotient OrderType.isEquivalent

/-- A "canonical" type order-isomorphic to the OrderType `o`, living in the same universe. This is
defined through the axiom of choice.

Use this over `Iio o` only when it is paramount to have a `Type u` rather than a `Type (u + 1)`. -/
def OrderType.toType (o : OrderType) : Type u :=
  o.out.carrier

instance linearOrder_toType (o : OrderType) : LinearOrder o.toType :=
  o.out.str

namespace OrderType

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

@[simp]
theorem type_toType (o : OrderType) : type o.toType = o :=
  o.out_eq

theorem type_eq {α β} [LinearOrder α] [LinearOrder β] :
    type α = type β ↔ Nonempty (α ≃o β) :=
  Quotient.eq'

theorem _root_.RelIso.OrderType_type_eq {α β} [LinearOrder α]
    [LinearOrder β] (h : α ≃o β) : type α = type β :=
  type_eq.2 ⟨h⟩

theorem type_eq_zero_of_empty [LinearOrder α] [IsEmpty α] : type α = 0 :=
  (ordIsoOfIsEmpty α PEmpty).OrderType_type_eq

@[simp]
theorem type_eq_zero_iff_isEmpty [LinearOrder α] : type α = 0 ↔ IsEmpty α :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero_of_empty α _⟩

theorem type_ne_zero_iff_nonempty [LinearOrder α] : type α ≠ 0 ↔ Nonempty α := by simp

theorem type_ne_zero_of_nonempty [LinearOrder α] [h : Nonempty α] : type α ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h

theorem type_pEmpty : type PEmpty = 0 :=
  rfl

theorem type_empty : type Empty = 0 :=
  type_eq_zero_of_empty

theorem type_eq_one_of_unique [LinearOrder α] [Nonempty α] [Subsingleton α] : type α = 1 := by
  cases nonempty_unique α
  exact (@ofUniqueOfIrrefl _).OrderType_type_eq

@[simp]
theorem type_eq_one_iff_unique [LinearOrder α] : type α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_eq_one_of_unique⟩

theorem type_pUnit : type PUnit = 1 :=
  rfl

theorem type_unit : type Unit = 1 :=
  rfl

@[simp]
theorem toType_empty_iff_eq_zero {o : OrderType} : IsEmpty o.toType ↔ o = 0 := by
  rw [← @type_eq_zero_iff_isEmpty o.toType, type_toType]

instance isEmpty_toType_zero : IsEmpty (toType 0) :=
  toType_empty_iff_eq_zero.2 rfl

@[simp]
theorem toType_nonempty_iff_ne_zero {o : OrderType} : Nonempty o.toType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.toType, type_toType]

protected theorem one_ne_zero : (1 : OrderType) ≠ 0 :=
  type_ne_zero_of_nonempty

instance nontrivial : Nontrivial OrderType.{u} :=
  ⟨⟨1, 0, OrderType.one_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to OrderTypes.

Not to be confused with well-founded recursion `OrderType.induction`. -/
@[elab_as_elim]
theorem inductionOn {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  Quot.inductionOn o (fun α ↦ H α)

/-- `Quotient.inductionOn₂` specialized to OrderTypes.

Not to be confused with well-founded recursion `OrderType.induction`. -/
@[elab_as_elim]
theorem inductionOn₂ {C : OrderType → OrderType → Prop} (o₁ o₂ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β], C (type α) (type β)) : C o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun α β => H α β

/-- `Quotient.inductionOn₃` specialized to OrderTypes.

Not to be confused with well-founded recursion `OrderType.induction`. -/
@[elab_as_elim]
theorem inductionOn₃ {C : OrderType → OrderType → OrderType → Prop} (o₁ o₂ o₃ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β] γ [LinearOrder γ],
      C (type α) (type β) (type γ)) : C o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ =>
    H α β γ

open Classical in
/-- To prove a result on OrderTypes, it suffices to prove it for order types of well-orders. -/
@[elab_as_elim]
theorem inductionOnLinOrd  {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  inductionOn o fun α ↦ H α

open Classical in
/-- To define a function on OrderTypes, it suffices to define them on order types of well-orders.

Since `LinearOrder` is data-carrying, `liftOnLinOrd_type` is not a definitional equality, unlike
`Quotient.liftOn_mk` which is always def-eq. -/
def liftOnLinOrd {δ : Sort v} (o : OrderType) (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) : δ :=
  Quotient.liftOn o (fun w ↦ f w)
    fun w₁ w₂ h ↦ c w₁ w₂ (Quotient.sound h)

@[simp]
theorem liftOnLinOrd_type {δ : Sort v} (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) {γ} [LinearOrder γ] :
    liftOnLinOrd (type γ) f c = f γ := by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
