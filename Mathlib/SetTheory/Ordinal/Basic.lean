/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.IsNormal
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.PPWithUniv

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `Ordinal`: the type of ordinals (in a given universe)
* `Ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `Ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r ⟨o, h⟩`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `Ordinal.card o`: the cardinality of an ordinal `o`.
* `Ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `Ordinal.liftInitialSeg`.
  For a version registering that it is a principal segment embedding if `u < v`, see
  `Ordinal.liftPrincipalSeg`.
* `Ordinal.omega0` or `ω` is the order type of `ℕ`. It is called this to match `Cardinal.aleph0`
  and so that the omega function can be named `Ordinal.omega`. This definition is universe
  polymorphic: `Ordinal.omega0.{u} : Ordinal.{u}` (contrast with `ℕ : Type`, which lives in
  a specific universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
  The main properties of addition (and the other operations on ordinals) are stated and proved in
  `Mathlib/SetTheory/Ordinal/Arithmetic.lean`.
  Here, we only introduce it and prove its basic properties to deduce the fact that the order on
  ordinals is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `Cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notation

* `ω` is a notation for the first infinite ordinal in the scope `Ordinal`.
-/

@[expose] public section

assert_not_exists Module Field

noncomputable section

open Function Cardinal Set Equiv Order
open scoped Cardinal InitialSeg

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Definition of ordinals -/


/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure WellOrder : Type (u + 1) where
  /-- The underlying type of the order. -/
  α : Type u
  /-- The underlying relation of the order. -/
  r : α → α → Prop
  /-- The proposition that `r` is a well-ordering for `α`. -/
  wo : IsWellOrder α r

attribute [instance] WellOrder.wo

namespace WellOrder

instance inhabited : Inhabited WellOrder :=
  ⟨⟨PEmpty, _, inferInstanceAs (IsWellOrder PEmpty emptyRelation)⟩⟩

end WellOrder

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance Ordinal.isEquivalent : Setoid WellOrder where
  r := fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
def Ordinal : Type (u + 1) :=
  Quotient Ordinal.isEquivalent

/-- A "canonical" type order-isomorphic to the ordinal `o`, living in the same universe. This is
defined through the axiom of choice; in particular, it has no useful def-eqs, and it is not exposed.

Use this over `Iio o` only when it is paramount to have a `Type u` rather than a `Type (u + 1)`,
and convert using

```
Ordinal.ToType.mk : Iio o → o.ToType
Ordinal.ToType.toOrd : o.ToType → Iio o
```
-/
@[no_expose]
def Ordinal.ToType (o : Ordinal.{u}) : Type u :=
  o.out.α

@[deprecated (since := "2025-12-04")]
alias Ordinal.toType := Ordinal.ToType

@[no_expose]
instance linearOrder_toType (o : Ordinal) : LinearOrder o.ToType :=
  @IsWellOrder.linearOrder _ o.out.r o.out.wo

instance wellFoundedLT_toType (o : Ordinal) : WellFoundedLT o.ToType :=
  o.out.wo.toIsWellFounded

instance hasWellFounded_toType (o : Ordinal) : WellFoundedRelation o.ToType :=
  WellFoundedLT.toWellFoundedRelation

namespace Ordinal

@[no_expose]
noncomputable instance (o : Ordinal) : SuccOrder o.ToType :=
  .ofLinearWellFoundedLT _

/-! ### Basic properties of the order type -/

/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧

/-- `typeLT α` is an abbreviation for the order type of the `<` relation of `α`. -/
scoped notation "typeLT " α:70 => @Ordinal.type α (· < ·) inferInstance

instance zero : Zero Ordinal :=
  ⟨type <| @emptyRelation PEmpty⟩

instance inhabited : Inhabited Ordinal :=
  ⟨0⟩

instance one : One Ordinal :=
  ⟨type <| @emptyRelation PUnit⟩

@[simp]
theorem type_toType (o : Ordinal) : typeLT o.ToType = o :=
  o.out_eq

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'

theorem _root_.RelIso.ordinal_type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩

theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinal_type_eq

@[simp]
theorem type_eq_zero_iff_isEmpty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero_of_empty α r _⟩

theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α := by simp

theorem type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h

theorem type_pEmpty : type (@emptyRelation PEmpty) = 0 :=
  rfl

theorem type_empty : type (@emptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _

theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Nonempty α] [Subsingleton α] : type r = 1 := by
  cases nonempty_unique α
  exact (RelIso.ofUniqueOfIrrefl r _).ordinal_type_eq

@[simp]
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_eq_one_of_unique r⟩

theorem type_pUnit : type (@emptyRelation PUnit) = 1 :=
  rfl

theorem type_unit : type (@emptyRelation Unit) = 1 :=
  rfl

@[simp]
theorem isEmpty_toType_iff {o : Ordinal} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero_iff_isEmpty o.ToType (· < ·), type_toType]

@[deprecated (since := "2026-02-18")] alias toType_empty_iff_eq_zero := isEmpty_toType_iff

instance isEmpty_toType_zero : IsEmpty (ToType 0) :=
  isEmpty_toType_iff.2 rfl

@[simp]
theorem nonempty_toType_iff {o : Ordinal} : Nonempty o.ToType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.ToType (· < ·), type_toType]

@[deprecated (since := "2026-02-18")] alias toType_nonempty_iff_ne_zero := nonempty_toType_iff

protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  type_ne_zero_of_nonempty _

instance nontrivial : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, Ordinal.one_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
theorem inductionOn {motive : Ordinal → Prop} (o : Ordinal)
    (type : ∀ (α r) [IsWellOrder α r], motive (type r)) : motive o :=
  Quot.inductionOn o fun ⟨α, r, _⟩ ↦ type α r

/-- `Quotient.inductionOn₂` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
theorem inductionOn₂ {motive : Ordinal → Ordinal → Prop} (o₁ o₂ : Ordinal)
    (type : ∀ (α r) [IsWellOrder α r] (β s) [IsWellOrder β s], motive (type r) (type s)) :
    motive o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ↦ type α r β s

/-- `Quotient.inductionOn₃` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
theorem inductionOn₃ {motive : Ordinal → Ordinal → Ordinal → Prop} (o₁ o₂ o₃ : Ordinal)
    (type : ∀ (α r) [IsWellOrder α r] (β s) [IsWellOrder β s] (γ t) [IsWellOrder γ t],
      motive (type r) (type s) (type t)) : motive o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ↦ type α r β s γ t

open Classical in
/-- To prove a result on ordinals, it suffices to prove it for order types of well-orders. -/
@[elab_as_elim]
theorem inductionOnWellOrder {motive : Ordinal → Prop} (o : Ordinal)
    (type : ∀ (α) [LinearOrder α] [WellFoundedLT α], motive (typeLT α)) : motive o :=
  inductionOn o fun α r wo ↦ @type α (linearOrderOfSTO r) wo.toIsWellFounded

open Classical in
/-- To define a function on ordinals, it suffices to define them on order types of well-orders.

Since `LinearOrder` is data-carrying, `liftOnWellOrder_type` is not a definitional equality, unlike
`Quotient.liftOn_mk` which is always def-eq. -/
def liftOnWellOrder {δ : Sort v} (o : Ordinal) (f : ∀ (α) [LinearOrder α] [WellFoundedLT α], δ)
    (c : ∀ (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β],
      typeLT α = typeLT β → f α = f β) : δ :=
  Quotient.liftOn o (fun w ↦ @f w.α (linearOrderOfSTO w.r) w.wo.toIsWellFounded)
    fun w₁ w₂ h ↦ @c
      w₁.α (linearOrderOfSTO w₁.r) w₁.wo.toIsWellFounded
      w₂.α (linearOrderOfSTO w₂.r) w₂.wo.toIsWellFounded
      (Quotient.sound h)

@[simp]
theorem liftOnWellOrder_type {δ : Sort v} (f : ∀ (α) [LinearOrder α] [WellFoundedLT α], δ)
    (c : ∀ (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β],
      typeLT α = typeLT β → f α = f β) {γ} [LinearOrder γ] [WellFoundedLT γ] :
    liftOnWellOrder (typeLT γ) f c = f γ := by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
  congr
  exact LinearOrder.ext_lt fun _ _ ↦ Iff.rfl

/-! ### The order on ordinals -/

/--
For `Ordinal`:

* less-equal is defined such that well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an *initial* segment of `s`.
* less-than is defined such that well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a *principal* segment of `s`.

Note that most of the relevant results on initial and principal segments are proved in the
`Mathlib/Order/InitialSeg.lean` file.
-/
instance partialOrder : PartialOrder Ordinal where
  le a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≼i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
        ⟨fun ⟨h⟩ => ⟨f.symm.toInitialSeg.trans <| h.trans g.toInitialSeg⟩, fun ⟨h⟩ =>
          ⟨f.toInitialSeg.trans <| h.trans g.symm.toInitialSeg⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≺i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
        ⟨fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f.symm <| h.transRelIso g⟩,
          fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f <| h.transRelIso g.symm⟩⟩
  le_refl := Quot.ind fun ⟨_, _, _⟩ => ⟨InitialSeg.refl _⟩
  le_trans a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  lt_iff_le_not_ge a b :=
    Quotient.inductionOn₂ a b fun _ _ =>
      ⟨fun ⟨f⟩ => ⟨⟨f⟩, fun ⟨g⟩ => (f.transInitial g).irrefl⟩, fun ⟨⟨f⟩, h⟩ =>
        f.principalSumRelIso.recOn (fun g => ⟨g⟩) fun g => (h ⟨g.symm.toInitialSeg⟩).elim⟩
  le_antisymm a b :=
    Quotient.inductionOn₂ a b fun _ _ ⟨h₁⟩ ⟨h₂⟩ =>
      Quot.sound ⟨InitialSeg.antisymm h₁ h₂⟩

instance : LinearOrder Ordinal :=
  { inferInstanceAs (PartialOrder Ordinal) with
    le_total := fun a b => Quotient.inductionOn₂ a b fun ⟨_, r, _⟩ ⟨_, s, _⟩ =>
      (InitialSeg.total r s).recOn (fun f => Or.inl ⟨f⟩) fun f => Or.inr ⟨f⟩
    toDecidableLE := Classical.decRel _ }

theorem _root_.InitialSeg.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≼i s) : type r ≤ type s :=
  ⟨h⟩

theorem _root_.RelEmbedding.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ↪r s) : type r ≤ type s :=
  ⟨h.collapse⟩

theorem _root_.PrincipalSeg.ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≺i s) : type r < type s :=
  ⟨h⟩

instance : OrderBot Ordinal where
  bot := 0
  bot_le o := inductionOn o fun _ r _ ↦ (InitialSeg.ofIsEmpty _ r).ordinal_type_le

@[simp]
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl

instance instIsEmptyIioZero : IsEmpty (Iio (0 : Ordinal)) := by
  simp [← bot_eq_zero]

@[deprecated nonpos_iff_eq_zero (since := "2025-11-21")]
protected theorem le_zero {o : Ordinal} : o ≤ 0 ↔ o = 0 :=
  le_bot_iff


@[deprecated not_neg (since := "2025-11-21")]
protected theorem not_lt_zero (o : Ordinal) : ¬o < 0 :=
  not_lt_bot

@[deprecated eq_zero_or_pos (since := "2025-11-21")]
protected theorem eq_zero_or_pos : ∀ a : Ordinal, a = 0 ∨ 0 < a := eq_bot_or_bot_lt

instance : ZeroLEOneClass Ordinal :=
  ⟨bot_le⟩

instance instNeZeroOne : NeZero (1 : Ordinal) :=
  ⟨Ordinal.one_ne_zero⟩

theorem type_le_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl

theorem type_le_iff' {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩

theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl

/-- Given two ordinals `α ≤ β`, then `initialSegToType α β` is the initial segment embedding of
`α.ToType` into `β.ToType`. -/
def initialSegToType {α β : Ordinal} (h : α ≤ β) : α.ToType ≤i β.ToType := by
  apply Classical.choice (type_le_iff.mp _)
  rwa [type_toType, type_toType]

/-- Given two ordinals `α < β`, then `principalSegToType α β` is the principal segment embedding
of `α.ToType` into `β.ToType`. -/
def principalSegToType {α β : Ordinal} (h : α < β) : α.ToType <i β.ToType := by
  apply Classical.choice (type_lt_iff.mp _)
  rwa [type_toType, type_toType]

/-! ### Enumerating elements in a well-order with ordinals -/

/-- The order type of an element inside a well order.

This is registered as a principal segment embedding into the ordinals, with top `type r`. -/
def typein (r : α → α → Prop) [IsWellOrder α r] : @PrincipalSeg α Ordinal.{u} r (· < ·) := by
  refine ⟨RelEmbedding.ofMonotone _ fun a b ha ↦
    ((PrincipalSeg.ofElement r a).codRestrict _ ?_ ?_).ordinal_type_lt, type r, fun a ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc⟩
    exact trans hc ha
  · exact ha
  · rintro ⟨b, rfl⟩
    exact (PrincipalSeg.ofElement _ _).ordinal_type_lt
  · refine inductionOn a ?_
    rintro β s wo ⟨g⟩
    exact ⟨_, g.subrelIso.ordinal_type_eq⟩

@[simp]
theorem type_subrel (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    type (Subrel r (r · a)) = typein r a :=
  rfl

@[simp]
theorem top_typein (r : α → α → Prop) [IsWellOrder α r] : (typein r).top = type r :=
  rfl

theorem typein_lt_type (r : α → α → Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  (typein r).lt_top a

theorem typein_lt_self {o : Ordinal} (i : o.ToType) : typein (α := o.ToType) (· < ·) i < o := by
  simp_rw [← type_toType o]
  apply typein_lt_type

@[simp]
theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : typein s f.top = type r :=
  f.subrelIso.ordinal_type_eq

@[simp]
theorem typein_lt_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} :
    typein r a < typein r b ↔ r a b :=
  (typein r).map_rel_iff

@[simp]
theorem typein_le_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} :
    typein r a ≤ typein r b ↔ ¬r b a := by
  rw [← not_lt, typein_lt_typein]

theorem typein_injective (r : α → α → Prop) [IsWellOrder α r] : Injective (typein r) :=
  (typein r).injective

theorem typein_inj (r : α → α → Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff

theorem mem_range_typein_iff (r : α → α → Prop) [IsWellOrder α r] {o} :
    o ∈ Set.range (typein r) ↔ o < type r :=
  (typein r).mem_range_iff_rel

theorem typein_surj (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    o ∈ Set.range (typein r) :=
  (typein r).mem_range_of_rel_top h

theorem typein_surjOn (r : α → α → Prop) [IsWellOrder α r] :
    Set.SurjOn (typein r) Set.univ (Set.Iio (type r)) :=
  (typein r).surjOn

@[simp]
theorem type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : α) :
    type (α := Iio x) LT.lt = typein LT.lt x :=
  rfl

/-- A well order `r` is order-isomorphic to the set of ordinals smaller than `type r`.
`enum r ⟨o, h⟩` is the `o`-th element of `α` ordered by `r`.

That is, `enum` maps an initial segment of the ordinals, those less than the order type of `r`, to
the elements of `α`. -/
@[simps! symm_apply_coe]
def enum (r : α → α → Prop) [IsWellOrder α r] : (· < · : Iio (type r) → Iio (type r) → Prop) ≃r r :=
  (typein r).subrelIso

@[simp]
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r ⟨o, h⟩) = o :=
  (typein r).apply_subrelIso _

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : s ≺i r) {h : type s < type r} : enum r ⟨type s, h⟩ = f.top :=
  (typein r).injective <| (typein_enum _ _).trans (typein_top _).symm

@[simp]
theorem enum_typein (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    enum r ⟨typein r a, typein_lt_type r a⟩ = a :=
  enum_type (PrincipalSeg.ofElement r a)

theorem enum_lt_enum {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    r (enum r o₁) (enum r o₂) ↔ o₁ < o₂ :=
  (enum _).map_rel_iff

theorem enum_le_enum (r : α → α → Prop) [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    ¬r (enum r o₁) (enum r o₂) ↔ o₂ ≤ o₁ := by
  rw [enum_lt_enum (r := r), not_lt]

-- TODO: generalize to other well-orders
@[simp]
theorem enum_le_enum' (a : Ordinal) {o₁ o₂ : Iio (type (· < ·))} :
    enum (· < ·) o₁ ≤ enum (α := a.ToType) (· < ·) o₂ ↔ o₁ ≤ o₂ := by
  rw [← enum_le_enum, not_lt]

theorem enum_inj {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    enum r o₁ = enum r o₂ ↔ o₁ = o₂ :=
  EmbeddingLike.apply_eq_iff_eq _

theorem enum_zero_le {r : α → α → Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) :
    ¬r a (enum r ⟨0, h0⟩) := by
  rw [← enum_typein r a, enum_le_enum r]
  exact bot_le (α := Ordinal)

theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.ToType) :
    enum (α := o.ToType) (· < ·) ⟨0, type_toType _ ▸ h0⟩ ≤ a := by
  rw [← not_lt]
  apply enum_zero_le

theorem relIso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) :
    ∀ (hr : o < type r) (hs : o < type s), f (enum r ⟨o, hr⟩) = enum s ⟨o, hs⟩ := by
  refine inductionOn o ?_; rintro γ t wo ⟨g⟩ ⟨h⟩
  rw [enum_type g, enum_type (g.transRelIso f)]; rfl

theorem relIso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r ⟨o, hr⟩) = enum s ⟨o, hr.trans_eq (Quotient.sound ⟨f⟩)⟩ :=
  relIso_enum' _ _ _ _

/-- The order isomorphism between ordinals less than `o` and `o.ToType`. -/
@[simps! -isSimp]
def ToType.mk {o : Ordinal} : Set.Iio o ≃o o.ToType where
  toFun x := enum (α := o.ToType) (· < ·) ⟨x.1, type_toType _ ▸ x.2⟩
  invFun x := ⟨typein (α := o.ToType) (· < ·) x, typein_lt_self x⟩
  left_inv _ := Subtype.ext (typein_enum _ _)
  right_inv _ := enum_typein _ _
  map_rel_iff' := enum_le_enum' _

@[deprecated (since := "2025-12-04")] noncomputable alias enumIsoToType := ToType.mk

/-- Convert an element of `α.toType` to the corresponding `Ordinal` -/
abbrev ToType.toOrd {o : Ordinal} (α : o.ToType) : Set.Iio o := ToType.mk.symm α

instance (o : Ordinal) : Coe o.ToType (Set.Iio o) where
  coe := ToType.toOrd
instance (o : Ordinal) : CoeOut o.ToType Ordinal where
  coe x := x.toOrd

instance small_Iio (o : Ordinal.{u}) : Small.{u} (Iio o) :=
  ⟨_, ⟨ToType.mk.toEquiv⟩⟩

instance small_Iic (o : Ordinal.{u}) : Small.{u} (Iic o) := by
  rw [← Iio_union_right]
  infer_instance

instance small_Ico (a b : Ordinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
instance small_Icc (a b : Ordinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
instance small_Ioo (a b : Ordinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self
instance small_Ioc (a b : Ordinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self

/-- `o.ToType` is an `OrderBot` whenever `o ≠ 0`. -/
@[implicit_reducible]
def toTypeOrderBot {o : Ordinal} (ho : o ≠ 0) : OrderBot o.ToType where
  bot := (enum (· < ·)) ⟨0, _⟩
  bot_le := enum_zero_le' (bot_lt_iff_ne_bot.2 ho)

theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (α := o.ToType) (· < ·) ⟨0, by rwa [type_toType]⟩ =
      have H := toTypeOrderBot (o := o) (by rintro rfl; simp at ho)
      (⊥ : o.ToType) :=
  rfl

theorem lt_wf : @WellFounded Ordinal (· < ·) :=
  wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ ↦
    RelHomClass.wellFounded (enum _) wo.wf)

instance wellFoundedRelation : WellFoundedRelation Ordinal :=
  ⟨(· < ·), lt_wf⟩

instance wellFoundedLT : WellFoundedLT Ordinal :=
  ⟨lt_wf⟩

instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[deprecated WellFoundedLT.induction (since := "2026-02-27")]
theorem induction {p : Ordinal.{u} → Prop} (i : Ordinal.{u}) (h : ∀ j, (∀ k, k < j → p k) → p j) :
    p i :=
  WellFoundedLT.induction i h

theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) : typein s (f a) = typein r a := by
  rw [← f.transPrincipal_apply _ a, (f.transPrincipal _).eq]

/-! ### Cardinality of ordinals -/

/-- The cardinal of an ordinal is the cardinality of any type on which a relation with that order
type is defined. -/
def card : Ordinal → Cardinal :=
  Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩

@[simp]
theorem card_type (r : α → α → Prop) [IsWellOrder α r] : card (type r) = #α :=
  rfl

@[simp]
theorem card_typein {r : α → α → Prop} [IsWellOrder α r] (x : α) :
    #{ y // r y x } = (typein r x).card :=
  rfl

@[gcongr]
theorem card_le_card {o₁ o₂ : Ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

@[simp]
theorem card_zero : card 0 = 0 := mk_eq_zero _

@[simp]
theorem card_one : card 1 = 1 := mk_eq_one _

variable (r) in
/-- The cardinality of a set is an upper-bound for the cardinality of the order type of the set's
mex (minimum excluded value). See `not_lt_enum_ord_mk_min_compl` for the `α` version. -/
theorem card_typein_min_le_mk [IsWellOrder α r] {s : Set α} (hs : sᶜ.Nonempty) :
    (typein r <| IsWellFounded.wf.min (r := r) sᶜ hs).card ≤ #s :=
  IsWellFounded.wf.cardinalMk_subtype_lt_min_compl_le hs

/-! ### Lifting ordinals to a higher universe -/

/-- The universe lift operation for ordinals, which embeds `Ordinal.{u}` as
  a proper initial segment of `Ordinal.{v}` for `v > u`. For the initial segment version,
  see `liftInitialSeg`. -/
@[pp_with_univ]
def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  Quotient.liftOn o (fun w => type <| ULift.down ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩

@[simp]
theorem type_ulift (r : α → α → Prop) [IsWellOrder α r] :
    type (ULift.down ⁻¹'o r) = lift.{v} (type r) :=
  rfl

@[deprecated (since := "2026-02-20")] alias type_uLift := type_ulift

@[simp]
theorem type_lt_ulift [LinearOrder α] [WellFoundedLT α] :
    typeLT (ULift α) = lift.{v} (typeLT α) :=
  rfl

theorem _root_.RelIso.ordinal_lift_type_eq {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) : lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinal_type_eq

@[simp]
theorem type_preimage {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinal_type_eq

@[simp]
theorem type_lift_preimage (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

/-- `lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't seem to work. -/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩

/-- An ordinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work. -/
theorem lift_id' (a : Ordinal) : lift a = a :=
  inductionOn a fun _ r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩

/-- An ordinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id : ∀ a, lift.{u, u} a = a :=
  lift_id'.{u, u}

/-- An ordinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Ordinal.{u}) : lift.{0} a = a :=
  lift_id' a

theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ Nonempty (r ≼i s) := by
  constructor <;> refine fun ⟨f⟩ ↦ ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).toInitialSeg)
  · exact (RelIso.preimage Equiv.ulift r).toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).symm.toInitialSeg)

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) := by
  refine Quotient.eq'.trans ⟨?_, ?_⟩ <;> refine fun ⟨f⟩ ↦ ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.trans <| f.trans (RelIso.preimage Equiv.ulift s)
  · exact (RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm

theorem lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s) := by
  constructor <;> refine fun ⟨f⟩ ↦ ⟨?_⟩
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r).symm).transInitial
      (RelIso.preimage Equiv.ulift s).toInitialSeg
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r)).transInitial
      (RelIso.preimage Equiv.ulift s).symm.toInitialSeg

@[simp]
theorem lift_le {a b : Ordinal} : lift.{u, v} a ≤ lift.{u, v} b ↔ a ≤ b :=
  inductionOn₂ a b fun α r _ β s _ => by
    rw [← lift_umax]
    exact lift_type_le.{_, _, u}

@[simp]
theorem lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v} b ↔ a = b := by
  simp_rw [le_antisymm_iff, lift_le]

@[simp]
theorem lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b ↔ a < b := by
  simp_rw [lt_iff_le_not_ge, lift_le]

@[simp]
theorem lift_typein_top {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : lift.{u} (typein s f.top) = lift (type r) :=
  f.subrelIso.ordinal_lift_type_eq

/-- Initial segment version of the lift operation on ordinals, embedding `Ordinal.{u}` in
`Ordinal.{v}` as an initial segment when `u ≤ v`. -/
def liftInitialSeg : Ordinal.{v} ≤i Ordinal.{max u v} := by
  refine ⟨RelEmbedding.ofMonotone lift.{u} (by simp),
    fun a b ↦ Ordinal.inductionOn₂ a b fun α r _ β s _ h ↦ ?_⟩
  rw [RelEmbedding.ofMonotone_coe, ← lift_id'.{max u v} (type s),
    ← lift_umax.{v, u}, lift_type_lt] at h
  obtain ⟨f⟩ := h
  use typein r f.top
  rw [RelEmbedding.ofMonotone_coe, ← lift_umax, lift_typein_top, lift_id']

@[simp]
theorem liftInitialSeg_coe : (liftInitialSeg.{v, u} : Ordinal → Ordinal) = lift.{v, u} :=
  rfl

@[simp]
theorem lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  (liftInitialSeg.trans liftInitialSeg).eq liftInitialSeg a

@[simp]
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _

@[simp]
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _

@[simp]
theorem lift_card (a) : Cardinal.lift.{u, v} (card a) = card (lift.{u} a) :=
  inductionOn a fun _ _ _ => rfl

theorem mem_range_lift_of_le {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b ≤ lift.{v} a) :
    b ∈ Set.range lift.{v} :=
  liftInitialSeg.mem_range_of_le h

theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b ≤ lift.{v} a ↔ ∃ a' ≤ a, lift.{v} a' = b :=
  liftInitialSeg.le_apply_iff

theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b < lift.{v} a ↔ ∃ a' < a, lift.{v} a' = b :=
  liftInitialSeg.lt_apply_iff

/-! ### The first infinite ordinal ω -/

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega0 : Ordinal.{u} :=
  lift (typeLT ℕ)

@[inherit_doc] scoped notation "ω" => Ordinal.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

/-- Note that the presence of this lemma makes `simp [omega0]` form a loop. -/
@[simp]
theorem type_nat_lt : typeLT ℕ = ω :=
  (lift_id _).symm

@[simp]
theorem card_omega0 : card ω = ℵ₀ :=
  rfl

@[simp]
theorem lift_omega0 : lift ω = ω :=
  lift_lift _

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`Mathlib/SetTheory/Ordinal/Arithmetic.lean`.
-/


/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
every element of `o₁` is smaller than every element of `o₂`. -/
instance add : Add Ordinal.{u} :=
  ⟨fun o₁ o₂ => Quotient.liftOn₂ o₁ o₂ (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => type (Sum.Lex r s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => (RelIso.sumLexCongr f g).ordinal_type_eq⟩

instance addMonoidWithOne : AddMonoidWithOne Ordinal.{u} where
  zero_add o := inductionOn o fun α _ _ => (RelIso.emptySumLex _ _).ordinal_type_eq
  add_zero o := inductionOn o fun α _ _ => (RelIso.sumLexEmpty _ _).ordinal_type_eq
  add_assoc o₁ o₂ o₃ :=
    Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quot.sound
        ⟨⟨sumAssoc _ _ _, by
          intro a b
          rcases a with (⟨a | a⟩ | a) <;> rcases b with (⟨b | b⟩ | b) <;>
            simp only [sumAssoc_apply_inl_inl, sumAssoc_apply_inl_inr, sumAssoc_apply_inr,
              Sum.lex_inl_inl, Sum.lex_inr_inr, Sum.Lex.sep, Sum.lex_inr_inl]⟩⟩
  nsmul := nsmulRec

@[simp]
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  inductionOn₂ o₁ o₂ fun _ _ _ _ _ _ ↦ rfl

theorem card_add_one (o : Ordinal) : card (o + 1) = card o + 1 := by
  simp

@[simp]
theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s :=
  rfl

@[simp]
theorem card_nat (n : ℕ) : card.{u} n = n := by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]

@[simp]
theorem card_ofNat (n : ℕ) [n.AtLeastTwo] :
    card.{u} ofNat(n) = OfNat.ofNat n :=
  card_nat n

instance instAddLeftMono : AddLeftMono Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦
      (RelEmbedding.ofMonotone (Sum.recOn · Sum.inl (Sum.inr ∘ f)) ?_).ordinal_type_le
    simp [f.map_rel_iff]

instance instAddRightMono : AddRightMono Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦
      (RelEmbedding.ofMonotone (Sum.recOn · (Sum.inl ∘ f) Sum.inr) ?_).ordinal_type_le
    simp [f.map_rel_iff]

instance existsAddOfLE : ExistsAddOfLE Ordinal where
  exists_add_of_le {a b} := by
    refine inductionOn₂ a b fun α r _ β s _ ⟨f⟩ ↦ ?_
    obtain ⟨γ, t, _, ⟨g⟩⟩ := f.exists_sum_relIso
    exact ⟨type t, g.ordinal_type_eq.symm⟩

instance canonicallyOrderedAdd : CanonicallyOrderedAdd Ordinal where
  le_add_self a b := by simpa using add_le_add_left bot_le a
  le_self_add a b := by simpa using add_le_add_right bot_le a

@[deprecated le_self_add (since := "2025-11-21")]
protected theorem le_add_right (a b : Ordinal) : a ≤ a + b := le_self_add

@[deprecated le_add_self (since := "2025-11-21")]
protected theorem le_add_left (a b : Ordinal) : a ≤ b + a := le_add_self

theorem max_zero_left : ∀ a : Ordinal, max 0 a = a :=
  max_bot_left

theorem max_zero_right : ∀ a : Ordinal, max a 0 = a :=
  max_bot_right

@[simp]
theorem max_eq_zero {a b : Ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  max_eq_bot

@[simp]
theorem sInf_empty : sInf (∅ : Set Ordinal) = 0 :=
  dif_neg Set.not_nonempty_empty

/-! ### Successor order properties -/

private theorem succ_le_iff' {a b : Ordinal} : a + 1 ≤ b ↔ a < b := by
  refine inductionOn₂ a b fun α r _ β s _ ↦ ⟨?_, ?_⟩ <;> rintro ⟨f⟩
  · refine ⟨((InitialSeg.leAdd _ _).trans f).toPrincipalSeg fun h ↦ ?_⟩
    simpa using h (f (Sum.inr PUnit.unit))
  · apply (RelEmbedding.ofMonotone (Sum.recOn · f fun _ ↦ f.top) ?_).ordinal_type_le
    simpa [f.map_rel_iff] using f.lt_top

instance : NoMaxOrder Ordinal :=
  ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

instance : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) (by exact succ_le_iff')

instance : SuccAddOrder Ordinal := ⟨fun _ => rfl⟩

@[deprecated succ_eq_add_one (since := "2026-02-26")]
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl

@[deprecated zero_add (since := "2026-02-26")]
theorem succ_zero : succ (0 : Ordinal) = 1 :=
  zero_add 1

@[deprecated one_add_one_eq_two (since := "2026-02-26")]
theorem succ_one : succ (1 : Ordinal) = 2 := one_add_one_eq_two

@[deprecated add_assoc (since := "2026-02-26")]
theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assoc _ _ _).symm

theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 := by
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]

theorem succ_pos (o : Ordinal) : 0 < succ o :=
  bot_lt_succ o

-- TODO: generalize to `SuccAddOrder`
theorem add_one_ne_zero (o : Ordinal) : o + 1 ≠ 0 :=
  (succ_pos o).ne'

@[deprecated add_one_ne_zero (since := "2026-02-27")]
theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  add_one_ne_zero o

@[simp]
theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 := by
  simpa using @lt_succ_bot_iff _ _ _ a _ _

theorem le_one_iff {a : Ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 := by
  simpa using @le_succ_bot_iff _ _ _ a _

@[deprecated card_add_one (since := "2026-02-27")]
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp

theorem natCast_succ (n : ℕ) : ↑n.succ = succ (n : Ordinal) :=
  rfl

instance uniqueIioOne : Unique (Iio (1 : Ordinal)) where
  default := ⟨0, zero_lt_one' Ordinal⟩
  uniq a := Subtype.ext <| lt_one_iff_zero.1 a.2

@[simp]
theorem Iio_one_default_eq : (default : Iio (1 : Ordinal)) = ⟨0, zero_lt_one' Ordinal⟩ :=
  rfl

instance uniqueToTypeOne : Unique (ToType 1) where
  default := enum (α := ToType 1) (· < ·) ⟨0, by simp⟩
  uniq a := by
    rw [← enum_typein (α := ToType 1) (· < ·) a]
    congr
    rw [← lt_one_iff_zero]
    apply typein_lt_self

theorem one_toType_eq (x : ToType 1) : x = enum (· < ·) ⟨0, by simp⟩ :=
  Unique.eq_default x

theorem type_lt_mem_range_succ_iff [LinearOrder α] [WellFoundedLT α] :
    typeLT α ∈ range succ ↔ ∃ x : α, IsMax x := by
  simp_rw [← isTop_iff_isMax]
  constructor <;> intro ⟨a, ha⟩
  · refine ⟨enum (α := α) (· < ·) ⟨a, ?_⟩, fun b ↦ ?_⟩
    · rw [mem_Iio, ← ha, lt_succ_iff]
    · rw [← enum_typein (α := α) (· < ·) b, ← not_lt, enum_le_enum (r := (· < ·)),
        Subtype.mk_le_mk, ← lt_succ_iff, ha]
      exact typein_lt_type ..
  · refine ⟨typein (α := α) (· < ·) a, eq_of_forall_lt_iff fun o ↦ ?_⟩
    rw [lt_succ_iff]
    refine ⟨fun h ↦ h.trans_lt (typein_lt_type _ _), fun h ↦ ?_⟩
    rw [← typein_enum _ h, typein_le_typein, not_lt]
    apply ha

theorem type_lt_mem_range_succ [LinearOrder α] [WellFoundedLT α] [OrderTop α] :
    typeLT α ∈ range succ :=
  type_lt_mem_range_succ_iff.2 ⟨⊤, isMax_top⟩

theorem isSuccPrelimit_type_lt_iff [LinearOrder α] [WellFoundedLT α] :
    IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α := by
  rw [← not_iff_not, noMaxOrder_iff, not_isSuccPrelimit_iff', type_lt_mem_range_succ_iff]
  simp [IsMax]

theorem isSuccPrelimit_type_lt [LinearOrder α] [WellFoundedLT α] [h : NoMaxOrder α] :
    IsSuccPrelimit (typeLT α) :=
  isSuccPrelimit_type_lt_iff.2 h

/-! ### Extra properties of typein and enum -/

-- TODO: use `ToType.mk` for lemmas on `ToType` rather than `enum` and `typein`.

@[simp]
theorem typein_one_toType (x : ToType 1) : typein (α := ToType 1) (· < ·) x = 0 := by
  rw [one_toType_eq x, typein_enum]

theorem typein_le_typein' (o : Ordinal) {x y : o.ToType} :
    typein (α := o.ToType) (· < ·) x ≤ typein (α := o.ToType) (· < ·) y ↔ x ≤ y := by
  simp

theorem le_enum_succ {o : Ordinal} (a : (succ o).ToType) :
    a ≤ enum (α := (succ o).ToType) (· < ·) ⟨o, (type_toType _ ▸ lt_succ o)⟩ := by
  rw [← enum_typein (α := (succ o).ToType) (· < ·) a, enum_le_enum', Subtype.mk_le_mk,
    ← lt_succ_iff]
  apply typein_lt_self

/-! ### Universal ordinal -/

-- intended to be used with explicit universe parameters
/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `Ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
@[pp_with_univ, nolint checkUnivs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (typeLT Ordinal)

theorem univ_id : univ.{u, u + 1} = typeLT Ordinal :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `Ordinal.{u}` in
`Ordinal.{v}` as a principal segment when `u < v`. -/
def liftPrincipalSeg : Ordinal.{u} <i Ordinal.{max (u + 1) v} :=
  ⟨↑liftInitialSeg.{max (u + 1) v, u}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · obtain ⟨a, e⟩ := h
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein r⟩
    · rw [← lift_id (type s)] at h ⊢
      obtain ⟨f⟩ := lift_type_lt.{_,_,v}.1 h
      obtain ⟨f, a, hf⟩ := f
      exists a
      induction a using inductionOn with | type α r
      refine lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
        ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ ?_) ?_).symm⟩
      · exact fun b => enum r ⟨f b, (hf _).1 ⟨_, rfl⟩⟩
      · refine fun a b h => (typein_lt_typein r).1 ?_
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        obtain ⟨b, e⟩ := (hf _).2 (typein_lt_type _ a')
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]⟩

@[simp]
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

@[simp]
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{u, v}).top = univ.{u, v} :=
  rfl

theorem liftPrincipalSeg_top' : liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal := by
  simp only [liftPrincipalSeg_top, univ_id]

end Ordinal

/-! ### Representing a cardinal with an ordinal -/


namespace Cardinal

open Ordinal

@[simp]
theorem mk_toType (o : Ordinal) : #o.ToType = o.card :=
  (Ordinal.card_type _).symm.trans <| by rw [Ordinal.type_toType]

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
@[no_expose]
def ord (c : Cardinal) : Ordinal :=
  Quot.liftOn c (fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2) <| by
  rintro α β ⟨f⟩
  refine congr_arg sInf <| ext fun o ↦ ⟨?_, ?_⟩ <;>
    rintro ⟨⟨r, hr⟩, rfl⟩ <;>
    refine ⟨⟨_, RelIso.IsWellOrder.preimage r ?_⟩, type_preimage _ _⟩
  exacts [f.symm, f]

theorem ord_eq_iInf (α : Type u) : ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2 :=
  (rfl)

@[deprecated (since := "2026-03-15")] alias ord_eq_Inf := ord_eq_iInf

/-- There exists a well-order on `α` whose order type is exactly `ord #α`. -/
theorem ord_eq (α) : ∃ (r : α → α → Prop) (wo : IsWellOrder α r), ord #α = @type α r wo :=
  let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩

theorem ord_le_type (r : α → α → Prop) [h : IsWellOrder α r] : ord #α ≤ type r :=
  ciInf_le' _ (Subtype.mk r h)

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card := by
  refine c.inductionOn fun α ↦ o.inductionOn fun β s _ ↦ ?_
  let ⟨r, _, e⟩ := ord_eq α
  constructor <;> intro h
  · rw [e] at h
    exact card_le_card h
  · obtain ⟨f⟩ := h
    have g := RelEmbedding.preimage f s
    have := RelEmbedding.isWellOrder g
    exact (ord_le_type _).trans g.ordinal_type_le

theorem gc_ord_card : GaloisConnection ord card := fun _ _ => ord_le

theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt

@[simp]
theorem card_ord (c) : (ord c).card = c :=
  c.inductionOn fun α ↦ let ⟨r, _, e⟩ := ord_eq α; e ▸ card_type r

theorem card_surjective : Function.Surjective card :=
  fun c ↦ ⟨_, card_ord c⟩

theorem bddAbove_ord_image_iff {s : Set Cardinal} : BddAbove (ord '' s) ↔ BddAbove s :=
  gc_ord_card.bddAbove_l_image

/-- Galois coinsertion between `Cardinal.ord` and `Ordinal.card`. -/
def gciOrdCard : GaloisCoinsertion ord card :=
  gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le

theorem ord_card_le (o : Ordinal) : o.card.ord ≤ o :=
  gc_ord_card.l_u_le _

theorem lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord :=
  lt_ord.2 <| lt_succ _

theorem card_le_iff {o : Ordinal} {c : Cardinal} : o.card ≤ c ↔ o < (succ c).ord := by
  rw [lt_ord, lt_succ_iff]

/--
A variation on `Cardinal.lt_ord` using `≤`: If `o` is no greater than the
initial ordinal of cardinality `c`, then its cardinal is no greater than `c`.

The converse, however, is false (for instance, `o = ω+1` and `c = ℵ₀`).
-/
lemma card_le_of_le_ord {o : Ordinal} {c : Cardinal} (ho : o ≤ c.ord) : o.card ≤ c := by
  rw [← card_ord c]; exact Ordinal.card_le_card ho

@[mono]
theorem ord_strictMono : StrictMono ord :=
  gciOrdCard.strictMono_l

@[mono]
theorem ord_mono : Monotone ord :=
  gc_ord_card.monotone_l

@[simp]
theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
  gciOrdCard.l_le_l_iff

@[simp]
theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
  ord_strictMono.lt_iff_lt

@[simp]
theorem ord_zero : ord 0 = 0 :=
  gc_ord_card.l_bot

@[simp]
theorem ord_nat (n : ℕ) : ord n = n := by
  apply (ord_le.2 (card_nat n).ge).antisymm
  induction n with
  | zero => exact _root_.zero_le _
  | succ n IH => exact (IH.trans_lt <| by simpa using Nat.cast_lt.2 n.lt_succ_self).succ_le

@[simp]
theorem ord_ofNat (n : ℕ) [n.AtLeastTwo] : ord ofNat(n) = OfNat.ofNat n :=
  ord_nat n

@[simp]
theorem ord_one : ord 1 = 1 := by simpa using ord_nat 1

theorem isNormal_ord : Order.IsNormal ord where
  strictMono := ord_strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit := by
    intro a ha
    simp_rw [lowerBounds, upperBounds, mem_setOf, forall_mem_image, ord_le]
    refine fun b H ↦ le_of_forall_lt fun c hc ↦ ?_
    simpa using H (ha.succ_lt hc)

@[simp]
theorem ord_aleph0 : ord.{u} ℵ₀ = ω := by
  refine le_antisymm (ord_le.2 le_rfl) <| le_of_forall_lt fun o h ↦ ?_
  rcases Ordinal.lt_lift_iff.1 h with ⟨o, ho, rfl⟩
  rw [lt_ord, ← lift_card, lift_lt_aleph0, ← typein_enum _ ho]
  exact lt_aleph0_iff_fintype.2 ⟨Set.fintypeLTNat _⟩

@[simp]
theorem lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lift.{u, v} c) := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) ?_
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, _, rfl⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]

theorem mk_ord_toType (c : Cardinal) : #c.ord.ToType = c := by simp

theorem card_typein_lt (r : α → α → Prop) [IsWellOrder α r] (x : α) (h : ord #α = type r) :
    card (typein r x) < #α := by
  rw [← lt_ord, h]
  apply typein_lt_type

theorem card_typein_toType_lt (c : Cardinal) (x : c.ord.ToType) :
    card (typein (α := c.ord.ToType) (· < ·) x) < c := by
  rw [← lt_ord]
  apply typein_lt_self

theorem mk_Iio_ord_toType {c : Cardinal} (i : c.ord.ToType) : #(Iio i) < c :=
  card_typein_toType_lt c i

theorem ord_injective : Injective ord := by
  intro c c' h
  rw [← card_ord c, ← card_ord c', h]

@[simp]
theorem ord_inj {a b : Cardinal} : a.ord = b.ord ↔ a = b :=
  ord_injective.eq_iff

@[simp]
theorem ord_eq_zero {a : Cardinal} : a.ord = 0 ↔ a = 0 :=
  ord_injective.eq_iff' ord_zero

@[simp]
theorem ord_eq_one {a : Cardinal} : a.ord = 1 ↔ a = 1 :=
  ord_injective.eq_iff' ord_one

@[simp]
theorem omega0_le_ord {a : Cardinal} : ω ≤ a.ord ↔ ℵ₀ ≤ a := by
  rw [← ord_aleph0, ord_le_ord]

@[simp]
theorem ord_le_omega0 {a : Cardinal} : a.ord ≤ ω ↔ a ≤ ℵ₀ := by
  rw [← ord_aleph0, ord_le_ord]

@[simp]
theorem ord_lt_omega0 {a : Cardinal} : a.ord < ω ↔ a < ℵ₀ :=
  le_iff_le_iff_lt_iff_lt.1 omega0_le_ord

@[simp]
theorem omega0_lt_ord {a : Cardinal} : ω < a.ord ↔ ℵ₀ < a :=
  le_iff_le_iff_lt_iff_lt.1 ord_le_omega0

@[simp]
theorem ord_eq_omega0 {a : Cardinal} : a.ord = ω ↔ a = ℵ₀ :=
  ord_injective.eq_iff' ord_aleph0

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.ofMonotone Cardinal.ord fun _ _ => Cardinal.ord_lt_ord.2)

@[simp]
theorem ord.orderEmbedding_coe : (ord.orderEmbedding : Cardinal → Ordinal) = ord :=
  rfl

-- intended to be used with explicit universe parameters
/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `Ordinal.{u}`, or `Cardinal.{u}`,
  as an element of `Cardinal.{v}` (when `u < v`). -/
@[pp_with_univ, nolint checkUnivs]
def univ :=
  lift.{v, u + 1} #Ordinal

theorem univ_id : univ.{u, u + 1} = #Ordinal :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [liftPrincipalSeg_coe, lift_ord, lift_succ, ord_le, succ_le_iff] using
    le_of_lt (liftPrincipalSeg.{u, u + 1}.lt_top (succ c).ord)

theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  have := lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
  rw [lift_lift, lift_univ, univ_umax.{u, v}] at this
  exact this

theorem aleph0_lt_univ : ℵ₀ < univ.{u, v} := by
  simpa using lift_lt_univ' ℵ₀

theorem nat_lt_univ (n : ℕ) : n < univ.{u, v} := natCast_lt_aleph0.trans aleph0_lt_univ

theorem univ_pos : 0 < univ.{u, v} :=
  aleph0_pos.trans aleph0_lt_univ

theorem univ_ne_zero : univ.{u, v} ≠ 0 :=
  univ_pos.ne'

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  have := liftPrincipalSeg.mem_range_of_rel_top (by simpa only [liftPrincipalSeg_coe] using h)
  rcases this with ⟨o, h'⟩
  rw [← h', liftPrincipalSeg_coe, ← lift_card]
  apply lift_lt_univ'

theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    obtain ⟨o, e⟩ := liftPrincipalSeg.mem_range_of_rel_top (by simpa only [liftPrincipalSeg_top])
    have := card_ord c
    rw [← e, liftPrincipalSeg_coe, ← lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [← univ_id] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩

theorem IsStrongLimit.univ : IsStrongLimit univ.{u, v} :=
  ⟨univ_ne_zero, fun c h ↦ let ⟨w, h⟩ := lt_univ'.1 h; lt_univ'.2 ⟨2 ^ w, by simp [h]⟩⟩

theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v + 1, _} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

/-- If a cardinal `c` is nonzero, then `c.ord.ToType` has a least element. -/
@[implicit_reducible]
noncomputable def toTypeOrderBot {c : Cardinal} (hc : c ≠ 0) :
    OrderBot c.ord.ToType :=
  Ordinal.toTypeOrderBot (fun h ↦ hc (ord_injective (by simpa using h)))

end Cardinal

namespace Ordinal

@[simp]
theorem card_univ : card univ.{u, v} = Cardinal.univ.{u, v} :=
  rfl

@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o := by
  rw [← Cardinal.ord_le, Cardinal.ord_nat]

@[simp]
theorem one_le_card {o} : 1 ≤ card o ↔ 1 ≤ o := by
  simpa using nat_le_card (n := 1)

@[simp]
theorem ofNat_le_card {o} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) ≤ card o ↔ (OfNat.ofNat n : Ordinal) ≤ o :=
  nat_le_card

@[simp]
theorem aleph0_le_card {o} : ℵ₀ ≤ card o ↔ ω ≤ o := by
  rw [← ord_le, ord_aleph0]

@[simp]
theorem card_lt_aleph0 {o} : card o < ℵ₀ ↔ o < ω :=
  le_iff_le_iff_lt_iff_lt.1 aleph0_le_card

@[simp]
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o := by
  rw [← succ_le_iff, ← succ_le_iff, ← nat_succ, nat_le_card]
  rfl

@[simp]
theorem zero_lt_card {o} : 0 < card o ↔ 0 < o := by
  simpa using nat_lt_card (n := 0)

@[simp]
theorem one_lt_card {o} : 1 < card o ↔ 1 < o := by
  simpa using nat_lt_card (n := 1)

@[simp]
theorem ofNat_lt_card {o} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < card o ↔ (OfNat.ofNat n : Ordinal) < o :=
  nat_lt_card

@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp]
theorem card_lt_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o < ofNat(n) ↔ o < OfNat.ofNat n :=
  card_lt_nat

@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
theorem card_le_one {o} : card o ≤ 1 ↔ o ≤ 1 := by
  simpa using card_le_nat (n := 1)

@[simp]
theorem card_le_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o ≤ ofNat(n) ↔ o ≤ OfNat.ofNat n :=
  card_le_nat

@[simp]
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n := by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp]
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 := by
  simpa using card_eq_nat (n := 0)

@[simp]
theorem card_eq_one {o} : card o = 1 ↔ o = 1 := by
  simpa using card_eq_nat (n := 1)

theorem _root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0 (o : Ordinal) {c : Cardinal} (hc : c < ℵ₀) :
    o ≤ c.ord ↔ o.card ≤ c := by
  rcases lt_aleph0.mp hc with ⟨n, rfl⟩
  simp

theorem mem_range_lift_of_card_le {a : Cardinal.{u}} {b : Ordinal.{max u v}}
    (h : card b ≤ Cardinal.lift.{v, u} a) : b ∈ Set.range lift.{v, u} := by
  rw [card_le_iff, ← lift_succ, ← lift_ord] at h
  exact mem_range_lift_of_le h.le

@[simp]
theorem card_eq_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o = ofNat(n) ↔ o = OfNat.ofNat n :=
  card_eq_nat

variable (r) in
@[simp]
theorem type_fintype [IsWellOrder α r] [Fintype α] :
    type r = Fintype.card α := by rw [← card_eq_nat, card_type, mk_fintype]

theorem type_fin (n : ℕ) : typeLT (Fin n) = n := by simp

variable (r) in
theorem ord_mk_le_type [IsWellOrder α r] (s : Set α) : (#s).ord ≤ type r := by
  grw [← ord_le_type, ord_le_ord, le_mk_iff_exists_set]
  use s

variable (r) in
theorem ord_mk_lt_type [IsWellOrder α r] {s : Set α} (hfin : s.Finite) (h : sᶜ.Nonempty) :
    (#s).ord < type r := by
  grw [← ord_le_type, ord_lt_ord, ← mk_univ (α := α)]
  exact card_lt_card_of_left_finite hfin h.ssubset_univ

variable (r) in
/-- The `#s`-th element of `α` is an upper-bound for the set's mex (minimum excluded value),
ordered by `r`, when `s` is finite. See `card_typein_min_le_mk` for the `Ordinal` version. -/
theorem not_lt_enum_ord_mk_min_compl [IsWellOrder α r] {s : Set α} (hfin : s.Finite)
    (h : sᶜ.Nonempty) :
    ¬r (enum r ⟨#s |>.ord, ord_mk_lt_type r hfin h⟩) (IsWellFounded.wf.min (r := r) sᶜ h) := by
  grw [← typein_le_typein, typein_enum, Cardinal.le_ord_iff_card_le_of_lt_aleph0 _ hfin.lt_aleph0,
    card_typein_min_le_mk]

end Ordinal

/-! ### Sorted lists -/

theorem List.SortedGT.lt_ord_of_lt [LinearOrder α] [WellFoundedLT α] {l m : List α}
    {o : Ordinal} (hl : l.SortedGT) (hm : m.SortedGT) (hmltl : m < l)
    (hlt : ∀ i ∈ l, Ordinal.typein (α := α) (· < ·) i < o) :
      ∀ i ∈ m, Ordinal.typein (α := α) (· < ·) i < o := by
  replace hmltl : List.Lex (· < ·) m l := hmltl
  cases l with
  | nil => simp at hmltl
  | cons a as =>
    cases m with
    | nil => intro i hi; simp at hi
    | cons b bs =>
      intro i hi
      suffices h : i ≤ a by refine lt_of_le_of_lt ?_ (hlt a mem_cons_self); simpa
      cases hi with
      | head as => exact List.head_le_of_lt hmltl
      | tail b hi => exact le_of_lt (lt_of_lt_of_le (List.rel_of_pairwise_cons hm.pairwise hi)
          (List.head_le_of_lt hmltl))

@[deprecated (since := "2025-11-27")] alias List.Sorted.lt_ord_of_lt := List.SortedGT.lt_ord_of_lt
