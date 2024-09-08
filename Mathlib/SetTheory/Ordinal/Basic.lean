/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Sum.Order
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.PPWithUniv

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
  `Ordinal.lift.initialSeg`.
  For a version registering that it is a principal segment embedding if `u < v`, see
  `Ordinal.lift.principalSeg`.
* `Ordinal.omega` or `ω` is the order type of `ℕ`. This definition is universe polymorphic:
  `Ordinal.omega.{u} : Ordinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.

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

## Notations

* `ω` is a notation for the first infinite ordinal in the locale `Ordinal`.
-/

assert_not_exists Module
assert_not_exists Field

noncomputable section

open Function Cardinal Set Equiv Order
open scoped Cardinal InitialSeg

universe u v w

variable {α : Type u} {β : Type*} {γ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

/-! ### Well order on an arbitrary type -/


section WellOrderingThm

-- Porting note: `parameter` does not work
-- parameter {σ : Type u}
variable {σ : Type u}


open Function

theorem nonempty_embedding_to_cardinal : Nonempty (σ ↪ Cardinal.{u}) :=
  (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : σ → Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ sum g)⟩ := invFun_surjective hf (2 ^ sum g)
    have : g x ≤ sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx]; exact cantor _) this

/-- An embedding of any type to the set of cardinals. -/
def embeddingToCardinal : σ ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def WellOrderingRel : σ → σ → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)

instance WellOrderingRel.isWellOrder : IsWellOrder σ WellOrderingRel :=
  (RelEmbedding.preimage _ _).isWellOrder

instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder σ r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

end WellOrderingThm

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
  ⟨⟨PEmpty, _, inferInstanceAs (IsWellOrder PEmpty EmptyRelation)⟩⟩

@[simp]
theorem eta (o : WellOrder) : mk o.α o.r o.wo = o := by
  cases o
  rfl

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
defined through the axiom of choice.

Use this over `Iio o` only when it is paramount to have a `Type u` rather than a `Type (u + 1)`. -/
def Ordinal.toType (o : Ordinal.{u}) : Type u :=
  o.out.α

instance hasWellFounded_toType (o : Ordinal) : WellFoundedRelation o.toType :=
  ⟨o.out.r, o.out.wo.wf⟩

instance linearOrder_toType (o : Ordinal) : LinearOrder o.toType :=
  @IsWellOrder.linearOrder _ o.out.r o.out.wo

instance isWellOrder_toType_lt (o : Ordinal) : IsWellOrder o.toType (· < ·) :=
  o.out.wo

namespace Ordinal

/-! ### Basic properties of the order type -/

/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧

instance zero : Zero Ordinal :=
  ⟨type <| @EmptyRelation PEmpty⟩

instance inhabited : Inhabited Ordinal :=
  ⟨0⟩

instance one : One Ordinal :=
  ⟨type <| @EmptyRelation PUnit⟩

/-- The order type of an element inside a well order. For the embedding as a principal segment, see
`typein.principalSeg`. -/
def typein (r : α → α → Prop) [IsWellOrder α r] (a : α) : Ordinal :=
  type (Subrel r { b | r b a })

@[simp]
theorem type_def' (w : WellOrder) : ⟦w⟧ = type w.r := by
  cases w
  rfl

@[simp]
theorem type_def (r) [wo : IsWellOrder α r] : (⟦⟨α, r, wo⟩⟧ : Ordinal) = type r := by
  rfl

@[simp]
theorem type_lt (o : Ordinal) : type (α := o.toType) (· < ·) = o :=
  (type_def' _).symm.trans <| Quotient.out_eq o

@[deprecated type_lt (since := "2024-08-26")]
theorem type_out (o : Ordinal) : Ordinal.type o.out.r = o :=
  type_lt o

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

theorem type_pEmpty : type (@EmptyRelation PEmpty) = 0 :=
  rfl

theorem type_empty : type (@EmptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _

theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Unique α] : type r = 1 :=
  (RelIso.relIsoOfUniqueOfIrrefl r _).ordinal_type_eq

@[simp]
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    ⟨s.toEquiv.unique⟩,
    fun ⟨h⟩ => @type_eq_one_of_unique α r _ h⟩

theorem type_pUnit : type (@EmptyRelation PUnit) = 1 :=
  rfl

theorem type_unit : type (@EmptyRelation Unit) = 1 :=
  rfl

@[simp]
theorem toType_empty_iff_eq_zero {o : Ordinal} : IsEmpty o.toType ↔ o = 0 := by
  rw [← @type_eq_zero_iff_isEmpty o.toType (· < ·), type_lt]

@[deprecated toType_empty_iff_eq_zero (since := "2024-08-26")]
alias out_empty_iff_eq_zero := toType_empty_iff_eq_zero

@[deprecated toType_empty_iff_eq_zero (since := "2024-08-26")]
theorem eq_zero_of_out_empty (o : Ordinal) [h : IsEmpty o.toType] : o = 0 :=
  toType_empty_iff_eq_zero.1 h

instance isEmpty_toType_zero : IsEmpty (toType 0) :=
  toType_empty_iff_eq_zero.2 rfl

@[simp]
theorem toType_nonempty_iff_ne_zero {o : Ordinal} : Nonempty o.toType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.toType (· < ·), type_lt]

@[deprecated toType_nonempty_iff_ne_zero (since := "2024-08-26")]
alias out_nonempty_iff_ne_zero := toType_nonempty_iff_ne_zero

@[deprecated toType_nonempty_iff_ne_zero (since := "2024-08-26")]
theorem ne_zero_of_out_nonempty (o : Ordinal) [h : Nonempty o.toType] : o ≠ 0 :=
  toType_nonempty_iff_ne_zero.1 h

protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  type_ne_zero_of_nonempty _

instance nontrivial : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, Ordinal.one_ne_zero⟩⟩

@[simp]
theorem type_preimage {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinal_type_eq

@[elab_as_elim]
theorem inductionOn {C : Ordinal → Prop} (o : Ordinal)
    (H : ∀ (α r) [IsWellOrder α r], C (type r)) : C o :=
  Quot.inductionOn o fun ⟨α, r, wo⟩ => @H α r wo

/-! ### The order on ordinals -/

/--
For `Ordinal`:

* less-equal is defined such that well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an *initial* segment of `s`.

* less-than is defined such that well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a *principal* segment of `s`.
-/
instance partialOrder : PartialOrder Ordinal where
  le a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≼i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ =>
      propext
        ⟨fun ⟨h⟩ => ⟨(InitialSeg.ofIso f.symm).trans <| h.trans (InitialSeg.ofIso g)⟩, fun ⟨h⟩ =>
          ⟨(InitialSeg.ofIso f).trans <| h.trans (InitialSeg.ofIso g.symm)⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≺i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ =>
      propext
        ⟨fun ⟨h⟩ => ⟨PrincipalSeg.equivLT f.symm <| h.ltLe (InitialSeg.ofIso g)⟩, fun ⟨h⟩ =>
          ⟨PrincipalSeg.equivLT f <| h.ltLe (InitialSeg.ofIso g.symm)⟩⟩
  le_refl := Quot.ind fun ⟨_, _, _⟩ => ⟨InitialSeg.refl _⟩
  le_trans a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  lt_iff_le_not_le a b :=
    Quotient.inductionOn₂ a b fun _ _ =>
      ⟨fun ⟨f⟩ => ⟨⟨f⟩, fun ⟨g⟩ => (f.ltLe g).irrefl⟩, fun ⟨⟨f⟩, h⟩ =>
        Sum.recOn f.ltOrEq (fun g => ⟨g⟩) fun g => (h ⟨InitialSeg.ofIso g.symm⟩).elim⟩
  le_antisymm a b :=
    Quotient.inductionOn₂ a b fun _ _ ⟨h₁⟩ ⟨h₂⟩ =>
      Quot.sound ⟨InitialSeg.antisymm h₁ h₂⟩

theorem type_le_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl

theorem type_le_iff' {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩

theorem _root_.InitialSeg.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≼i s) : type r ≤ type s :=
  ⟨h⟩

theorem _root_.RelEmbedding.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ↪r s) : type r ≤ type s :=
  ⟨h.collapse⟩

@[simp]
theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl

theorem _root_.PrincipalSeg.ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≺i s) : type r < type s :=
  ⟨h⟩

@[simp]
protected theorem zero_le (o : Ordinal) : 0 ≤ o :=
  inductionOn o fun _ r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le

instance orderBot : OrderBot Ordinal where
  bot := 0
  bot_le := Ordinal.zero_le

@[simp]
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl

@[simp]
protected theorem le_zero {o : Ordinal} : o ≤ 0 ↔ o = 0 :=
  le_bot_iff

protected theorem pos_iff_ne_zero {o : Ordinal} : 0 < o ↔ o ≠ 0 :=
  bot_lt_iff_ne_bot

protected theorem not_lt_zero (o : Ordinal) : ¬o < 0 :=
  not_lt_bot

theorem eq_zero_or_pos : ∀ a : Ordinal, a = 0 ∨ 0 < a :=
  eq_bot_or_bot_lt

instance zeroLEOneClass : ZeroLEOneClass Ordinal :=
  ⟨Ordinal.zero_le _⟩

instance NeZero.one : NeZero (1 : Ordinal) :=
  ⟨Ordinal.one_ne_zero⟩

/-- Given two ordinals `α ≤ β`, then `initialSegToType α β` is the initial segment embedding of
`α.toType` into `β.toType`. -/
def initialSegToType {α β : Ordinal} (h : α ≤ β) :
    @InitialSeg α.toType β.toType (· < ·) (· < ·) := by
  change α.out.r ≼i β.out.r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice

@[deprecated initialSegToType (since := "2024-08-26")]
noncomputable alias initialSegOut := initialSegToType

/-- Given two ordinals `α < β`, then `principalSegToType α β` is the principal segment embedding
of `α.toType` into `β.toType`. -/
def principalSegToType {α β : Ordinal} (h : α < β) :
    @PrincipalSeg α.toType β.toType (· < ·) (· < ·) := by
  change α.out.r ≺i β.out.r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice

@[deprecated principalSegToType (since := "2024-08-26")]
noncomputable alias principalSegOut := principalSegToType

theorem typein_lt_type (r : α → α → Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  ⟨PrincipalSeg.ofElement _ _⟩

theorem typein_lt_self {o : Ordinal} (i : o.toType) : typein (α := o.toType) (· < ·) i < o := by
  simp_rw [← type_lt o]
  apply typein_lt_type

@[simp]
theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≺i s) : typein s f.top = type r :=
  Eq.symm <|
    Quot.sound
      ⟨RelIso.ofSurjective (RelEmbedding.codRestrict _ f f.lt_top) fun ⟨a, h⟩ => by
          rcases f.down.1 h with ⟨b, rfl⟩; exact ⟨b, rfl⟩⟩

@[simp]
theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) : Ordinal.typein s (f a) = Ordinal.typein r a :=
  Eq.symm <|
    Quotient.sound
      ⟨RelIso.ofSurjective
        (RelEmbedding.codRestrict _ ((Subrel.relEmbedding _ _).trans f) fun ⟨x, h⟩ => by
          rw [RelEmbedding.trans_apply]; exact f.toRelEmbedding.map_rel_iff.2 h)
          fun ⟨y, h⟩ => by
            rcases f.init h with ⟨a, rfl⟩
            exact ⟨⟨a, f.toRelEmbedding.map_rel_iff.1 h⟩,
              Subtype.eq <| RelEmbedding.trans_apply _ _ _⟩⟩

@[simp]
theorem typein_lt_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} :
    typein r a < typein r b ↔ r a b :=
  ⟨fun ⟨f⟩ => by
    have : f.top.1 = a := by
      let f' := PrincipalSeg.ofElement r a
      let g' := f.trans (PrincipalSeg.ofElement r b)
      have : g'.top = f'.top := by rw [Subsingleton.elim f' g']
      exact this
    rw [← this]
    exact f.top.2, fun h =>
    ⟨PrincipalSeg.codRestrict _ (PrincipalSeg.ofElement r a) (fun x => @trans _ r _ _ _ _ x.2 h) h⟩⟩

theorem typein_surj (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    ∃ a, typein r a = o :=
  inductionOn o (fun _ _ _ ⟨f⟩ => ⟨f.top, typein_top _⟩) h

theorem typein_injective (r : α → α → Prop) [IsWellOrder α r] : Injective (typein r) :=
  injective_of_increasing r (· < ·) (typein r) (typein_lt_typein r).2

@[simp]
theorem typein_inj (r : α → α → Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff

/-- Principal segment version of the `typein` function, embedding a well order into ordinals as a
principal segment. -/
def typein.principalSeg {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    @PrincipalSeg α Ordinal.{u} r (· < ·) :=
  ⟨⟨⟨typein r, typein_injective r⟩, typein_lt_typein r⟩, type r,
    fun _ ↦ ⟨typein_surj r, fun ⟨a, h⟩ ↦ h ▸ typein_lt_type r a⟩⟩

@[simp]
theorem typein.principalSeg_coe (r : α → α → Prop) [IsWellOrder α r] :
    (typein.principalSeg r : α → Ordinal) = typein r :=
  rfl

/-! ### Enumerating elements in a well-order with ordinals. -/

/-- A well order `r` is order-isomorphic to the set of ordinals smaller than `type r`.
`enum r ⟨o, h⟩` is the `o`-th element of `α` ordered by `r`.

That is, `enum` maps an initial segment of the ordinals, those less than the order type of `r`, to
the elements of `α`. -/
-- The explicit typing is required in order for `simp` to work properly.
@[simps! symm_apply_coe]
def enum (r : α → α → Prop) [IsWellOrder α r] :
    @RelIso (Subtype fun o => o < type r) α (Subrel (· < · ) _) r :=
  (typein.principalSeg r).subrelIso

@[simp]
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r ⟨o, h⟩) = o :=
  (typein.principalSeg r).apply_subrelIso _

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : s ≺i r) {h : type s < type r} : enum r ⟨type s, h⟩ = f.top :=
  (typein.principalSeg r).injective <| (typein_enum _ _).trans (typein_top _).symm

@[simp]
theorem enum_typein (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    enum r ⟨typein r a, typein_lt_type r a⟩ = a :=
  enum_type (PrincipalSeg.ofElement r a)

theorem enum_lt_enum {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : {o // o < type r}} :
    r (enum r o₁) (enum r o₂) ↔ o₁ < o₂ := by
  rw [← typein_lt_typein r, typein_enum, typein_enum, Subtype.coe_lt_coe]

theorem relIso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) :
    ∀ (hr : o < type r) (hs : o < type s), f (enum r ⟨o, hr⟩) = enum s ⟨o, hs⟩ := by
  refine inductionOn o ?_; rintro γ t wo ⟨g⟩ ⟨h⟩
  rw [enum_type g, enum_type (PrincipalSeg.ltEquiv g f)]; rfl

theorem relIso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r ⟨o, hr⟩) = enum s ⟨o, hr.trans_eq (Quotient.sound ⟨f⟩)⟩ :=
  relIso_enum' _ _ _ _

theorem lt_wf : @WellFounded Ordinal (· < ·) :=
  wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ ↦
    RelHomClass.wellFounded (enum _) wo.wf)

instance wellFoundedRelation : WellFoundedRelation Ordinal :=
  ⟨(· < ·), lt_wf⟩

/-- Reformulation of well founded induction on ordinals as a lemma that works with the
`induction` tactic, as in `induction i using Ordinal.induction with | h i IH => ?_`. -/
theorem induction {p : Ordinal.{u} → Prop} (i : Ordinal.{u}) (h : ∀ j, (∀ k, k < j → p k) → p j) :
    p i :=
  lt_wf.induction i h

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

theorem card_le_card {o₁ o₂ : Ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

@[simp]
theorem card_zero : card 0 = 0 := mk_eq_zero _

@[simp]
theorem card_one : card 1 = 1 := mk_eq_one _

/-! ### Lifting ordinals to a higher universe -/

-- Porting note: Needed to add universe hint .{u} below
/-- The universe lift operation for ordinals, which embeds `Ordinal.{u}` as
  a proper initial segment of `Ordinal.{v}` for `v > u`. For the initial segment version,
  see `lift.initialSeg`. -/
@[pp_with_univ]
def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  Quotient.liftOn o (fun w => type <| ULift.down.{u} ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩

@[simp]
theorem type_uLift (r : α → α → Prop) [IsWellOrder α r] :
    type (ULift.down ⁻¹'o r) = lift.{v} (type r) := by
  simp (config := { unfoldPartialApp := true })
  rfl

theorem _root_.RelIso.ordinal_lift_type_eq {α : Type u} {β : Type v} {r : α → α → Prop}
    {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) :
    lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinal_type_eq

-- @[simp]
theorem type_lift_preimage {α : Type u} {β : Type v} (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

@[simp, nolint simpNF]
theorem type_lift_preimage_aux {α : Type u} {β : Type v} (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (@type _ (fun x y => r (f x) (f y))
      (inferInstanceAs (IsWellOrder β (f ⁻¹'o r)))) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

/-- `lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't seem to work. -/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩

/-- `lift.{max v u, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't seem to work. -/
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax

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

@[simp]
theorem lift_lift (a : Ordinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun _ _ _ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans <|
          (RelIso.preimage Equiv.ulift _).trans (RelIso.preimage Equiv.ulift _).symm⟩

theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ Nonempty (r ≼i s) :=
  ⟨fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equiv.ulift r).symm).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s))⟩,
    fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equiv.ulift r)).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s).symm)⟩⟩

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equiv.ulift r).symm.trans <| f.trans (RelIso.preimage Equiv.ulift s)⟩,
      fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩⟩

theorem lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s) := by
  haveI := @RelEmbedding.isWellOrder _ _ (@Equiv.ulift.{max v w} α ⁻¹'o r) r
    (RelIso.preimage Equiv.ulift.{max v w} r) _
  haveI := @RelEmbedding.isWellOrder _ _ (@Equiv.ulift.{max u w} β ⁻¹'o s) s
    (RelIso.preimage Equiv.ulift.{max u w} s) _
  exact ⟨fun ⟨f⟩ =>
    ⟨(f.equivLT (RelIso.preimage Equiv.ulift r).symm).ltLe
        (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s))⟩,
    fun ⟨f⟩ =>
    ⟨(f.equivLT (RelIso.preimage Equiv.ulift r)).ltLe
        (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s).symm)⟩⟩

@[simp]
theorem lift_le {a b : Ordinal} : lift.{u,v} a ≤ lift.{u,v} b ↔ a ≤ b :=
  inductionOn a fun α r _ =>
    inductionOn b fun β s _ => by
      rw [← lift_umax]
      exact lift_type_le.{_,_,u}

@[simp]
theorem lift_inj {a b : Ordinal} : lift.{u,v} a = lift.{u,v} b ↔ a = b := by
  simp only [le_antisymm_iff, lift_le]

@[simp]
theorem lift_lt {a b : Ordinal} : lift.{u,v} a < lift.{u,v} b ↔ a < b := by
  simp only [lt_iff_le_not_le, lift_le]

@[simp]
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _

@[simp]
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _

@[simp]
theorem lift_card (a) : Cardinal.lift.{u,v} (card a)= card (lift.{u,v} a) :=
  inductionOn a fun _ _ _ => rfl

theorem lift_down' {a : Cardinal.{u}} {b : Ordinal.{max u v}}
    (h : card.{max u v} b ≤ Cardinal.lift.{v,u} a) : ∃ a', lift.{v,u} a' = b :=
  let ⟨c, e⟩ := Cardinal.lift_down h
  Cardinal.inductionOn c
    (fun α =>
      inductionOn b fun β s _ e' => by
        rw [card_type, ← Cardinal.lift_id'.{max u v, u} #β, ← Cardinal.lift_umax.{u, v},
          lift_mk_eq.{u, max u v, max u v}] at e'
        cases' e' with f
        have g := RelIso.preimage f s
        haveI := (g : f ⁻¹'o s ↪r s).isWellOrder
        have := lift_type_eq.{u, max u v, max u v}.2 ⟨g⟩
        rw [lift_id, lift_umax.{u, v}] at this
        exact ⟨_, this⟩)
    e

theorem lift_down {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b ≤ lift.{v,u} a) :
    ∃ a', lift.{v,u} a' = b :=
  @lift_down' (card a) _ (by rw [lift_card]; exact card_le_card h)

theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b ≤ lift.{v,u} a ↔ ∃ a', lift.{v,u} a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨_, e, h⟩ => e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b < lift.{v,u} a ↔ ∃ a', lift.{v,u} a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down (le_of_lt h)
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨_, e, h⟩ => e ▸ lift_lt.2 h⟩

/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initialSeg : @InitialSeg Ordinal.{u} Ordinal.{max u v} (· < ·) (· < ·) :=
  ⟨⟨⟨lift.{v}, fun _ _ => lift_inj.1⟩, lift_lt⟩, fun _ _ h => lift_down (le_of_lt h)⟩

@[simp]
theorem lift.initialSeg_coe : (lift.initialSeg.{u,v} : Ordinal → Ordinal) = lift.{v,u} :=
  rfl

/-! ### The first infinite ordinal `omega` -/


/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : Ordinal.{u} :=
  lift <| @type ℕ (· < ·) _

@[inherit_doc]
scoped notation "ω" => Ordinal.omega

/-- Note that the presence of this lemma makes `simp [omega]` form a loop. -/
@[simp]
theorem type_nat_lt : @type ℕ (· < ·) _ = ω :=
  (lift_id _).symm

@[simp]
theorem card_omega : card ω = ℵ₀ :=
  rfl

@[simp]
theorem lift_omega : lift ω = ω :=
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
  ⟨fun o₁ o₂ =>
    Quotient.liftOn₂ o₁ o₂ (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => type (Sum.Lex r s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.sumLexCongr f g⟩⟩

instance addMonoidWithOne : AddMonoidWithOne Ordinal.{u} where
  add := (· + ·)
  zero := 0
  one := 1
  zero_add o :=
    inductionOn o fun α r _ =>
      Eq.symm <| Quotient.sound ⟨⟨(emptySum PEmpty α).symm, Sum.lex_inr_inr⟩⟩
  add_zero o :=
    inductionOn o fun α r _ =>
      Eq.symm <| Quotient.sound ⟨⟨(sumEmpty α PEmpty).symm, Sum.lex_inl_inl⟩⟩
  add_assoc o₁ o₂ o₃ :=
    Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quot.sound
        ⟨⟨sumAssoc _ _ _, by
          intros a b
          rcases a with (⟨a | a⟩ | a) <;> rcases b with (⟨b | b⟩ | b) <;>
            simp only [sumAssoc_apply_inl_inl, sumAssoc_apply_inl_inr, sumAssoc_apply_inr,
              Sum.lex_inl_inl, Sum.lex_inr_inr, Sum.Lex.sep, Sum.lex_inr_inl]⟩⟩
  nsmul := nsmulRec

@[simp]
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  inductionOn o₁ fun _ __ => inductionOn o₂ fun _ _ _ => rfl

@[simp]
theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s :=
  rfl

@[simp]
theorem card_nat (n : ℕ) : card.{u} n = n := by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem card_ofNat (n : ℕ) [n.AtLeastTwo] :
    card.{u} (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  card_nat n

-- Porting note: Rewritten proof of elim, previous version was difficult to debug
instance add_covariantClass_le : CovariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· ≤ ·) where
  elim := fun c a b h => by
    revert h c
    refine inductionOn a (fun α₁ r₁ _ ↦ ?_)
    refine inductionOn b (fun α₂ r₂ _ ↦ ?_)
    rintro c ⟨⟨⟨f, fo⟩, fi⟩⟩
    refine inductionOn c (fun β s _ ↦ ?_)
    refine ⟨⟨⟨(Embedding.refl.{u+1} _).sumMap f, ?_⟩, ?_⟩⟩
    · intros a b
      match a, b with
      | Sum.inl a, Sum.inl b => exact Sum.lex_inl_inl.trans Sum.lex_inl_inl.symm
      | Sum.inl a, Sum.inr b => apply iff_of_true <;> apply Sum.Lex.sep
      | Sum.inr a, Sum.inl b => apply iff_of_false <;> exact Sum.lex_inr_inl
      | Sum.inr a, Sum.inr b => exact Sum.lex_inr_inr.trans <| fo.trans Sum.lex_inr_inr.symm
    · intros a b H
      match a, b, H with
      | _, Sum.inl b, _ => exact ⟨Sum.inl b, rfl⟩
      | Sum.inl a, Sum.inr b, H => exact (Sum.lex_inr_inl H).elim
      | Sum.inr a, Sum.inr b, H =>
        let ⟨w, h⟩ := fi _ _ (Sum.lex_inr_inr.1 H)
        exact ⟨Sum.inr w, congr_arg Sum.inr h⟩

-- Porting note: Rewritten proof of elim, previous version was difficult to debug
instance add_swap_covariantClass_le :
    CovariantClass Ordinal.{u} Ordinal.{u} (swap (· + ·)) (· ≤ ·) where
  elim := fun c a b h => by
    revert h c
    refine inductionOn a (fun α₁ r₁ _ ↦ ?_)
    refine inductionOn b (fun α₂ r₂ _ ↦ ?_)
    rintro c ⟨⟨⟨f, fo⟩, fi⟩⟩
    refine inductionOn c (fun β s _ ↦ ?_)
    exact @RelEmbedding.ordinal_type_le _ _ (Sum.Lex r₁ s) (Sum.Lex r₂ s) _ _
              ⟨f.sumMap (Embedding.refl _), by
                intro a b
                constructor <;> intro H
                · cases' a with a a <;> cases' b with b b <;> cases H <;> constructor <;>
                    [rwa [← fo]; assumption]
                · cases H <;> constructor <;> [rwa [fo]; assumption]⟩

theorem le_add_right (a b : Ordinal) : a ≤ a + b := by
  simpa only [add_zero] using add_le_add_left (Ordinal.zero_le b) a

theorem le_add_left (a b : Ordinal) : a ≤ b + a := by
  simpa only [zero_add] using add_le_add_right (Ordinal.zero_le b) a

instance linearOrder : LinearOrder Ordinal :=
  {inferInstanceAs (PartialOrder Ordinal) with
    le_total := fun a b =>
      match lt_or_eq_of_le (le_add_left b a), lt_or_eq_of_le (le_add_right a b) with
      | Or.inr h, _ => by rw [h]; exact Or.inl (le_add_right _ _)
      | _, Or.inr h => by rw [h]; exact Or.inr (le_add_left _ _)
      | Or.inl h₁, Or.inl h₂ => by
        revert h₁ h₂
        refine inductionOn a ?_
        intro α₁ r₁ _
        refine inductionOn b ?_
        intro α₂ r₂ _ ⟨f⟩ ⟨g⟩
        rw [← typein_top f, ← typein_top g, le_iff_lt_or_eq, le_iff_lt_or_eq,
                 typein_lt_typein, typein_lt_typein]
        rcases trichotomous_of (Sum.Lex r₁ r₂) g.top f.top with (h | h | h) <;>
          [exact Or.inl (Or.inl h); (left; right; rw [h]); exact Or.inr (Or.inl h)]
    decidableLE := Classical.decRel _ }

instance wellFoundedLT : WellFoundedLT Ordinal :=
  ⟨lt_wf⟩

instance isWellOrder : IsWellOrder Ordinal (· < ·) where

instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

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

private theorem succ_le_iff' {a b : Ordinal} : a + 1 ≤ b ↔ a < b :=
  ⟨lt_of_lt_of_le
      (inductionOn a fun α r _ =>
        ⟨⟨⟨⟨fun x => Sum.inl x, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩,
            Sum.inr PUnit.unit, fun b =>
            Sum.recOn b (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => Sum.Lex.sep _ _⟩) fun x =>
              Sum.lex_inr_inr.trans ⟨False.elim, fun ⟨x, H⟩ => Sum.inl_ne_inr H⟩⟩⟩),
    inductionOn a fun α r hr =>
      inductionOn b fun β s hs ⟨⟨f, t, hf⟩⟩ => by
        haveI := hs
        refine ⟨⟨RelEmbedding.ofMonotone (Sum.rec f fun _ => t) (fun a b ↦ ?_), fun a b ↦ ?_⟩⟩
        · rcases a with (a | _) <;> rcases b with (b | _)
          · simpa only [Sum.lex_inl_inl] using f.map_rel_iff.2
          · intro
            rw [hf]
            exact ⟨_, rfl⟩
          · exact False.elim ∘ Sum.lex_inr_inl
          · exact False.elim ∘ Sum.lex_inr_inr.1
        · rcases a with (a | _)
          · intro h
            have := @PrincipalSeg.init _ _ _ _ _ ⟨f, t, hf⟩ _ _ h
            cases' this with w h
            exact ⟨Sum.inl w, h⟩
          · intro h
            cases' (hf b).1 h with w h
            exact ⟨Sum.inl w, h⟩⟩

instance noMaxOrder : NoMaxOrder Ordinal :=
  ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

instance instSuccOrder : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) succ_le_iff'

instance instSuccAddOrder : SuccAddOrder Ordinal := ⟨fun _ => rfl⟩

@[simp]
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl

@[simp]
theorem succ_zero : succ (0 : Ordinal) = 1 :=
  zero_add 1

-- Porting note: Proof used to be rfl
@[simp]
theorem succ_one : succ (1 : Ordinal) = 2 := by congr; simp only [Nat.unaryCast, zero_add]

theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assoc _ _ _).symm

@[deprecated Order.one_le_iff_pos (since := "2024-09-04")]
protected theorem one_le_iff_pos {o : Ordinal} : 1 ≤ o ↔ 0 < o :=
  Order.one_le_iff_pos

theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 := by
  rw [Order.one_le_iff_pos, Ordinal.pos_iff_ne_zero]

theorem succ_pos (o : Ordinal) : 0 < succ o :=
  bot_lt_succ o

theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  ne_of_gt <| succ_pos o

@[simp]
theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 := by
  simpa using @lt_succ_bot_iff _ _ _ a _ _

theorem le_one_iff {a : Ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 := by
  simpa using @le_succ_bot_iff _ _ _ a _

@[simp]
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp only [← add_one_eq_succ, card_add, card_one]

theorem natCast_succ (n : ℕ) : ↑n.succ = succ (n : Ordinal) :=
  rfl

@[deprecated (since := "2024-04-17")]
alias nat_cast_succ := natCast_succ

instance uniqueIioOne : Unique (Iio (1 : Ordinal)) where
  default := ⟨0, by simp⟩
  uniq a := Subtype.ext <| lt_one_iff_zero.1 a.2

instance uniqueToTypeOne : Unique (toType 1) where
  default := enum (α := toType 1) (· < ·) ⟨0, by simp⟩
  uniq a := by
    unfold default
    rw [← enum_typein (α := toType 1) (· < ·) a]
    congr
    rw [← lt_one_iff_zero]
    apply typein_lt_self

theorem one_toType_eq (x : toType 1) : x = enum (· < ·) ⟨0, by simp⟩ :=
  Unique.eq_default x

@[deprecated one_toType_eq (since := "2024-08-26")]
alias one_out_eq := one_toType_eq

/-! ### Extra properties of typein and enum -/

-- TODO: move this section with the other properties of `typein` and `enum`.
-- TODO: use `enumIsoToType` for lemmas on `toType` rather than `enum` and `typein`.

@[simp]
theorem typein_one_toType (x : toType 1) : typein (α := toType 1) (· < ·) x = 0 := by
  rw [one_toType_eq x, typein_enum]

@[deprecated typein_one_toType (since := "2024-08-26")]
alias typein_one_out := typein_one_toType

@[simp]
theorem typein_le_typein (r : α → α → Prop) [IsWellOrder α r] {x y : α} :
    typein r x ≤ typein r y ↔ ¬r y x := by
  rw [← not_lt, typein_lt_typein]

theorem typein_le_typein' (o : Ordinal) {x y : o.toType} :
    typein (α := o.toType) (· < ·) x ≤ typein (α := o.toType) (· < ·) y ↔ x ≤ y := by
  simp

theorem enum_le_enum (r : α → α → Prop) [IsWellOrder α r] {o₁ o₂ : {o // o < type r}} :
    ¬r (enum r o₁) (enum r o₂) ↔ o₂ ≤ o₁ := by
  rw [← @not_lt _ _ o₁ o₂, enum_lt_enum (r := r)]

@[simp]
theorem enum_le_enum' (a : Ordinal) {o₁ o₂ : {o // o < type (· < ·)}} :
    enum (· < ·) o₁ ≤ enum (α := a.toType) (· < ·) o₂ ↔ o₁ ≤ o₂ := by
  rw [← enum_le_enum (α := a.toType) (· < ·), ← not_lt]

theorem enum_zero_le {r : α → α → Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) :
    ¬r a (enum r ⟨0, h0⟩) := by
  rw [← enum_typein r a, enum_le_enum r]
  apply Ordinal.zero_le

theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.toType) :
    enum (α := o.toType) (· < ·) ⟨0, by rwa [type_lt]⟩ ≤ a := by
  rw [← not_lt]
  apply enum_zero_le

theorem le_enum_succ {o : Ordinal} (a : (succ o).toType) :
    a ≤ enum (α := (succ o).toType) (· < ·) ⟨o, (by rw [type_lt]; exact lt_succ o)⟩ := by
  rw [← enum_typein (α := (succ o).toType) (· < ·) a, enum_le_enum', Subtype.mk_le_mk,
    ← lt_succ_iff]
  apply typein_lt_self

theorem enum_inj {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : {o // o < type r}} :
    enum r o₁ = enum r o₂ ↔ o₁ = o₂ := by
  rw [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]

/-- The order isomorphism between ordinals less than `o` and `o.toType`. -/
@[simps!]
noncomputable def enumIsoToType (o : Ordinal) : Set.Iio o ≃o o.toType where
  toFun x :=
    enum (α := o.toType) (· < ·) ⟨x.1, by
      rw [type_lt]
      exact x.2⟩
  invFun x := ⟨typein (α := o.toType) (· < ·) x, typein_lt_self x⟩
  left_inv := fun ⟨o', h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv h := enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    apply enum_le_enum'

@[deprecated (since := "2024-08-26")]
alias enumIsoOut := enumIsoToType

/-- `o.toType` is an `OrderBot` whenever `0 < o`. -/
def toTypeOrderBotOfPos {o : Ordinal} (ho : 0 < o) : OrderBot o.toType where
  bot_le := enum_zero_le' ho

@[deprecated toTypeOrderBotOfPos (since := "2024-08-26")]
noncomputable alias outOrderBotOfPos := toTypeOrderBotOfPos

theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (α := o.toType) (· < ·) ⟨0, by rwa [type_lt]⟩ =
      have H := toTypeOrderBotOfPos ho
      (⊥ : o.toType) :=
  rfl

/-! ### Universal ordinal -/


-- intended to be used with explicit universe parameters
/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `Ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
@[pp_with_univ, nolint checkUnivs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)

theorem univ_id : univ.{u, u + 1} = @type Ordinal (· < ·) _ :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principalSeg : @PrincipalSeg Ordinal.{u} Ordinal.{max (u + 1) v} (· < ·) (· < ·) :=
  ⟨↑lift.initialSeg.{u, max (u + 1) v}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · rw [← lift_id (type s)] at h ⊢
      cases' lift_type_lt.{_,_,v}.1 h with f
      cases' f with f a hf
      exists a
      revert hf
      -- Porting note: apply inductionOn does not work, refine does
      refine inductionOn a ?_
      intro α r _ hf
      refine
        lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
          ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ ?_) ?_).symm⟩
      · exact fun b => enum r ⟨f b, (hf _).2 ⟨_, rfl⟩⟩
      · refine fun a b h => (typein_lt_typein r).1 ?_
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        cases' (hf _).1 (typein_lt_type _ a') with b e
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]
    · cases' h with a e
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein.principalSeg r⟩⟩

@[simp]
theorem lift.principalSeg_coe :
    (lift.principalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

-- Porting note: Added universe hints below
@[simp]
theorem lift.principalSeg_top : (lift.principalSeg.{u,v}).top = univ.{u,v} :=
  rfl

theorem lift.principalSeg_top' : lift.principalSeg.{u, u + 1}.top = @type Ordinal (· < ·) _ := by
  simp only [lift.principalSeg_top, univ_id]

end Ordinal

/-! ### Representing a cardinal with an ordinal -/


namespace Cardinal

open Ordinal

@[simp]
theorem mk_toType (o : Ordinal) : #o.toType = o.card :=
  (Ordinal.card_type _).symm.trans <| by rw [Ordinal.type_lt]

@[deprecated mk_toType (since := "2024-08-26")]
alias mk_ordinal_out := mk_toType

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : Cardinal) : Ordinal :=
  let F := fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2
  Quot.liftOn c F
    (by
      suffices ∀ {α β}, α ≈ β → F α ≤ F β from
        fun α β h => (this h).antisymm (this (Setoid.symm h))
      rintro α β ⟨f⟩
      refine le_ciInf_iff'.2 fun i => ?_
      haveI := @RelEmbedding.isWellOrder _ _ (f ⁻¹'o i.1) _ (↑(RelIso.preimage f i.1)) i.2
      exact
        (ciInf_le' _
              (Subtype.mk (f ⁻¹'o i.val)
                (@RelEmbedding.isWellOrder _ _ _ _ (↑(RelIso.preimage f i.1)) i.2))).trans_eq
          (Quot.sound ⟨RelIso.preimage f i.1⟩))

theorem ord_eq_Inf (α : Type u) : ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2 :=
  rfl

theorem ord_eq (α) : ∃ (r : α → α → Prop) (wo : IsWellOrder α r), ord #α = @type α r wo :=
  let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩

theorem ord_le_type (r : α → α → Prop) [h : IsWellOrder α r] : ord #α ≤ type r :=
  ciInf_le' _ (Subtype.mk r h)

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
  inductionOn c fun α =>
    Ordinal.inductionOn o fun β s _ => by
      let ⟨r, _, e⟩ := ord_eq α
      simp only [card_type]; constructor <;> intro h
      · rw [e] at h
        exact
          let ⟨f⟩ := h
          ⟨f.toEmbedding⟩
      · cases' h with f
        have g := RelEmbedding.preimage f s
        haveI := RelEmbedding.isWellOrder g
        exact le_trans (ord_le_type _) g.ordinal_type_le

theorem gc_ord_card : GaloisConnection ord card := fun _ _ => ord_le

theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt

@[simp]
theorem card_ord (c) : (ord c).card = c :=
  Quotient.inductionOn c fun α => by
    let ⟨r, _, e⟩ := ord_eq α
    -- Porting note: cardinal.mk_def is now Cardinal.mk'_def, not sure why
    simp only [mk'_def, e, card_type]

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
lemma card_le_of_le_ord {o : Ordinal} {c : Cardinal} (ho : o ≤ c.ord) :
    o.card ≤ c := by
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
theorem ord_nat (n : ℕ) : ord n = n :=
  (ord_le.2 (card_nat n).ge).antisymm
    (by
      induction' n with n IH
      · apply Ordinal.zero_le
      · exact succ_le_of_lt (IH.trans_lt <| ord_lt_ord.2 <| natCast_lt.2 (Nat.lt_succ_self n)))

@[simp]
theorem ord_one : ord 1 = 1 := by simpa using ord_nat 1

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ord_ofNat (n : ℕ) [n.AtLeastTwo] : ord (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  ord_nat n

@[simp]
theorem lift_ord (c) : Ordinal.lift.{u,v} (ord c) = ord (lift.{u,v} c) := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) ?_
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, rfl, _⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]

theorem mk_ord_toType (c : Cardinal) : #c.ord.toType = c := by simp

@[deprecated mk_ord_toType (since := "2024-08-26")]
alias mk_ord_out := mk_ord_toType

theorem card_typein_lt (r : α → α → Prop) [IsWellOrder α r] (x : α) (h : ord #α = type r) :
    card (typein r x) < #α := by
  rw [← lt_ord, h]
  apply typein_lt_type

theorem card_typein_toType_lt (c : Cardinal) (x : c.ord.toType) :
    card (typein (α := c.ord.toType) (· < ·) x) < c := by
  rw [← lt_ord]
  apply typein_lt_self

@[deprecated card_typein_toType_lt (since := "2024-08-26")]
alias card_typein_out_lt := card_typein_toType_lt

theorem mk_Iio_ord_toType {c : Cardinal} (i : c.ord.toType) : #(Iio i) < c :=
  card_typein_toType_lt c i

@[deprecated (since := "2024-08-26")]
alias mk_Iio_ord_out_α := mk_Iio_ord_toType

theorem ord_injective : Injective ord := by
  intro c c' h
  rw [← card_ord c, ← card_ord c', h]

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
  simpa only [lift.principalSeg_coe, lift_ord, lift_succ, ord_le, succ_le_iff] using
    le_of_lt (lift.principalSeg.{u, u + 1}.lt_top (succ c).ord)

theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  have := lift_lt.{_, max (u+1) v}.2 (lift_lt_univ c)
  rw [lift_lift, lift_univ, univ_umax.{u,v}] at this
  exact this

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  have := lift.principalSeg.{u, v}.down.1 (by simpa only [lift.principalSeg_coe] using h)
  rcases this with ⟨o, h'⟩
  rw [← h', lift.principalSeg_coe, ← lift_card]
  apply lift_lt_univ'

theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    cases' lift.principalSeg.{u, u + 1}.down.1 (by simpa only [lift.principalSeg_top] ) with o e
    have := card_ord c
    rw [← e, lift.principalSeg_coe, ← lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, e, h'⟩ := lt_lift_iff.1 h
    rw [← univ_id] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ' _⟩

theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v+1,_} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

end Cardinal

namespace Ordinal

@[simp]
theorem card_univ : card univ.{u,v} = Cardinal.univ.{u,v} :=
  rfl

@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o := by
  rw [← Cardinal.ord_le, Cardinal.ord_nat]

@[simp]
theorem one_le_card {o} : 1 ≤ card o ↔ 1 ≤ o := by
  simpa using nat_le_card (n := 1)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_le_card {o} {n : ℕ} [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Cardinal)) ≤ card o ↔ (OfNat.ofNat n : Ordinal) ≤ o :=
  nat_le_card

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

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_lt_card {o} {n : ℕ} [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Cardinal)) < card o ↔ (OfNat.ofNat n : Ordinal) < o :=
  nat_lt_card

@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem card_lt_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o < (no_index (OfNat.ofNat n)) ↔ o < OfNat.ofNat n :=
  card_lt_nat

@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
theorem card_le_one {o} : card o ≤ 1 ↔ o ≤ 1 := by
  simpa using card_le_nat (n := 1)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem card_le_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o ≤ (no_index (OfNat.ofNat n)) ↔ o ≤ OfNat.ofNat n :=
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

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem card_eq_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o = (no_index (OfNat.ofNat n)) ↔ o = OfNat.ofNat n :=
  card_eq_nat

@[simp]
theorem type_fintype (r : α → α → Prop) [IsWellOrder α r] [Fintype α] :
    type r = Fintype.card α := by rw [← card_eq_nat, card_type, mk_fintype]

theorem type_fin (n : ℕ) : @type (Fin n) (· < ·) _ = n := by simp

end Ordinal

/-! ### Sorted lists -/

theorem List.Sorted.lt_ord_of_lt [LinearOrder α] [IsWellOrder α (· < ·)] {l m : List α}
    {o : Ordinal} (hl : l.Sorted (· > ·)) (hm : m.Sorted (· > ·)) (hmltl : m < l)
    (hlt : ∀ i ∈ l, Ordinal.typein (· < ·) i < o) : ∀ i ∈ m, Ordinal.typein (· < ·) i < o := by
  replace hmltl : List.Lex (· < ·) m l := hmltl
  cases l with
  | nil => simp at hmltl
  | cons a as =>
    cases m with
    | nil => intro i hi; simp at hi
    | cons b bs =>
      intro i hi
      suffices h : i ≤ a by refine lt_of_le_of_lt ?_ (hlt a (mem_cons_self a as)); simpa
      cases hi with
      | head as => exact List.head_le_of_lt hmltl
      | tail b hi => exact le_of_lt (lt_of_lt_of_le (List.rel_of_sorted_cons hm _ hi)
          (List.head_le_of_lt hmltl))
