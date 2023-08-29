/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Data.Sum.Order
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.PPWithUniv

#align_import set_theory.ordinal.basic from "leanprover-community/mathlib"@"8ea5598db6caeddde6cb734aa179cc2408dbd345"

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
* `enum r o h`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
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
  every element of `o₁` is smaller than every element of `o₂`. The main properties of addition
  (and the other operations on ordinals) are stated and proved in `OrdinalArithmetic.lean`. Here,
  we only introduce it and prove its basic properties to deduce the fact that the order on ordinals
  is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `Cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notations

* `ω` is a notation for the first infinite ordinal in the locale `Ordinal`.
-/


noncomputable section

open Function Cardinal Set Equiv Order

open Classical Cardinal InitialSeg

universe u v w

variable {α : Type _} {β : Type*} {γ : Type*} {r : α → α → Prop} {s : β → β → Prop}
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
                     -- ⊢ 2 ^ sum g > sum g
                              -- 🎉 no goals
#align nonempty_embedding_to_cardinal nonempty_embedding_to_cardinal

/-- An embedding of any type to the set of cardinals. -/
def embeddingToCardinal : σ ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal
#align embedding_to_cardinal embeddingToCardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def WellOrderingRel : σ → σ → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)
#align well_ordering_rel WellOrderingRel

instance WellOrderingRel.isWellOrder : IsWellOrder σ WellOrderingRel :=
  (RelEmbedding.preimage _ _).isWellOrder
#align well_ordering_rel.is_well_order WellOrderingRel.isWellOrder

instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder σ r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩
#align is_well_order.subtype_nonempty IsWellOrder.subtype_nonempty

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
set_option linter.uppercaseLean3 false in
#align Well_order WellOrder

attribute [instance] WellOrder.wo

namespace WellOrder

instance inhabited : Inhabited WellOrder :=
  ⟨⟨PEmpty, _, inferInstanceAs (IsWellOrder PEmpty EmptyRelation)⟩⟩

@[simp]
theorem eta (o : WellOrder) : mk o.α o.r o.wo = o := by
  cases o
  -- ⊢ { α := { α := α✝, r := r✝, wo := wo✝ }.α, r := { α := α✝, r := r✝, wo := wo✝ …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Well_order.eta WellOrder.eta

end WellOrder

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance Ordinal.isEquivalent : Setoid WellOrder
    where
  r := fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩
#align ordinal.is_equivalent Ordinal.isEquivalent

/-- `Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
def Ordinal : Type (u + 1) :=
  Quotient Ordinal.isEquivalent
#align ordinal Ordinal

instance hasWellFoundedOut (o : Ordinal) : WellFoundedRelation o.out.α :=
  ⟨o.out.r, o.out.wo.wf⟩
#align has_well_founded_out hasWellFoundedOut

instance linearOrderOut (o : Ordinal) : LinearOrder o.out.α :=
  IsWellOrder.linearOrder o.out.r
#align linear_order_out linearOrderOut

instance isWellOrder_out_lt (o : Ordinal) : IsWellOrder o.out.α (· < ·) :=
  o.out.wo
#align is_well_order_out_lt isWellOrder_out_lt

namespace Ordinal

-- ### Basic properties of the order type
/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧
#align ordinal.type Ordinal.type

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
#align ordinal.typein Ordinal.typein

@[simp]
theorem type_def' (w : WellOrder) : ⟦w⟧ = type w.r := by
  cases w
  -- ⊢ Quotient.mk isEquivalent { α := α✝, r := r✝, wo := wo✝ } = type { α := α✝, r …
  rfl
  -- 🎉 no goals
#align ordinal.type_def' Ordinal.type_def'

@[simp, nolint simpNF] -- Porting note: dsimp can not prove this
theorem type_def (r) [wo : IsWellOrder α r] : (⟦⟨α, r, wo⟩⟧ : Ordinal) = type r := by
  rfl
  -- 🎉 no goals
#align ordinal.type_def Ordinal.type_def

@[simp]
theorem type_out (o : Ordinal) : Ordinal.type o.out.r = o := by
  rw [Ordinal.type, WellOrder.eta, Quotient.out_eq]
  -- 🎉 no goals
#align ordinal.type_out Ordinal.type_out

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'
#align ordinal.type_eq Ordinal.type_eq

theorem _root_.RelIso.ordinal_type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩
#align rel_iso.ordinal_type_eq RelIso.ordinal_type_eq

@[simp]
theorem type_lt (o : Ordinal) : type ((· < ·) : o.out.α → o.out.α → Prop) = o :=
  (type_def' _).symm.trans <| Quotient.out_eq o
#align ordinal.type_lt Ordinal.type_lt

theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinal_type_eq
#align ordinal.type_eq_zero_of_empty Ordinal.type_eq_zero_of_empty

@[simp]
theorem type_eq_zero_iff_isEmpty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero_of_empty α r _⟩
#align ordinal.type_eq_zero_iff_is_empty Ordinal.type_eq_zero_iff_isEmpty

theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α := by simp
                                                                                    -- 🎉 no goals
#align ordinal.type_ne_zero_iff_nonempty Ordinal.type_ne_zero_iff_nonempty

theorem type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h
#align ordinal.type_ne_zero_of_nonempty Ordinal.type_ne_zero_of_nonempty

theorem type_pEmpty : type (@EmptyRelation PEmpty) = 0 :=
  rfl
#align ordinal.type_pempty Ordinal.type_pEmpty

theorem type_empty : type (@EmptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _
#align ordinal.type_empty Ordinal.type_empty

theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Unique α] : type r = 1 :=
  (RelIso.relIsoOfUniqueOfIrrefl r _).ordinal_type_eq
#align ordinal.type_eq_one_of_unique Ordinal.type_eq_one_of_unique

@[simp]
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    ⟨s.toEquiv.unique⟩,
    fun ⟨h⟩ => @type_eq_one_of_unique α r _ h⟩
#align ordinal.type_eq_one_iff_unique Ordinal.type_eq_one_iff_unique

theorem type_pUnit : type (@EmptyRelation PUnit) = 1 :=
  rfl
#align ordinal.type_punit Ordinal.type_pUnit

theorem type_unit : type (@EmptyRelation Unit) = 1 :=
  rfl
#align ordinal.type_unit Ordinal.type_unit

@[simp]
theorem out_empty_iff_eq_zero {o : Ordinal} : IsEmpty o.out.α ↔ o = 0 := by
  rw [← @type_eq_zero_iff_isEmpty o.out.α (· < ·), type_lt]
  -- 🎉 no goals
#align ordinal.out_empty_iff_eq_zero Ordinal.out_empty_iff_eq_zero

theorem eq_zero_of_out_empty (o : Ordinal) [h : IsEmpty o.out.α] : o = 0 :=
  out_empty_iff_eq_zero.1 h
#align ordinal.eq_zero_of_out_empty Ordinal.eq_zero_of_out_empty

instance isEmpty_out_zero : IsEmpty (0 : Ordinal).out.α :=
  out_empty_iff_eq_zero.2 rfl
#align ordinal.is_empty_out_zero Ordinal.isEmpty_out_zero

@[simp]
theorem out_nonempty_iff_ne_zero {o : Ordinal} : Nonempty o.out.α ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.out.α (· < ·), type_lt]
  -- 🎉 no goals
#align ordinal.out_nonempty_iff_ne_zero Ordinal.out_nonempty_iff_ne_zero

theorem ne_zero_of_out_nonempty (o : Ordinal) [h : Nonempty o.out.α] : o ≠ 0 :=
  out_nonempty_iff_ne_zero.1 h
#align ordinal.ne_zero_of_out_nonempty Ordinal.ne_zero_of_out_nonempty

protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  type_ne_zero_of_nonempty _
#align ordinal.one_ne_zero Ordinal.one_ne_zero

instance nontrivial : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, Ordinal.one_ne_zero⟩⟩

--@[simp] -- Porting note: not in simp nf, added aux lemma below
theorem type_preimage {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinal_type_eq
#align ordinal.type_preimage Ordinal.type_preimage

@[simp]
theorem type_preimage_aux {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    @type _ (fun x y => r (f x) (f y)) (inferInstanceAs (IsWellOrder β (↑f ⁻¹'o r))) = type r := by
    convert (RelIso.preimage f r).ordinal_type_eq
    -- 🎉 no goals

@[elab_as_elim]
theorem inductionOn {C : Ordinal → Prop} (o : Ordinal)
    (H : ∀ (α r) [IsWellOrder α r], C (type r)) : C o :=
  Quot.inductionOn o fun ⟨α, r, wo⟩ => @H α r wo
#align ordinal.induction_on Ordinal.inductionOn

/-! ### The order on ordinals -/


instance partialOrder : PartialOrder Ordinal
    where
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

-- Porting note: How can we add a doc to this?
-- /-- Ordinal less-equal is defined such that
--   well orders `r` and `s` satisfy `type r ≤ type s` if there exists
--   a function embedding `r` as an initial segment of `s`. -/
-- add_decl_doc Ordinal.partial_order.le

-- /-- Ordinal less-than is defined such that
--   well orders `r` and `s` satisfy `type r < type s` if there exists
--   a function embedding `r` as a principal segment of `s`. -/
-- add_decl_doc ordinal.partial_order.lt

theorem type_le_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl
#align ordinal.type_le_iff Ordinal.type_le_iff

theorem type_le_iff' {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩
#align ordinal.type_le_iff' Ordinal.type_le_iff'

theorem _root_.InitialSeg.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≼i s) : type r ≤ type s :=
  ⟨h⟩
#align initial_seg.ordinal_type_le InitialSeg.ordinal_type_le

theorem _root_.RelEmbedding.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ↪r s) : type r ≤ type s :=
  ⟨h.collapse⟩
#align rel_embedding.ordinal_type_le RelEmbedding.ordinal_type_le

@[simp]
theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl
#align ordinal.type_lt_iff Ordinal.type_lt_iff

theorem _root_.PrincipalSeg.ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
  [IsWellOrder α r] [IsWellOrder β s] (h : r ≺i s) : type r < type s :=
  ⟨h⟩
#align principal_seg.ordinal_type_lt PrincipalSeg.ordinal_type_lt

protected theorem zero_le (o : Ordinal) : 0 ≤ o :=
  inductionOn o fun _ r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le
#align ordinal.zero_le Ordinal.zero_le

instance orderBot : OrderBot Ordinal where
  bot := 0
  bot_le := Ordinal.zero_le

@[simp]
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl
#align ordinal.bot_eq_zero Ordinal.bot_eq_zero

@[simp]
protected theorem le_zero {o : Ordinal} : o ≤ 0 ↔ o = 0 :=
  le_bot_iff
#align ordinal.le_zero Ordinal.le_zero

protected theorem pos_iff_ne_zero {o : Ordinal} : 0 < o ↔ o ≠ 0 :=
  bot_lt_iff_ne_bot
#align ordinal.pos_iff_ne_zero Ordinal.pos_iff_ne_zero

protected theorem not_lt_zero (o : Ordinal) : ¬o < 0 :=
  not_lt_bot
#align ordinal.not_lt_zero Ordinal.not_lt_zero

theorem eq_zero_or_pos : ∀ a : Ordinal, a = 0 ∨ 0 < a :=
  eq_bot_or_bot_lt
#align ordinal.eq_zero_or_pos Ordinal.eq_zero_or_pos

instance zeroLEOneClass : ZeroLEOneClass Ordinal :=
  ⟨Ordinal.zero_le _⟩

instance NeZero.one : NeZero (1 : Ordinal) :=
  ⟨Ordinal.one_ne_zero⟩
#align ordinal.ne_zero.one Ordinal.NeZero.one

/-- Given two ordinals `α ≤ β`, then `initialSegOut α β` is the initial segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def initialSegOut {α β : Ordinal} (h : α ≤ β) :
    InitialSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) := by
  change α.out.r ≼i β.out.r
  -- ⊢ (Quotient.out α).r ≼i (Quotient.out β).r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  -- ⊢ (Quotient.out α).r ≼i (Quotient.out β).r
                                                      -- ⊢ Quotient.mk isEquivalent (Quotient.out α) ≤ Quotient.mk isEquivalent (Quotie …
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice
  -- ⊢ Quotient.mk isEquivalent { α := α✝, r := r✝, wo := wo✝ } ≤ Quotient.mk isEqu …
                        -- ⊢ Quotient.mk isEquivalent { α := α✝¹, r := r✝¹, wo := wo✝¹ } ≤ Quotient.mk is …
                                              -- 🎉 no goals
#align ordinal.initial_seg_out Ordinal.initialSegOut

/-- Given two ordinals `α < β`, then `principalSegOut α β` is the principal segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def principalSegOut {α β : Ordinal} (h : α < β) :
    PrincipalSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) := by
  change α.out.r ≺i β.out.r
  -- ⊢ (Quotient.out α).r ≺i (Quotient.out β).r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  -- ⊢ (Quotient.out α).r ≺i (Quotient.out β).r
                                                      -- ⊢ Quotient.mk isEquivalent (Quotient.out α) < Quotient.mk isEquivalent (Quotie …
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice
  -- ⊢ Quotient.mk isEquivalent { α := α✝, r := r✝, wo := wo✝ } < Quotient.mk isEqu …
                        -- ⊢ Quotient.mk isEquivalent { α := α✝¹, r := r✝¹, wo := wo✝¹ } < Quotient.mk is …
                                              -- 🎉 no goals
#align ordinal.principal_seg_out Ordinal.principalSegOut

theorem typein_lt_type (r : α → α → Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  ⟨PrincipalSeg.ofElement _ _⟩
#align ordinal.typein_lt_type Ordinal.typein_lt_type

theorem typein_lt_self {o : Ordinal} (i : o.out.α) :
    @typein _ (· < ·) (isWellOrder_out_lt _) i < o := by
  simp_rw [← type_lt o]
  -- ⊢ typein (fun x x_1 => x < x_1) i < type fun x x_1 => x < x_1
  apply typein_lt_type
  -- 🎉 no goals
#align ordinal.typein_lt_self Ordinal.typein_lt_self

@[simp]
theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≺i s) : typein s f.top = type r :=
  Eq.symm <|
    Quot.sound
      ⟨RelIso.ofSurjective (RelEmbedding.codRestrict _ f f.lt_top) fun ⟨a, h⟩ => by
          rcases f.down.1 h with ⟨b, rfl⟩; exact ⟨b, rfl⟩⟩
          -- ⊢ ∃ a, ↑(RelEmbedding.codRestrict {b | s b f.top} { toRelEmbedding := f.toRelE …
                                           -- 🎉 no goals
#align ordinal.typein_top Ordinal.typein_top

@[simp]
theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) : Ordinal.typein s (f a) = Ordinal.typein r a :=
  Eq.symm <|
    Quotient.sound
      ⟨RelIso.ofSurjective
        (RelEmbedding.codRestrict _ ((Subrel.relEmbedding _ _).trans f) fun ⟨x, h⟩ => by
          rw [RelEmbedding.trans_apply]; exact f.toRelEmbedding.map_rel_iff.2 h)
          -- ⊢ ↑f.toRelEmbedding (↑(Subrel.relEmbedding r {b | r b a}) { val := x, property …
                                         -- 🎉 no goals
          fun ⟨y, h⟩ => by
            rcases f.init h with ⟨a, rfl⟩
            -- ⊢ ∃ a_1, ↑(RelEmbedding.codRestrict {b | s b (↑f a✝)} (RelEmbedding.trans (Sub …
            exact ⟨⟨a, f.toRelEmbedding.map_rel_iff.1 h⟩,
              Subtype.eq <| RelEmbedding.trans_apply _ _ _⟩⟩
#align ordinal.typein_apply Ordinal.typein_apply

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
    -- ⊢ r (↑f.top) b
    exact f.top.2, fun h =>
    -- 🎉 no goals
    ⟨PrincipalSeg.codRestrict _ (PrincipalSeg.ofElement r a) (fun x => @trans _ r _ _ _ _ x.2 h) h⟩⟩
#align ordinal.typein_lt_typein Ordinal.typein_lt_typein

theorem typein_surj (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    ∃ a, typein r a = o :=
  inductionOn o (fun _ _ _ ⟨f⟩ => ⟨f.top, typein_top _⟩) h
#align ordinal.typein_surj Ordinal.typein_surj

theorem typein_injective (r : α → α → Prop) [IsWellOrder α r] : Injective (typein r) :=
  injective_of_increasing r (· < ·) (typein r) (typein_lt_typein r).2
#align ordinal.typein_injective Ordinal.typein_injective

@[simp]
theorem typein_inj (r : α → α → Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff
#align ordinal.typein_inj Ordinal.typein_inj

/-- Principal segment version of the `typein` function, embedding a well order into
  ordinals as a principal segment. -/
def typein.principalSeg {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    @PrincipalSeg α Ordinal.{u} r (· < ·) :=
  ⟨⟨⟨typein r, typein_injective r⟩, typein_lt_typein r⟩, type r,
    fun _ ↦ ⟨typein_surj r, fun ⟨a, h⟩ ↦ h ▸ typein_lt_type r a⟩⟩
#align ordinal.typein.principal_seg Ordinal.typein.principalSeg

@[simp]
theorem typein.principalSeg_coe (r : α → α → Prop) [IsWellOrder α r] :
    (typein.principalSeg r : α → Ordinal) = typein r :=
  rfl
#align ordinal.typein.principal_seg_coe Ordinal.typein.principalSeg_coe

/-! ### Enumerating elements in a well-order with ordinals. -/


/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum (r : α → α → Prop) [IsWellOrder α r] (o) (h : o < type r) : α :=
  (typein.principalSeg r).subrelIso ⟨o, h⟩

@[simp]
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r o h) = o :=
  (typein.principalSeg r).apply_subrelIso _
#align ordinal.typein_enum Ordinal.typein_enum

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : s ≺i r) {h : type s < type r} : enum r (type s) h = f.top :=
  (typein.principalSeg r).injective <| (typein_enum _ _).trans (typein_top _).symm
#align ordinal.enum_type Ordinal.enum_type

@[simp]
theorem enum_typein (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    enum r (typein r a) (typein_lt_type r a) = a :=
  enum_type (PrincipalSeg.ofElement r a)
#align ordinal.enum_typein Ordinal.enum_typein

theorem enum_lt_enum {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Ordinal} (h₁ : o₁ < type r)
    (h₂ : o₂ < type r) : r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ := by
  rw [← typein_lt_typein r, typein_enum, typein_enum]
  -- 🎉 no goals
#align ordinal.enum_lt_enum Ordinal.enum_lt_enum

theorem relIso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) :
    ∀ (hr : o < type r) (hs : o < type s), f (enum r o hr) = enum s o hs := by
  refine' inductionOn o _; rintro γ t wo ⟨g⟩ ⟨h⟩
  -- ⊢ ∀ (α_1 : Type u) (r_1 : α_1 → α_1 → Prop) [inst : IsWellOrder α_1 r_1] (hr : …
                           -- ⊢ ↑f (enum r (type t) (_ : Nonempty (t ≺i r))) = enum s (type t) (_ : Nonempty …
  skip; rw [enum_type g, enum_type (PrincipalSeg.ltEquiv g f)]; rfl
  -- ⊢ ↑f (enum r (type t) (_ : Nonempty (t ≺i r))) = enum s (type t) (_ : Nonempty …
        -- ⊢ ↑f g.top = (PrincipalSeg.ltEquiv g f).top
                                                                -- 🎉 no goals
#align ordinal.rel_iso_enum' Ordinal.relIso_enum'

theorem relIso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r o hr) =
      enum s o
        (by
          convert hr using 1
          -- ⊢ type s = type r
          apply Quotient.sound
          -- ⊢ { α := β, r := s, wo := inst✝ } ≈ { α := α, r := r, wo := inst✝¹ }
          exact ⟨f.symm⟩) :=
          -- 🎉 no goals
  relIso_enum' _ _ _ _
#align ordinal.rel_iso_enum Ordinal.relIso_enum

theorem lt_wf : @WellFounded Ordinal (· < ·) :=
/-
  wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, r, wo⟩ ↦
    RelHomClass.wellFounded (typein.principalSeg r).subrelIso wo.wf)
-/
  ⟨fun a =>
    inductionOn a fun α r wo =>
      suffices ∀ a, Acc (· < ·) (typein r a) from
        ⟨_, fun o h =>
          let ⟨a, e⟩ := typein_surj r h
          e ▸ this a⟩
      fun a =>
      Acc.recOn (wo.wf.apply a) fun x _ IH =>
        ⟨_, fun o h => by
          rcases typein_surj r (lt_trans h (typein_lt_type r _)) with ⟨b, rfl⟩
          -- ⊢ Acc (fun x x_1 => x < x_1) (typein r b)
          exact IH _ ((typein_lt_typein r).1 h)⟩⟩
          -- 🎉 no goals
#align ordinal.lt_wf Ordinal.lt_wf

instance wellFoundedRelation : WellFoundedRelation Ordinal :=
  ⟨(· < ·), lt_wf⟩

/-- Reformulation of well founded induction on ordinals as a lemma that works with the
`induction` tactic, as in `induction i using Ordinal.induction with i IH`. -/
theorem induction {p : Ordinal.{u} → Prop} (i : Ordinal.{u}) (h : ∀ j, (∀ k, k < j → p k) → p j) :
    p i :=
  lt_wf.induction i h
#align ordinal.induction Ordinal.induction

/-! ### Cardinality of ordinals -/


/-- The cardinal of an ordinal is the cardinality of any type on which a relation with that order
type is defined. -/
def card : Ordinal → Cardinal :=
  Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩
#align ordinal.card Ordinal.card

@[simp]
theorem card_type (r : α → α → Prop) [IsWellOrder α r] : card (type r) = #α :=
  rfl
#align ordinal.card_type Ordinal.card_type

-- Porting note: nolint, simpNF linter falsely claims the lemma never applies
@[simp, nolint simpNF]
theorem card_typein {r : α → α → Prop} [IsWellOrder α r] (x : α) :
    #{ y // r y x } = (typein r x).card :=
  rfl
#align ordinal.card_typein Ordinal.card_typein

theorem card_le_card {o₁ o₂ : Ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩
#align ordinal.card_le_card Ordinal.card_le_card

@[simp]
theorem card_zero : card 0 = 0 := mk_eq_zero _
#align ordinal.card_zero Ordinal.card_zero

@[simp]
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
  ⟨inductionOn o fun α r _ h => by
      haveI := Cardinal.mk_eq_zero_iff.1 h
      -- ⊢ type r = 0
      apply type_eq_zero_of_empty,
      -- 🎉 no goals
    fun e => by simp only [e, card_zero]⟩
                -- 🎉 no goals
#align ordinal.card_eq_zero Ordinal.card_eq_zero

@[simp]
theorem card_one : card 1 = 1 := mk_eq_one _
#align ordinal.card_one Ordinal.card_one

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
#align ordinal.lift Ordinal.lift

-- Porting note: Needed to add universe hints ULift.down.{v,u} below
-- @[simp] -- Porting note: Not in simpnf, added aux lemma below
theorem type_uLift (r : α → α → Prop) [IsWellOrder α r] :
    type (ULift.down.{v,u} ⁻¹'o r) = lift.{v} (type r) := by
  simp
  -- ⊢ (type fun x y => r x.down y.down) = lift.{v, u} (type r)
  rfl
  -- 🎉 no goals
#align ordinal.type_ulift Ordinal.type_uLift

-- Porting note: simpNF linter falsely claims that this never applies
@[simp, nolint simpNF]
theorem type_uLift_aux (r : α → α → Prop) [IsWellOrder α r] :
    @type.{max v u} _ (fun x y => r (ULift.down.{v,u} x) (ULift.down.{v,u} y))
      (inferInstanceAs (IsWellOrder (ULift α) (ULift.down ⁻¹'o r))) = lift.{v} (type r) :=
  rfl

theorem _root_.RelIso.ordinal_lift_type_eq {α : Type u} {β : Type v} {r : α → α → Prop}
    {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) :
    lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinal_type_eq
#align rel_iso.ordinal_lift_type_eq RelIso.ordinal_lift_type_eq

-- @[simp]
theorem type_lift_preimage {α : Type u} {β : Type v} (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq
#align ordinal.type_lift_preimage Ordinal.type_lift_preimage

@[simp, nolint simpNF]
theorem type_lift_preimage_aux {α : Type u} {β : Type v} (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (@type _ (fun x y => r (f x) (f y))
      (inferInstanceAs (IsWellOrder β (f ⁻¹'o r)))) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

/-- `lift.{max u v, u}` equals `lift.{v, u}`. -/
-- @[simp] -- Porting note: simp lemma never applies, tested
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩
#align ordinal.lift_umax Ordinal.lift_umax

/-- `lift.{max v u, u}` equals `lift.{v, u}`. -/
-- @[simp] -- Porting note: simp lemma never applies, tested
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax
#align ordinal.lift_umax' Ordinal.lift_umax'

/-- An ordinal lifted to a lower or equal universe equals itself. -/
-- @[simp] -- Porting note: simp lemma never applies, tested
theorem lift_id' (a : Ordinal) : lift a = a :=
  inductionOn a fun _ r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩
#align ordinal.lift_id' Ordinal.lift_id'

/-- An ordinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id : ∀ a, lift.{u, u} a = a :=
  lift_id'.{u, u}
#align ordinal.lift_id Ordinal.lift_id

/-- An ordinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Ordinal.{u}) : lift.{0} a = a :=
  lift_id' a
#align ordinal.lift_uzero Ordinal.lift_uzero

@[simp]
theorem lift_lift (a : Ordinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun _ _ _ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans <|
          (RelIso.preimage Equiv.ulift _).trans (RelIso.preimage Equiv.ulift _).symm⟩
#align ordinal.lift_lift Ordinal.lift_lift

theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ Nonempty (r ≼i s) :=
  ⟨fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equiv.ulift r).symm).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s))⟩,
    fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equiv.ulift r)).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s).symm)⟩⟩
#align ordinal.lift_type_le Ordinal.lift_type_le

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equiv.ulift r).symm.trans <| f.trans (RelIso.preimage Equiv.ulift s)⟩,
      fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩⟩
#align ordinal.lift_type_eq Ordinal.lift_type_eq

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
#align ordinal.lift_type_lt Ordinal.lift_type_lt

@[simp]
theorem lift_le {a b : Ordinal} : lift.{u,v} a ≤ lift.{u,v} b ↔ a ≤ b :=
  inductionOn a fun α r _ =>
    inductionOn b fun β s _ => by
      rw [← lift_umax]
      -- ⊢ lift.{max v u, v} (type r) ≤ lift.{max v u, v} (type s) ↔ type r ≤ type s
      exact lift_type_le.{_,_,u}
      -- 🎉 no goals
#align ordinal.lift_le Ordinal.lift_le

@[simp]
theorem lift_inj {a b : Ordinal} : lift.{u,v} a = lift.{u,v} b ↔ a = b := by
  simp only [le_antisymm_iff, lift_le]
  -- 🎉 no goals
#align ordinal.lift_inj Ordinal.lift_inj

@[simp]
theorem lift_lt {a b : Ordinal} : lift.{u,v} a < lift.{u,v} b ↔ a < b := by
  simp only [lt_iff_le_not_le, lift_le]
  -- 🎉 no goals
#align ordinal.lift_lt Ordinal.lift_lt

@[simp]
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _
#align ordinal.lift_zero Ordinal.lift_zero

@[simp]
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _
#align ordinal.lift_one Ordinal.lift_one

@[simp]
theorem lift_card (a) : Cardinal.lift.{u,v} (card a)= card (lift.{u,v} a) :=
  inductionOn a fun _ _ _ => rfl
#align ordinal.lift_card Ordinal.lift_card

theorem lift_down' {a : Cardinal.{u}} {b : Ordinal.{max u v}}
    (h : card.{max u v} b ≤ Cardinal.lift.{v,u} a) : ∃ a', lift.{v,u} a' = b :=
  let ⟨c, e⟩ := Cardinal.lift_down h
  Cardinal.inductionOn c
    (fun α =>
      inductionOn b fun β s _ e' => by
        rw [card_type, ← Cardinal.lift_id'.{max u v, u} #β, ← Cardinal.lift_umax.{u, v},
          lift_mk_eq.{u, max u v, max u v}] at e'
        cases' e' with f
        -- ⊢ ∃ a', lift.{v, u} a' = type s
        have g := RelIso.preimage f s
        -- ⊢ ∃ a', lift.{v, u} a' = type s
        haveI := (g : f ⁻¹'o s ↪r s).isWellOrder
        -- ⊢ ∃ a', lift.{v, u} a' = type s
        have := lift_type_eq.{u, max u v, max u v}.2 ⟨g⟩
        -- ⊢ ∃ a', lift.{v, u} a' = type s
        rw [lift_id, lift_umax.{u, v}] at this
        -- ⊢ ∃ a', lift.{v, u} a' = type s
        exact ⟨_, this⟩)
        -- 🎉 no goals
    e
#align ordinal.lift_down' Ordinal.lift_down'

theorem lift_down {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b ≤ lift.{v,u} a) :
    ∃ a', lift.{v,u} a' = b :=
  @lift_down' (card a) _ (by rw [lift_card]; exact card_le_card h)
                             -- ⊢ card b ≤ card (lift.{v, u} a)
                                             -- 🎉 no goals
#align ordinal.lift_down Ordinal.lift_down

theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b ≤ lift.{v,u} a ↔ ∃ a', lift.{v,u} a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨_, e, h⟩ => e ▸ lift_le.2 h⟩
#align ordinal.le_lift_iff Ordinal.le_lift_iff

theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b < lift.{v,u} a ↔ ∃ a', lift.{v,u} a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down (le_of_lt h)
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨_, e, h⟩ => e ▸ lift_lt.2 h⟩
#align ordinal.lt_lift_iff Ordinal.lt_lift_iff

/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initialSeg : @InitialSeg Ordinal.{u} Ordinal.{max u v} (· < ·) (· < ·) :=
  ⟨⟨⟨lift.{v}, fun _ _ => lift_inj.1⟩, lift_lt⟩, fun _ _ h => lift_down (le_of_lt h)⟩
#align ordinal.lift.initial_seg Ordinal.lift.initialSeg

@[simp]
theorem lift.initialSeg_coe : (lift.initialSeg.{u,v} : Ordinal → Ordinal) = lift.{v,u} :=
  rfl
#align ordinal.lift.initial_seg_coe Ordinal.lift.initialSeg_coe

/-! ### The first infinite ordinal `omega` -/


/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : Ordinal.{u} :=
  lift <| @type ℕ (· < ·) _
#align ordinal.omega Ordinal.omega

-- mathport name: ordinal.omega
@[inherit_doc]
scoped notation "ω" => Ordinal.omega

/-- Note that the presence of this lemma makes `simp [omega]` form a loop. -/
@[simp]
theorem type_nat_lt : @type ℕ (· < ·) _ = ω :=
  (lift_id _).symm
#align ordinal.type_nat_lt Ordinal.type_nat_lt

@[simp]
theorem card_omega : card ω = ℵ₀ :=
  rfl
#align ordinal.card_omega Ordinal.card_omega

@[simp]
theorem lift_omega : lift ω = ω :=
  lift_lift _
#align ordinal.lift_omega Ordinal.lift_omega

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`OrdinalArithmetic.lean`.
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
          -- ⊢ Sum.Lex r (Sum.Lex s t) (↑(sumAssoc α β γ) a) (↑(sumAssoc α β γ) b) ↔ Sum.Le …
          rcases a with (⟨a | a⟩ | a) <;> rcases b with (⟨b | b⟩ | b) <;>
            simp only [sumAssoc_apply_inl_inl, sumAssoc_apply_inl_inr, sumAssoc_apply_inr,
              Sum.lex_inl_inl, Sum.lex_inr_inr, Sum.Lex.sep, Sum.lex_inr_inl]⟩⟩

@[simp]
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  inductionOn o₁ fun _ __ => inductionOn o₂ fun _ _ _ => rfl
#align ordinal.card_add Ordinal.card_add

@[simp]
theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s :=
  rfl
#align ordinal.type_sum_lex Ordinal.type_sum_lex

@[simp]
theorem card_nat (n : ℕ) : card.{u} n = n := by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]
  -- 🎉 no goals
#align ordinal.card_nat Ordinal.card_nat

-- Porting note: Rewritten proof of elim, previous version was difficult to debug
instance add_covariantClass_le : CovariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· ≤ ·) where
  elim := fun c a b h => by
    revert h c
    -- ⊢ ∀ (c : Ordinal.{u}), a ≤ b → c + a ≤ c + b
    refine inductionOn a (fun α₁ r₁ _ ↦ ?_)
    -- ⊢ ∀ (c : Ordinal.{u}), type r₁ ≤ b → c + type r₁ ≤ c + b
    refine inductionOn b (fun α₂ r₂ _ ↦ ?_)
    -- ⊢ ∀ (c : Ordinal.{u}), type r₁ ≤ type r₂ → c + type r₁ ≤ c + type r₂
    rintro c ⟨⟨⟨f, fo⟩, fi⟩⟩
    -- ⊢ c + type r₁ ≤ c + type r₂
    refine inductionOn c (fun β s _ ↦ ?_)
    -- ⊢ type s + type r₁ ≤ type s + type r₂
    have := (Embedding.refl β).sumMap f
    -- ⊢ type s + type r₁ ≤ type s + type r₂
    refine ⟨⟨⟨(Embedding.refl.{u+1} _).sumMap f, ?_⟩, ?_⟩⟩
    -- ⊢ ∀ {a b : β ⊕ α₁}, Sum.Lex s r₂ (↑(Embedding.sumMap (Embedding.refl β) f) a)  …
    · intros a b
      -- ⊢ Sum.Lex s r₂ (↑(Embedding.sumMap (Embedding.refl β) f) a) (↑(Embedding.sumMa …
      match a, b with
      | Sum.inl a, Sum.inl b => exact Sum.lex_inl_inl.trans Sum.lex_inl_inl.symm
      | Sum.inl a, Sum.inr b => apply iff_of_true <;> apply Sum.Lex.sep
      | Sum.inr a, Sum.inl b => apply iff_of_false <;> exact Sum.lex_inr_inl
      | Sum.inr a, Sum.inr b => exact Sum.lex_inr_inr.trans <| fo.trans Sum.lex_inr_inr.symm
    · intros a b H
      -- ⊢ ∃ a', ↑{ toEmbedding := Embedding.sumMap (Embedding.refl β) f, map_rel_iff'  …
      match a, b, H with
      | _, Sum.inl b, _ => exact ⟨Sum.inl b, rfl⟩
      | Sum.inl a, Sum.inr b, H => exact (Sum.lex_inr_inl H).elim
      | Sum.inr a, Sum.inr b, H =>
        let ⟨w, h⟩ := fi _ _ (Sum.lex_inr_inr.1 H)
        exact ⟨Sum.inr w, congr_arg Sum.inr h⟩
#align ordinal.add_covariant_class_le Ordinal.add_covariantClass_le

-- Porting note: Rewritten proof of elim, previous version was difficult to debug
instance add_swap_covariantClass_le :
    CovariantClass Ordinal.{u} Ordinal.{u} (swap (· + ·)) (· ≤ ·) where
  elim := fun c a b h => by
    revert h c
    -- ⊢ ∀ (c : Ordinal.{u}), a ≤ b → Function.swap (fun x x_1 => x + x_1) c a ≤ Func …
    refine inductionOn a (fun α₁ r₁ _ ↦ ?_)
    -- ⊢ ∀ (c : Ordinal.{u}), type r₁ ≤ b → Function.swap (fun x x_1 => x + x_1) c (t …
    refine inductionOn b (fun α₂ r₂ _ ↦ ?_)
    -- ⊢ ∀ (c : Ordinal.{u}), type r₁ ≤ type r₂ → Function.swap (fun x x_1 => x + x_1 …
    rintro c ⟨⟨⟨f, fo⟩, fi⟩⟩
    -- ⊢ Function.swap (fun x x_1 => x + x_1) c (type r₁) ≤ Function.swap (fun x x_1  …
    refine inductionOn c (fun β s _ ↦ ?_)
    -- ⊢ Function.swap (fun x x_1 => x + x_1) (type s) (type r₁) ≤ Function.swap (fun …
    exact @RelEmbedding.ordinal_type_le _ _ (Sum.Lex r₁ s) (Sum.Lex r₂ s) _ _
              ⟨f.sumMap (Embedding.refl _), by
                intro a b
                constructor <;> intro H
                · cases' a with a a <;> cases' b with b b <;> cases H <;> constructor <;>
                    [rwa [← fo]; assumption]
                · cases H <;> constructor <;> [rwa [fo]; assumption]⟩
#align ordinal.add_swap_covariant_class_le Ordinal.add_swap_covariantClass_le

theorem le_add_right (a b : Ordinal) : a ≤ a + b := by
  simpa only [add_zero] using add_le_add_left (Ordinal.zero_le b) a
  -- 🎉 no goals
#align ordinal.le_add_right Ordinal.le_add_right

theorem le_add_left (a b : Ordinal) : a ≤ b + a := by
  simpa only [zero_add] using add_le_add_right (Ordinal.zero_le b) a
  -- 🎉 no goals
#align ordinal.le_add_left Ordinal.le_add_left

instance linearOrder : LinearOrder Ordinal :=
  {inferInstanceAs (PartialOrder Ordinal) with
    le_total := fun a b =>
      match lt_or_eq_of_le (le_add_left b a), lt_or_eq_of_le (le_add_right a b) with
      | Or.inr h, _ => by rw [h]; exact Or.inl (le_add_right _ _)
                          -- ⊢ a ≤ a + b ∨ a + b ≤ a
                                  -- 🎉 no goals
      | _, Or.inr h => by rw [h]; exact Or.inr (le_add_left _ _)
                          -- ⊢ a + b ≤ b ∨ b ≤ a + b
                                  -- 🎉 no goals
      | Or.inl h₁, Or.inl h₂ => by
        revert h₁ h₂
        -- ⊢ b < a + b → a < a + b → a ≤ b ∨ b ≤ a
        refine inductionOn a ?_
        -- ⊢ ∀ (α : Type ?u.163980) (r : α → α → Prop) [inst : IsWellOrder α r], b < type …
        intro α₁ r₁ _
        -- ⊢ b < type r₁ + b → type r₁ < type r₁ + b → type r₁ ≤ b ∨ b ≤ type r₁
        refine inductionOn b ?_
        -- ⊢ ∀ (α : Type ?u.163980) (r : α → α → Prop) [inst : IsWellOrder α r], type r < …
        intro α₂ r₂ _ ⟨f⟩ ⟨g⟩
        -- ⊢ type r₁ ≤ type r₂ ∨ type r₂ ≤ type r₁
        rw [← typein_top f, ← typein_top g, le_iff_lt_or_eq, le_iff_lt_or_eq,
                 typein_lt_typein, typein_lt_typein]
        rcases trichotomous_of (Sum.Lex r₁ r₂) g.top f.top with (h | h | h) <;>
          [exact Or.inl (Or.inl h); (left; right; rw [h]); exact Or.inr (Or.inl h)]
    decidableLE := Classical.decRel _ }

instance wellFoundedLT : WellFoundedLT Ordinal :=
  ⟨lt_wf⟩

instance isWellOrder : IsWellOrder Ordinal (· < ·) where

instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  IsWellOrder.conditionallyCompleteLinearOrderBot _

@[simp]
theorem max_zero_left : ∀ a : Ordinal, max 0 a = a :=
  max_bot_left
#align ordinal.max_zero_left Ordinal.max_zero_left

@[simp]
theorem max_zero_right : ∀ a : Ordinal, max a 0 = a :=
  max_bot_right
#align ordinal.max_zero_right Ordinal.max_zero_right

@[simp]
theorem max_eq_zero {a b : Ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  max_eq_bot
#align ordinal.max_eq_zero Ordinal.max_eq_zero

@[simp]
theorem sInf_empty : sInf (∅ : Set Ordinal) = 0 :=
  dif_neg Set.not_nonempty_empty
#align ordinal.Inf_empty Ordinal.sInf_empty

-- ### Successor order properties
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
        -- ⊢ type r + 1 ≤ type s
        refine' ⟨⟨RelEmbedding.ofMonotone (Sum.rec f fun _ => t) (fun a b ↦ _), fun a b ↦ _⟩⟩
        -- ⊢ Sum.Lex r EmptyRelation a b → s ((fun t_1 => Sum.rec (↑f) (fun x => t) t_1)  …
        · rcases a with (a | _) <;> rcases b with (b | _)
          -- ⊢ Sum.Lex r EmptyRelation (Sum.inl a) b → s ((fun t_1 => Sum.rec (↑f) (fun x = …
                                    -- ⊢ Sum.Lex r EmptyRelation (Sum.inl a) (Sum.inl b) → s ((fun t_1 => Sum.rec (↑f …
                                    -- ⊢ Sum.Lex r EmptyRelation (Sum.inr val✝) (Sum.inl b) → s ((fun t_1 => Sum.rec  …
          · simpa only [Sum.lex_inl_inl] using f.map_rel_iff.2
            -- 🎉 no goals
          · intro
            -- ⊢ s ((fun t_1 => Sum.rec (↑f) (fun x => t) t_1) (Sum.inl a)) ((fun t_1 => Sum. …
            rw [hf]
            -- ⊢ ∃ a_1, ↑f a_1 = (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) (Sum.inl a)
            exact ⟨_, rfl⟩
            -- 🎉 no goals
          · exact False.elim ∘ Sum.lex_inr_inl
            -- 🎉 no goals
          · exact False.elim ∘ Sum.lex_inr_inr.1
            -- 🎉 no goals
        · rcases a with (a | _)
          -- ⊢ s b (↑(RelEmbedding.ofMonotone (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) (_ …
          · intro h
            -- ⊢ ∃ a', ↑(RelEmbedding.ofMonotone (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) ( …
            have := @PrincipalSeg.init _ _ _ _ _ ⟨f, t, hf⟩ _ _ h
            -- ⊢ ∃ a', ↑(RelEmbedding.ofMonotone (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) ( …
            cases' this with w h
            -- ⊢ ∃ a', ↑(RelEmbedding.ofMonotone (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) ( …
            exact ⟨Sum.inl w, h⟩
            -- 🎉 no goals
          · intro h
            -- ⊢ ∃ a', ↑(RelEmbedding.ofMonotone (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) ( …
            cases' (hf b).1 h with w h
            -- ⊢ ∃ a', ↑(RelEmbedding.ofMonotone (fun t_1 => Sum.rec (↑f) (fun x => t) t_1) ( …
            exact ⟨Sum.inl w, h⟩⟩
            -- 🎉 no goals

instance noMaxOrder : NoMaxOrder Ordinal :=
  ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

instance succOrder : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) succ_le_iff'

@[simp]
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl
#align ordinal.add_one_eq_succ Ordinal.add_one_eq_succ

@[simp]
theorem succ_zero : succ (0 : Ordinal) = 1 :=
  zero_add 1
#align ordinal.succ_zero Ordinal.succ_zero

-- Porting note: Proof used to be rfl
@[simp]
theorem succ_one : succ (1 : Ordinal) = 2 := by
  unfold instOfNat OfNat.ofNat
  -- ⊢ succ One.toOfNat1.1 = { ofNat := ↑2 }.1
  simpa using by rfl
  -- 🎉 no goals
#align ordinal.succ_one Ordinal.succ_one

theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assoc _ _ _).symm
#align ordinal.add_succ Ordinal.add_succ

theorem one_le_iff_pos {o : Ordinal} : 1 ≤ o ↔ 0 < o := by rw [← succ_zero, succ_le_iff]
                                                           -- 🎉 no goals
#align ordinal.one_le_iff_pos Ordinal.one_le_iff_pos

theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 := by
  rw [one_le_iff_pos, Ordinal.pos_iff_ne_zero]
  -- 🎉 no goals
#align ordinal.one_le_iff_ne_zero Ordinal.one_le_iff_ne_zero

theorem succ_pos (o : Ordinal) : 0 < succ o :=
  bot_lt_succ o
#align ordinal.succ_pos Ordinal.succ_pos

theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  ne_of_gt <| succ_pos o
#align ordinal.succ_ne_zero Ordinal.succ_ne_zero

theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 := by
  simpa using @lt_succ_bot_iff _ _ _ a _ _
  -- 🎉 no goals
#align ordinal.lt_one_iff_zero Ordinal.lt_one_iff_zero

theorem le_one_iff {a : Ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 := by
  simpa using @le_succ_bot_iff _ _ _ a _
  -- 🎉 no goals
#align ordinal.le_one_iff Ordinal.le_one_iff

@[simp]
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp only [← add_one_eq_succ, card_add, card_one]
  -- 🎉 no goals
#align ordinal.card_succ Ordinal.card_succ

theorem nat_cast_succ (n : ℕ) : ↑n.succ = succ (n : Ordinal) :=
  rfl
#align ordinal.nat_cast_succ Ordinal.nat_cast_succ

instance uniqueIioOne : Unique (Iio (1 : Ordinal))
    where
  default := ⟨0, by simp⟩
                    -- 🎉 no goals
  uniq a := Subtype.ext <| lt_one_iff_zero.1 a.2
#align ordinal.unique_Iio_one Ordinal.uniqueIioOne

instance uniqueOutOne : Unique (1 : Ordinal).out.α
    where
  default := enum (· < ·) 0 (by simp)
                                -- 🎉 no goals
  uniq a := by
    unfold default
    -- ⊢ a = { default := enum (fun x x_1 => x < x_1) 0 (_ : 0 < type fun x x_1 => x  …
    rw [← @enum_typein _ (· < ·) (isWellOrder_out_lt _) a]
    -- ⊢ enum (fun x x_1 => x < x_1) (typein (fun x x_1 => x < x_1) a) (_ : typein (f …
    congr
    -- ⊢ typein (fun x x_1 => x < x_1) a = 0
    rw [← lt_one_iff_zero]
    -- ⊢ typein (fun x x_1 => x < x_1) a < 1
    apply typein_lt_self
    -- 🎉 no goals
#align ordinal.unique_out_one Ordinal.uniqueOutOne

theorem one_out_eq (x : (1 : Ordinal).out.α) : x = enum (· < ·) 0 (by simp) :=
                                                                      -- 🎉 no goals
  Unique.eq_default x
#align ordinal.one_out_eq Ordinal.one_out_eq

/-! ### Extra properties of typein and enum -/


@[simp]
theorem typein_one_out (x : (1 : Ordinal).out.α) :
    @typein _ (· < ·) (isWellOrder_out_lt _) x = 0 := by
  rw [one_out_eq x, typein_enum]
  -- 🎉 no goals
#align ordinal.typein_one_out Ordinal.typein_one_out

@[simp]
theorem typein_le_typein (r : α → α → Prop) [IsWellOrder α r] {x x' : α} :
    typein r x ≤ typein r x' ↔ ¬r x' x := by rw [← not_lt, typein_lt_typein]
                                             -- 🎉 no goals
#align ordinal.typein_le_typein Ordinal.typein_le_typein

-- @[simp] -- Porting note: simp can prove this
theorem typein_le_typein' (o : Ordinal) {x x' : o.out.α} :
    @typein _ (· < ·) (isWellOrder_out_lt _) x ≤ @typein _ (· < ·) (isWellOrder_out_lt _) x'
      ↔ x ≤ x' := by
  rw [typein_le_typein]
  -- ⊢ ¬x' < x ↔ x ≤ x'
  exact not_lt
  -- 🎉 no goals
#align ordinal.typein_le_typein' Ordinal.typein_le_typein'

-- Porting note: added nolint, simpnf linter falsely claims it never applies
@[simp, nolint simpNF]
theorem enum_le_enum (r : α → α → Prop) [IsWellOrder α r] {o o' : Ordinal} (ho : o < type r)
    (ho' : o' < type r) : ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' := by
  rw [← @not_lt _ _ o' o, enum_lt_enum ho']
  -- 🎉 no goals
#align ordinal.enum_le_enum Ordinal.enum_le_enum

@[simp]
theorem enum_le_enum' (a : Ordinal) {o o' : Ordinal} (ho : o < type (· < ·))
    (ho' : o' < type (· < ·)) : enum (· < ·) o ho ≤ @enum a.out.α (· < ·) _ o' ho' ↔ o ≤ o' := by
  rw [← @enum_le_enum _ (· < ·) (isWellOrder_out_lt _), ← not_lt]
  -- 🎉 no goals
#align ordinal.enum_le_enum' Ordinal.enum_le_enum'

theorem enum_zero_le {r : α → α → Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) :
    ¬r a (enum r 0 h0) := by
  rw [← enum_typein r a, enum_le_enum r]
  -- ⊢ 0 ≤ typein r a
  apply Ordinal.zero_le
  -- 🎉 no goals
#align ordinal.enum_zero_le Ordinal.enum_zero_le

theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.out.α) :
    @enum o.out.α (· < ·) _ 0 (by rwa [type_lt]) ≤ a := by
                                  -- 🎉 no goals
  rw [← not_lt]
  -- ⊢ ¬a < enum (fun x x_1 => x < x_1) 0 (_ : 0 < type fun x x_1 => x < x_1)
  apply enum_zero_le
  -- 🎉 no goals
#align ordinal.enum_zero_le' Ordinal.enum_zero_le'

theorem le_enum_succ {o : Ordinal} (a : (succ o).out.α) :
    a ≤
      @enum (succ o).out.α (· < ·) _ o
        (by
          rw [type_lt]
          -- ⊢ o < succ o
          exact lt_succ o) := by
          -- 🎉 no goals
  rw [← @enum_typein _ (· < ·) (isWellOrder_out_lt _) a, enum_le_enum', ← lt_succ_iff]
  -- ⊢ typein (fun x x_1 => x < x_1) a < succ o
  apply typein_lt_self
  -- 🎉 no goals
#align ordinal.le_enum_succ Ordinal.le_enum_succ

@[simp]
theorem enum_inj {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Ordinal} (h₁ : o₁ < type r)
    (h₂ : o₂ < type r) : enum r o₁ h₁ = enum r o₂ h₂ ↔ o₁ = o₂ :=
  (typein.principalSeg r).subrelIso.injective.eq_iff.trans Subtype.mk_eq_mk
#align ordinal.enum_inj Ordinal.enum_inj

-- TODO: Can we remove this definition and just use `(typein.principalSeg r).subrelIso` directly?
/-- A well order `r` is order isomorphic to the set of ordinals smaller than `type r`. -/
@[simps]
def enumIso (r : α → α → Prop) [IsWellOrder α r] : Subrel (· < ·) (· < type r) ≃r r :=
  { (typein.principalSeg r).subrelIso with
    toFun := fun x ↦ enum r x.1 x.2
    invFun := fun x ↦ ⟨typein r x, typein_lt_type r x⟩ }
#align ordinal.enum_iso Ordinal.enumIso

/-- The order isomorphism between ordinals less than `o` and `o.out.α`. -/
@[simps!]
noncomputable def enumIsoOut (o : Ordinal) : Set.Iio o ≃o o.out.α
    where
  toFun x :=
    enum (· < ·) x.1 <| by
      rw [type_lt]
      -- ⊢ ↑x < o
      exact x.2
      -- 🎉 no goals
  invFun x := ⟨@typein _ (· < ·) (isWellOrder_out_lt _) x, typein_lt_self x⟩
  left_inv := fun ⟨o', h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv h := enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    -- ⊢ ↑{ toFun := fun x => enum (fun x x_1 => x < x_1) ↑x (_ : ↑x < type fun x x_1 …
    apply enum_le_enum'
    -- 🎉 no goals
#align ordinal.enum_iso_out Ordinal.enumIsoOut

/-- `o.out.α` is an `OrderBot` whenever `0 < o`. -/
def outOrderBotOfPos {o : Ordinal} (ho : 0 < o) : OrderBot o.out.α where
  bot_le := enum_zero_le' ho
#align ordinal.out_order_bot_of_pos Ordinal.outOrderBotOfPos

theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (· < ·) 0 (by rwa [type_lt]) =
                       -- 🎉 no goals
      haveI H := outOrderBotOfPos ho
      ⊥ :=
  rfl
#align ordinal.enum_zero_eq_bot Ordinal.enum_zero_eq_bot

/-! ### Universal ordinal -/


-- intended to be used with explicit universe parameters
/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `Ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
 @[nolint checkUnivs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)
#align ordinal.univ Ordinal.univ

theorem univ_id : univ.{u, u + 1} = @type Ordinal (· < ·) _ :=
  lift_id _
#align ordinal.univ_id Ordinal.univ_id

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _
#align ordinal.lift_univ Ordinal.lift_univ

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _
#align ordinal.univ_umax Ordinal.univ_umax

/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principalSeg : @PrincipalSeg Ordinal.{u} Ordinal.{max (u + 1) v} (· < ·) (· < ·) :=
  ⟨↑lift.initialSeg.{u, max (u + 1) v}, univ.{u, v}, by
    refine' fun b => inductionOn b _; intro β s _
    -- ⊢ ∀ (α : Type (max (u + 1) v)) (r : α → α → Prop) [inst : IsWellOrder α r], ty …
                                      -- ⊢ type s < univ ↔ ∃ a, ↑initialSeg.toRelEmbedding a = type s
    rw [univ, ← lift_umax]; constructor <;> intro h
    -- ⊢ type s < lift.{max (u + 1) v, u + 1} (type fun x x_1 => x < x_1) ↔ ∃ a, ↑ini …
                            -- ⊢ type s < lift.{max (u + 1) v, u + 1} (type fun x x_1 => x < x_1) → ∃ a, ↑ini …
                                            -- ⊢ ∃ a, ↑initialSeg.toRelEmbedding a = type s
                                            -- ⊢ type s < lift.{max (u + 1) v, u + 1} (type fun x x_1 => x < x_1)
    · rw [← lift_id (type s)] at h ⊢
      -- ⊢ ∃ a, ↑initialSeg.toRelEmbedding a = lift.{max (u + 1) v, max (u + 1) v} (typ …
      cases' lift_type_lt.{_,_,v}.1 h with f
      -- ⊢ ∃ a, ↑initialSeg.toRelEmbedding a = lift.{max (u + 1) v, max (u + 1) v} (typ …
      cases' f with f a hf
      -- ⊢ ∃ a, ↑initialSeg.toRelEmbedding a = lift.{max (u + 1) v, max (u + 1) v} (typ …
      exists a
      -- ⊢ ↑initialSeg.toRelEmbedding a = lift.{max (u + 1) v, max (u + 1) v} (type s)
      revert hf
      -- ⊢ (∀ (b : Ordinal.{u}), b < a ↔ ∃ a, ↑f a = b) → ↑initialSeg.toRelEmbedding a  …
      -- Porting note: apply inductionOn does not work, refine does
      refine inductionOn a ?_
      -- ⊢ ∀ (α : Type u) (r : α → α → Prop) [inst : IsWellOrder α r], (∀ (b : Ordinal. …
      intro α r _ hf
      -- ⊢ ↑initialSeg.toRelEmbedding (type r) = lift.{max (u + 1) v, max (u + 1) v} (t …
      refine'
        lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
          ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone _ _) _).symm⟩
      · exact fun b => enum r (f b) ((hf _).2 ⟨_, rfl⟩)
        -- 🎉 no goals
      · refine' fun a b h => (typein_lt_typein r).1 _
        -- ⊢ typein r (enum r (↑f a) (_ : ↑f a < type r)) < typein r (enum r (↑f b) (_ :  …
        rw [typein_enum, typein_enum]
        -- ⊢ ↑f a < ↑f b
        exact f.map_rel_iff.2 h
        -- 🎉 no goals
      · intro a'
        -- ⊢ ∃ a, ↑(RelEmbedding.ofMonotone (fun b => enum r (↑f b) (_ : ↑f b < type r))  …
        cases' (hf _).1 (typein_lt_type _ a') with b e
        -- ⊢ ∃ a, ↑(RelEmbedding.ofMonotone (fun b => enum r (↑f b) (_ : ↑f b < type r))  …
        exists b
        -- ⊢ ↑(RelEmbedding.ofMonotone (fun b => enum r (↑f b) (_ : ↑f b < type r)) (_ :  …
        simp
        -- ⊢ enum r (↑f b) (_ : ↑f b < type r) = a'
        simp [e]
        -- 🎉 no goals
    · cases' h with a e
      -- ⊢ type s < lift.{max (u + 1) v, u + 1} (type fun x x_1 => x < x_1)
      rw [← e]
      -- ⊢ ↑initialSeg.toRelEmbedding a < lift.{max (u + 1) v, u + 1} (type fun x x_1 = …
      refine inductionOn a ?_
      -- ⊢ ∀ (α : Type u) (r : α → α → Prop) [inst : IsWellOrder α r], ↑initialSeg.toRe …
      intro α r _
      -- ⊢ ↑initialSeg.toRelEmbedding (type r) < lift.{max (u + 1) v, u + 1} (type fun  …
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein.principalSeg r⟩⟩
      -- 🎉 no goals
#align ordinal.lift.principal_seg Ordinal.lift.principalSeg

@[simp]
theorem lift.principalSeg_coe :
    (lift.principalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl
#align ordinal.lift.principal_seg_coe Ordinal.lift.principalSeg_coe

-- Porting note: Added universe hints below
@[simp]
theorem lift.principalSeg_top : (lift.principalSeg.{u,v}).top = univ.{u,v} :=
  rfl
#align ordinal.lift.principal_seg_top Ordinal.lift.principalSeg_top

theorem lift.principalSeg_top' : lift.principalSeg.{u, u + 1}.top = @type Ordinal (· < ·) _ := by
  simp only [lift.principalSeg_top, univ_id]
  -- 🎉 no goals
#align ordinal.lift.principal_seg_top' Ordinal.lift.principalSeg_top'

end Ordinal

/-! ### Representing a cardinal with an ordinal -/


namespace Cardinal

open Ordinal

@[simp]
theorem mk_ordinal_out (o : Ordinal) : #o.out.α = o.card :=
  (Ordinal.card_type _).symm.trans <| by rw [Ordinal.type_lt]
                                         -- 🎉 no goals
#align cardinal.mk_ordinal_out Cardinal.mk_ordinal_out

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : Cardinal) : Ordinal :=
  let F := fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2
  Quot.liftOn c F
    (by
      suffices : ∀ {α β}, α ≈ β → F α ≤ F β
      -- ⊢ ∀ (a b : Type u), Setoid.r a b → F a = F b
      exact fun α β h => (this h).antisymm (this (Setoid.symm h))
      -- ⊢ ∀ {α β : Type u}, α ≈ β → F α ≤ F β
      rintro α β ⟨f⟩
      -- ⊢ F α ≤ F β
      refine' le_ciInf_iff'.2 fun i => _
      -- ⊢ F α ≤ type ↑i
      haveI := @RelEmbedding.isWellOrder _ _ (f ⁻¹'o i.1) _ (↑(RelIso.preimage f i.1)) i.2
      -- ⊢ F α ≤ type ↑i
      exact
        (ciInf_le' _
              (Subtype.mk (f ⁻¹'o i.val)
                (@RelEmbedding.isWellOrder _ _ _ _ (↑(RelIso.preimage f i.1)) i.2))).trans_eq
          (Quot.sound ⟨RelIso.preimage f i.1⟩))
#align cardinal.ord Cardinal.ord

theorem ord_eq_Inf (α : Type u) : ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2 :=
  rfl
#align cardinal.ord_eq_Inf Cardinal.ord_eq_Inf

theorem ord_eq (α) : ∃ (r : α → α → Prop) (wo : IsWellOrder α r), ord #α = @type α r wo :=
  let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩
#align cardinal.ord_eq Cardinal.ord_eq

theorem ord_le_type (r : α → α → Prop) [h : IsWellOrder α r] : ord #α ≤ type r :=
  ciInf_le' _ (Subtype.mk r h)
#align cardinal.ord_le_type Cardinal.ord_le_type

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
  inductionOn c fun α =>
    Ordinal.inductionOn o fun β s _ => by
      let ⟨r, _, e⟩ := ord_eq α
      -- ⊢ ord #α ≤ type s ↔ #α ≤ card (type s)
      skip; simp only [card_type]; constructor <;> intro h
      -- ⊢ ord #α ≤ type s ↔ #α ≤ card (type s)
            -- ⊢ ord #α ≤ type s ↔ #α ≤ #β
                                   -- ⊢ ord #α ≤ type s → #α ≤ #β
                                                   -- ⊢ #α ≤ #β
                                                   -- ⊢ ord #α ≤ type s
      · rw [e] at h
        -- ⊢ #α ≤ #β
        exact
          let ⟨f⟩ := h
          ⟨f.toEmbedding⟩
      · cases' h with f
        -- ⊢ ord #α ≤ type s
        have g := RelEmbedding.preimage f s
        -- ⊢ ord #α ≤ type s
        haveI := RelEmbedding.isWellOrder g
        -- ⊢ ord #α ≤ type s
        exact le_trans (ord_le_type _) g.ordinal_type_le
        -- 🎉 no goals
#align cardinal.ord_le Cardinal.ord_le

theorem gc_ord_card : GaloisConnection ord card := fun _ _ => ord_le
#align cardinal.gc_ord_card Cardinal.gc_ord_card

theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt
#align cardinal.lt_ord Cardinal.lt_ord

@[simp]
theorem card_ord (c) : (ord c).card = c :=
  Quotient.inductionOn c fun α => by
    let ⟨r, _, e⟩ := ord_eq α
    -- ⊢ card (ord (Quotient.mk isEquivalent α)) = Quotient.mk isEquivalent α
    -- Porting note: cardinal.mk_def is now Cardinal.mk'_def, not sure why
    simp only [mk'_def, e, card_type]
    -- 🎉 no goals
#align cardinal.card_ord Cardinal.card_ord

/-- Galois coinsertion between `Cardinal.ord` and `Ordinal.card`. -/
def gciOrdCard : GaloisCoinsertion ord card :=
  gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le
#align cardinal.gci_ord_card Cardinal.gciOrdCard

theorem ord_card_le (o : Ordinal) : o.card.ord ≤ o :=
  gc_ord_card.l_u_le _
#align cardinal.ord_card_le Cardinal.ord_card_le

theorem lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord :=
  lt_ord.2 <| lt_succ _
#align cardinal.lt_ord_succ_card Cardinal.lt_ord_succ_card

@[mono]
theorem ord_strictMono : StrictMono ord :=
  gciOrdCard.strictMono_l
#align cardinal.ord_strict_mono Cardinal.ord_strictMono

@[mono]
theorem ord_mono : Monotone ord :=
  gc_ord_card.monotone_l
#align cardinal.ord_mono Cardinal.ord_mono

@[simp]
theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
  gciOrdCard.l_le_l_iff
#align cardinal.ord_le_ord Cardinal.ord_le_ord

@[simp]
theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
  ord_strictMono.lt_iff_lt
#align cardinal.ord_lt_ord Cardinal.ord_lt_ord

@[simp]
theorem ord_zero : ord 0 = 0 :=
  gc_ord_card.l_bot
#align cardinal.ord_zero Cardinal.ord_zero

@[simp]
theorem ord_nat (n : ℕ) : ord n = n :=
  (ord_le.2 (card_nat n).ge).antisymm
    (by
      induction' n with n IH
      -- ⊢ ↑Nat.zero ≤ ord ↑Nat.zero
      · apply Ordinal.zero_le
        -- 🎉 no goals
      · exact succ_le_of_lt (IH.trans_lt <| ord_lt_ord.2 <| natCast_lt.2 (Nat.lt_succ_self n)))
        -- 🎉 no goals
#align cardinal.ord_nat Cardinal.ord_nat

@[simp]
theorem ord_one : ord 1 = 1 := by simpa using ord_nat 1
                                  -- 🎉 no goals
#align cardinal.ord_one Cardinal.ord_one

@[simp]
theorem lift_ord (c) : Ordinal.lift.{u,v} (ord c) = ord (lift.{u,v} c) := by
  refine' le_antisymm (le_of_forall_lt fun a ha => _) _
  -- ⊢ a < ord (lift.{u, v} c)
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, rfl, _⟩
    -- ⊢ Ordinal.lift.{u, v} a < ord (lift.{u, v} c)
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
    -- 🎉 no goals
  · rw [ord_le, ← lift_card, card_ord]
    -- 🎉 no goals
#align cardinal.lift_ord Cardinal.lift_ord

theorem mk_ord_out (c : Cardinal) : #c.ord.out.α = c := by simp
                                                           -- 🎉 no goals
#align cardinal.mk_ord_out Cardinal.mk_ord_out

theorem card_typein_lt (r : α → α → Prop) [IsWellOrder α r] (x : α) (h : ord #α = type r) :
    card (typein r x) < #α := by
  rw [← lt_ord, h]
  -- ⊢ typein r x < type r
  apply typein_lt_type
  -- 🎉 no goals
#align cardinal.card_typein_lt Cardinal.card_typein_lt

theorem card_typein_out_lt (c : Cardinal) (x : c.ord.out.α) :
    card (@typein _ (· < ·) (isWellOrder_out_lt _) x) < c := by
  rw [← lt_ord]
  -- ⊢ typein (fun x x_1 => x < x_1) x < ord c
  apply typein_lt_self
  -- 🎉 no goals
#align cardinal.card_typein_out_lt Cardinal.card_typein_out_lt

theorem ord_injective : Injective ord := by
  intro c c' h
  -- ⊢ c = c'
  rw [← card_ord c, ← card_ord c', h]
  -- 🎉 no goals
#align cardinal.ord_injective Cardinal.ord_injective

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.ofMonotone Cardinal.ord fun _ _ => Cardinal.ord_lt_ord.2)
#align cardinal.ord.order_embedding Cardinal.ord.orderEmbedding

@[simp]
theorem ord.orderEmbedding_coe : (ord.orderEmbedding : Cardinal → Ordinal) = ord :=
  rfl
#align cardinal.ord.order_embedding_coe Cardinal.ord.orderEmbedding_coe

-- intended to be used with explicit universe parameters
/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `Ordinal.{u}`, or `Cardinal.{u}`,
  as an element of `Cardinal.{v}` (when `u < v`). -/
@[nolint checkUnivs]
def univ :=
  lift.{v, u + 1} #Ordinal
#align cardinal.univ Cardinal.univ

theorem univ_id : univ.{u, u + 1} = #Ordinal :=
  lift_id _
#align cardinal.univ_id Cardinal.univ_id

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _
#align cardinal.lift_univ Cardinal.lift_univ

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _
#align cardinal.univ_umax Cardinal.univ_umax

theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [lift.principalSeg_coe, lift_ord, lift_succ, ord_le, succ_le_iff] using
    le_of_lt (lift.principalSeg.{u, u + 1}.lt_top (succ c).ord)
#align cardinal.lift_lt_univ Cardinal.lift_lt_univ

theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  have := lift_lt.{_, max (u+1) v}.2 (lift_lt_univ c)
  -- ⊢ lift.{max (u + 1) v, u} c < univ
  rw [lift_lift, lift_univ, univ_umax.{u,v}] at this
  -- ⊢ lift.{max (u + 1) v, u} c < univ
  exact this
  -- 🎉 no goals
#align cardinal.lift_lt_univ' Cardinal.lift_lt_univ'

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine' le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  -- ⊢ card o < univ
  have := lift.principalSeg.{u, v}.down.1 (by simpa only [lift.principalSeg_coe] using h)
  -- ⊢ card o < univ
  rcases this with ⟨o, h'⟩
  -- ⊢ card o✝ < univ
  rw [←h', lift.principalSeg_coe, ← lift_card]
  -- ⊢ lift.{max (u + 1) v, u} (card o) < univ
  apply lift_lt_univ'
  -- 🎉 no goals
#align cardinal.ord_univ Cardinal.ord_univ

theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    -- ⊢ ∃ c', c = lift.{u + 1, u} c'
    rw [ord_univ] at this
    -- ⊢ ∃ c', c = lift.{u + 1, u} c'
    cases' lift.principalSeg.{u, u + 1}.down.1 (by simpa only [lift.principalSeg_top] ) with o e
    -- ⊢ ∃ c', c = lift.{u + 1, u} c'
    have := card_ord c
    -- ⊢ ∃ c', c = lift.{u + 1, u} c'
    rw [← e, lift.principalSeg_coe, ← lift_card] at this
    -- ⊢ ∃ c', c = lift.{u + 1, u} c'
    exact ⟨_, this.symm⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ _⟩
    -- 🎉 no goals
#align cardinal.lt_univ Cardinal.lt_univ

theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, e, h'⟩ := lt_lift_iff.1 h
    -- ⊢ ∃ c', c = lift.{max (u + 1) v, u} c'
    rw [← univ_id] at h'
    -- ⊢ ∃ c', c = lift.{max (u + 1) v, u} c'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    -- ⊢ ∃ c', c = lift.{max (u + 1) v, u} c'
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ' _⟩
    -- 🎉 no goals
#align cardinal.lt_univ' Cardinal.lt_univ'

theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v+1,_} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  -- ⊢ Small.{v, u} α ↔ ∃ c', lift.{v + 1, u} #α = lift.{max u (v + 1), v} c'
  constructor
  -- ⊢ Small.{v, u} α → ∃ c', lift.{v + 1, u} #α = lift.{max u (v + 1), v} c'
  · rintro ⟨β, e⟩
    -- ⊢ ∃ c', lift.{v + 1, u} #α = lift.{max u (v + 1), v} c'
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
    -- 🎉 no goals
  · rintro ⟨c, hc⟩
    -- ⊢ Small.{v, u} α
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩
    -- 🎉 no goals
#align cardinal.small_iff_lift_mk_lt_univ Cardinal.small_iff_lift_mk_lt_univ

end Cardinal

namespace Ordinal

@[simp]
theorem card_univ : card univ.{u,v} = Cardinal.univ.{u,v} :=
  rfl
#align ordinal.card_univ Ordinal.card_univ

@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o := by
  rw [← Cardinal.ord_le, Cardinal.ord_nat]
  -- 🎉 no goals
#align ordinal.nat_le_card Ordinal.nat_le_card

@[simp]
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o := by
  rw [← succ_le_iff, ← succ_le_iff, ← nat_succ, nat_le_card]
  -- ⊢ ↑(Nat.succ n) ≤ o ↔ succ ↑n ≤ o
  rfl
  -- 🎉 no goals
#align ordinal.nat_lt_card Ordinal.nat_lt_card

@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card
#align ordinal.card_lt_nat Ordinal.card_lt_nat

@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card
#align ordinal.card_le_nat Ordinal.card_le_nat

@[simp]
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n := by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]
  -- 🎉 no goals
#align ordinal.card_eq_nat Ordinal.card_eq_nat

@[simp]
theorem type_fintype (r : α → α → Prop) [IsWellOrder α r] [Fintype α] : type r = Fintype.card α :=
  by rw [← card_eq_nat, card_type, mk_fintype]
     -- 🎉 no goals
#align ordinal.type_fintype Ordinal.type_fintype

theorem type_fin (n : ℕ) : @type (Fin n) (· < ·) _ = n := by simp
                                                             -- 🎉 no goals
#align ordinal.type_fin Ordinal.type_fin

end Ordinal
