/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.WithBot

/-!
# Orders on a sum type

This file defines the disjoint sum and the linear (aka lexicographic) sum of two orders and
provides relation instances for `Sum.LiftRel` and `Sum.Lex`.

We declare the disjoint sum of orders as the default set of instances. The linear order goes on a
type synonym.

## Main declarations

* `Sum.LE`, `Sum.LT`: Disjoint sum of orders.
* `Sum.Lex.LE`, `Sum.Lex.LT`: Lexicographic/linear sum of orders.

## Notation

* `α ⊕ₗ β`:  The linear sum of `α` and `β`.
-/


variable {α β γ : Type*}

namespace Sum

/-! ### Unbundled relation classes -/


section LiftRel

variable (r : α → α → Prop) (s : β → β → Prop)

@[refl]
theorem LiftRel.refl [IsRefl α r] [IsRefl β s] : ∀ x, LiftRel r s x x
  | inl a => LiftRel.inl (_root_.refl a)
  | inr a => LiftRel.inr (_root_.refl a)

instance [IsRefl α r] [IsRefl β s] : IsRefl (α ⊕ β) (LiftRel r s) :=
  ⟨LiftRel.refl _ _⟩

instance [IsIrrefl α r] [IsIrrefl β s] : IsIrrefl (α ⊕ β) (LiftRel r s) :=
  ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

@[trans]
theorem LiftRel.trans [IsTrans α r] [IsTrans β s] :
    ∀ {a b c}, LiftRel r s a b → LiftRel r s b c → LiftRel r s a c
  | _, _, _, LiftRel.inl hab, LiftRel.inl hbc => LiftRel.inl <| _root_.trans hab hbc
  | _, _, _, LiftRel.inr hab, LiftRel.inr hbc => LiftRel.inr <| _root_.trans hab hbc

instance [IsTrans α r] [IsTrans β s] : IsTrans (α ⊕ β) (LiftRel r s) :=
  ⟨fun _ _ _ => LiftRel.trans _ _⟩

instance [IsAntisymm α r] [IsAntisymm β s] : IsAntisymm (α ⊕ β) (LiftRel r s) :=
  ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

end LiftRel

section Lex

variable (r : α → α → Prop) (s : β → β → Prop)

instance [IsRefl α r] [IsRefl β s] : IsRefl (α ⊕ β) (Lex r s) :=
  ⟨by
    rintro (a | a)
    exacts [Lex.inl (refl _), Lex.inr (refl _)]⟩

instance [IsIrrefl α r] [IsIrrefl β s] : IsIrrefl (α ⊕ β) (Lex r s) :=
  ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

instance [IsTrans α r] [IsTrans β s] : IsTrans (α ⊕ β) (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hbc⟩ | ⟨hbc⟩)
    exacts [.inl (_root_.trans hab hbc), .sep _ _, .inr (_root_.trans hab hbc), .sep _ _]⟩

instance [IsAntisymm α r] [IsAntisymm β s] : IsAntisymm (α ⊕ β) (Lex r s) :=
  ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

instance [IsTotal α r] [IsTotal β s] : IsTotal (α ⊕ β) (Lex r s) :=
  ⟨fun a b =>
    match a, b with
    | inl a, inl b => (total_of r a b).imp Lex.inl Lex.inl
    | inl _, inr _ => Or.inl (Lex.sep _ _)
    | inr _, inl _ => Or.inr (Lex.sep _ _)
    | inr a, inr b => (total_of s a b).imp Lex.inr Lex.inr⟩

instance [IsTrichotomous α r] [IsTrichotomous β s] : IsTrichotomous (α ⊕ β) (Lex r s) :=
  ⟨fun a b =>
    match a, b with
    | inl a, inl b => (trichotomous_of r a b).imp3 Lex.inl (congr_arg _) Lex.inl
    | inl _, inr _ => Or.inl (Lex.sep _ _)
    | inr _, inl _ => Or.inr (Or.inr <| Lex.sep _ _)
    | inr a, inr b => (trichotomous_of s a b).imp3 Lex.inr (congr_arg _) Lex.inr⟩

instance [IsWellOrder α r] [IsWellOrder β s] :
    IsWellOrder (α ⊕ β) (Sum.Lex r s) where wf := Sum.lex_wf IsWellFounded.wf IsWellFounded.wf

end Lex

/-! ### Disjoint sum of two orders -/


section Disjoint

instance instLESum [LE α] [LE β] : LE (α ⊕ β) :=
  ⟨LiftRel (· ≤ ·) (· ≤ ·)⟩

instance instLTSum [LT α] [LT β] : LT (α ⊕ β) :=
  ⟨LiftRel (· < ·) (· < ·)⟩

theorem le_def [LE α] [LE β] {a b : α ⊕ β} : a ≤ b ↔ LiftRel (· ≤ ·) (· ≤ ·) a b :=
  Iff.rfl

theorem lt_def [LT α] [LT β] {a b : α ⊕ β} : a < b ↔ LiftRel (· < ·) (· < ·) a b :=
  Iff.rfl

@[simp]
theorem inl_le_inl_iff [LE α] [LE β] {a b : α} : (inl a : α ⊕ β) ≤ inl b ↔ a ≤ b :=
  liftRel_inl_inl

@[simp]
theorem inr_le_inr_iff [LE α] [LE β] {a b : β} : (inr a : α ⊕ β) ≤ inr b ↔ a ≤ b :=
  liftRel_inr_inr

@[simp]
theorem inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α ⊕ β) < inl b ↔ a < b :=
  liftRel_inl_inl

@[simp]
theorem inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α ⊕ β) < inr b ↔ a < b :=
  liftRel_inr_inr

@[simp]
theorem not_inl_le_inr [LE α] [LE β] {a : α} {b : β} : ¬inl b ≤ inr a :=
  not_liftRel_inl_inr

@[simp]
theorem not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl b < inr a :=
  not_liftRel_inl_inr

@[simp]
theorem not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬inr b ≤ inl a :=
  not_liftRel_inr_inl

@[simp]
theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr b < inl a :=
  not_liftRel_inr_inl

section Preorder

variable [Preorder α] [Preorder β]

instance instPreorderSum : Preorder (α ⊕ β) :=
  { instLESum, instLTSum with
    le_refl := fun _ => LiftRel.refl _ _ _,
    le_trans := fun _ _ _ => LiftRel.trans _ _,
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
      · rintro ⟨⟨hab⟩ | ⟨hab⟩, hba⟩
        · exact LiftRel.inl (hab.lt_of_not_ge fun h => hba <| LiftRel.inl h)
        · exact LiftRel.inr (hab.lt_of_not_ge fun h => hba <| LiftRel.inr h) }

theorem inl_mono : Monotone (inl : α → α ⊕ β) := fun _ _ => LiftRel.inl

theorem inr_mono : Monotone (inr : β → α ⊕ β) := fun _ _ => LiftRel.inr

theorem inl_strictMono : StrictMono (inl : α → α ⊕ β) := fun _ _ => LiftRel.inl

theorem inr_strictMono : StrictMono (inr : β → α ⊕ β) := fun _ _ => LiftRel.inr

end Preorder

instance [PartialOrder α] [PartialOrder β] : PartialOrder (α ⊕ β) :=
  { instPreorderSum with
    le_antisymm := fun _ _ => show LiftRel _ _ _ _ → _ from antisymm }

instance noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α ⊕ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

instance noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α ⊕ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

@[simp]
theorem noMinOrder_iff [LT α] [LT β] : NoMinOrder (α ⊕ β) ↔ NoMinOrder α ∧ NoMinOrder β :=
  ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inl a : α ⊕ β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inr_lt_inl h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inr a : α ⊕ β)
        · exact (not_inl_lt_inr h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMinOrder _ _ _ _ h.1 h.2⟩

@[simp]
theorem noMaxOrder_iff [LT α] [LT β] : NoMaxOrder (α ⊕ β) ↔ NoMaxOrder α ∧ NoMaxOrder β :=
  ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inl a : α ⊕ β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inl_lt_inr h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inr a : α ⊕ β)
        · exact (not_inr_lt_inl h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMaxOrder _ _ _ _ h.1 h.2⟩

instance denselyOrdered [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α ⊕ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, LiftRel.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), LiftRel.inl ha, LiftRel.inl hb⟩
    | inr _, inr _, LiftRel.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), LiftRel.inr ha, LiftRel.inr hb⟩⟩

@[simp]
theorem denselyOrdered_iff [LT α] [LT β] :
    DenselyOrdered (α ⊕ β) ↔ DenselyOrdered α ∧ DenselyOrdered β :=
  ⟨fun _ =>
    ⟨⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α ⊕ β) _ _ _ _ (inl_lt_inl_iff.2 h)
        · exact ⟨c, inl_lt_inl_iff.1 ha, inl_lt_inl_iff.1 hb⟩
        · exact (not_inl_lt_inr ha).elim⟩,
      ⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α ⊕ β) _ _ _ _ (inr_lt_inr_iff.2 h)
        · exact (not_inl_lt_inr hb).elim
        · exact ⟨c, inr_lt_inr_iff.1 ha, inr_lt_inr_iff.1 hb⟩⟩⟩,
    fun h => @Sum.denselyOrdered _ _ _ _ h.1 h.2⟩

@[simp]
theorem swap_le_swap_iff [LE α] [LE β] {a b : α ⊕ β} : a.swap ≤ b.swap ↔ a ≤ b :=
  liftRel_swap_iff

@[simp]
theorem swap_lt_swap_iff [LT α] [LT β] {a b : α ⊕ β} : a.swap < b.swap ↔ a < b :=
  liftRel_swap_iff

end Disjoint

/-! ### Linear sum of two orders -/


namespace Lex


/-- The linear sum of two orders -/
notation:30 α " ⊕ₗ " β:29 => _root_.Lex (α ⊕ β)

--TODO: Can we make `inlₗ`, `inrₗ` `local notation`?
/-- Lexicographical `Sum.inl`. Only used for pattern matching. -/
@[match_pattern]
abbrev _root_.Sum.inlₗ (x : α) : α ⊕ₗ β :=
  toLex (Sum.inl x)

/-- Lexicographical `Sum.inr`. Only used for pattern matching. -/
@[match_pattern]
abbrev _root_.Sum.inrₗ (x : β) : α ⊕ₗ β :=
  toLex (Sum.inr x)

/-- The linear/lexicographical `≤` on a sum. -/
protected instance LE [LE α] [LE β] : LE (α ⊕ₗ β) :=
  ⟨Lex (· ≤ ·) (· ≤ ·)⟩

/-- The linear/lexicographical `<` on a sum. -/
protected instance LT [LT α] [LT β] : LT (α ⊕ₗ β) :=
  ⟨Lex (· < ·) (· < ·)⟩

@[simp]
theorem toLex_le_toLex [LE α] [LE β] {a b : α ⊕ β} :
    toLex a ≤ toLex b ↔ Lex (· ≤ ·) (· ≤ ·) a b :=
  Iff.rfl

@[simp]
theorem toLex_lt_toLex [LT α] [LT β] {a b : α ⊕ β} :
    toLex a < toLex b ↔ Lex (· < ·) (· < ·) a b :=
  Iff.rfl

theorem le_def [LE α] [LE β] {a b : α ⊕ₗ β} : a ≤ b ↔ Lex (· ≤ ·) (· ≤ ·) (ofLex a) (ofLex b) :=
  Iff.rfl

theorem lt_def [LT α] [LT β] {a b : α ⊕ₗ β} : a < b ↔ Lex (· < ·) (· < ·) (ofLex a) (ofLex b) :=
  Iff.rfl

theorem inl_le_inl_iff [LE α] [LE β] {a b : α} : toLex (inl a : α ⊕ β) ≤ toLex (inl b) ↔ a ≤ b :=
  lex_inl_inl

theorem inr_le_inr_iff [LE α] [LE β] {a b : β} : toLex (inr a : α ⊕ β) ≤ toLex (inr b) ↔ a ≤ b :=
  lex_inr_inr

theorem inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (inl a : α ⊕ β) < toLex (inl b) ↔ a < b :=
  lex_inl_inl

theorem inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (inr a : α ⊕ₗ β) < toLex (inr b) ↔ a < b :=
  lex_inr_inr

theorem inl_le_inr [LE α] [LE β] (a : α) (b : β) : toLex (inl a) ≤ toLex (inr b) :=
  Lex.sep _ _

theorem inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (inl a) < toLex (inr b) :=
  Lex.sep _ _

theorem not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬toLex (inr b) ≤ toLex (inl a) :=
  lex_inr_inl

theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬toLex (inr b) < toLex (inl a) :=
  lex_inr_inl

/-- `toLex` promoted to a `RelIso` between `<` relations. -/
def toLexRelIsoLT [LT α] [LT β] :
    Sum.Lex (· < · : α → α → Prop) (· < · : β → β → Prop) ≃r (· < · : α ⊕ₗ β → _ → _) where
  toFun := toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
theorem toLexRelIsoLT_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α := α) (β := β)) = toLex :=
  rfl

@[simp]
theorem toLexRelIsoLT_symm_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α := α) (β := β)).symm = ofLex :=
  rfl

/-- `toLex` promoted to a `RelIso` between `≤` relations. -/
def toLexRelIsoLE [LE α] [LE β] :
    Sum.Lex (· ≤ · : α → α → Prop) (· ≤ · : β → β → Prop) ≃r (· ≤ · : α ⊕ₗ β → _ → _) where
  toFun := toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
theorem toLexRelIsoLE_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α := α) (β := β)) = toLex :=
  rfl

@[simp]
theorem toLexRelIsoLE_symm_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α := α) (β := β)).symm = ofLex :=
  rfl

section Preorder

variable [Preorder α] [Preorder β]

instance preorder : Preorder (α ⊕ₗ β) :=
  { Lex.LE, Lex.LT with
    le_refl := refl_of (Lex (· ≤ ·) (· ≤ ·)),
    le_trans := fun _ _ _ => trans_of (Lex (· ≤ ·) (· ≤ ·)),
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩ | ⟨b, a⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
        · exact not_inr_lt_inl hab
      · rintro ⟨⟨hab⟩ | ⟨hab⟩ | ⟨a, b⟩, hba⟩
        · exact Lex.inl (hab.lt_of_not_ge fun h => hba <| Lex.inl h)
        · exact Lex.inr (hab.lt_of_not_ge fun h => hba <| Lex.inr h)
        · exact Lex.sep _ _ }

theorem toLex_mono : Monotone (@toLex (α ⊕ β)) := fun _ _ h => h.lex

theorem toLex_strictMono : StrictMono (@toLex (α ⊕ β)) := fun _ _ h => h.lex

theorem inl_mono : Monotone (toLex ∘ inl : α → α ⊕ₗ β) :=
  toLex_mono.comp Sum.inl_mono

theorem inr_mono : Monotone (toLex ∘ inr : β → α ⊕ₗ β) :=
  toLex_mono.comp Sum.inr_mono

theorem inl_strictMono : StrictMono (toLex ∘ inl : α → α ⊕ₗ β) :=
  toLex_strictMono.comp Sum.inl_strictMono

theorem inr_strictMono : StrictMono (toLex ∘ inr : β → α ⊕ₗ β) :=
  toLex_strictMono.comp Sum.inr_strictMono

end Preorder

instance partialOrder [PartialOrder α] [PartialOrder β] : PartialOrder (α ⊕ₗ β) :=
  { Lex.preorder with le_antisymm := fun _ _ => antisymm_of (Lex (· ≤ ·) (· ≤ ·)) }

instance linearOrder [LinearOrder α] [LinearOrder β] : LinearOrder (α ⊕ₗ β) :=
  { Lex.partialOrder with
    le_total := total_of (Lex (· ≤ ·) (· ≤ ·)),
    toDecidableLE := instDecidableRelSumLex,
    toDecidableLT := instDecidableRelSumLex,
    toDecidableEq := instDecidableEqSum }

/-- The lexicographical bottom of a sum is the bottom of the left component. -/
instance orderBot [LE α] [OrderBot α] [LE β] :
    OrderBot (α ⊕ₗ β) where
  bot := inl ⊥
  bot_le := by
    rintro (a | b)
    · exact Lex.inl bot_le
    · exact Lex.sep _ _

@[simp]
theorem inl_bot [LE α] [OrderBot α] [LE β] : toLex (inl ⊥ : α ⊕ β) = ⊥ :=
  rfl

/-- The lexicographical top of a sum is the top of the right component. -/
instance orderTop [LE α] [LE β] [OrderTop β] :
    OrderTop (α ⊕ₗ β) where
  top := inr ⊤
  le_top := by
    rintro (a | b)
    · exact Lex.sep _ _
    · exact Lex.inr le_top

@[simp]
theorem inr_top [LE α] [LE β] [OrderTop β] : toLex (inr ⊤ : α ⊕ β) = ⊤ :=
  rfl

instance boundedOrder [LE α] [LE β] [OrderBot α] [OrderTop β] : BoundedOrder (α ⊕ₗ β) :=
  { Lex.orderBot, Lex.orderTop with }

instance noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

instance noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

instance noMinOrder_of_nonempty [LT α] [LT β] [NoMinOrder α] [Nonempty α] : NoMinOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr _ => ⟨toLex (inl <| Classical.arbitrary α), inl_lt_inr _ _⟩⟩

instance noMaxOrder_of_nonempty [LT α] [LT β] [NoMaxOrder β] [Nonempty β] : NoMaxOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl _ => ⟨toLex (inr <| Classical.arbitrary β), inl_lt_inr _ _⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

instance denselyOrdered_of_noMaxOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMaxOrder α] : DenselyOrdered (α ⊕ₗ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl a, inr _, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_gt a
      ⟨toLex (inl c), inl_lt_inl_iff.2 h, inl_lt_inr _ _⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

instance denselyOrdered_of_noMinOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMinOrder β] : DenselyOrdered (α ⊕ₗ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl _, inr b, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_lt b
      ⟨toLex (inr c), inl_lt_inr _ _, inr_lt_inr_iff.2 h⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

end Lex

end Sum

/-! ### Order isomorphisms -/


open OrderDual Sum

namespace OrderIso

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*} [LE α] [LE β] [LE γ]
  [LE α₁] [LE α₂] [LE β₁] [LE β₂] [LE γ₁] [LE γ₂] (a : α) (b : β) (c : γ)

/-- `Equiv.sumCongr` promoted to an order isomorphism. -/
@[simps! apply]
def sumCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ ⊕ β₁ ≃o α₂ ⊕ β₂ where
  toEquiv := .sumCongr ea eb
  map_rel_iff' := by aesop

@[simp]
theorem sumCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂) :
    (e₁.sumCongr e₂).trans (f₁.sumCongr f₂) = (e₁.trans f₁).sumCongr (e₂.trans f₂) := by
  ext; simp

@[simp]
theorem sumCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) :
    (ea.sumCongr eb).symm = ea.symm.sumCongr eb.symm :=
  rfl

@[simp]
theorem sumCongr_refl : sumCongr (.refl α) (.refl β) = .refl _ := by
  ext; simp

/-- `Equiv.sumComm` promoted to an order isomorphism. -/
@[simps! apply]
def sumComm (α β : Type*) [LE α] [LE β] : α ⊕ β ≃o β ⊕ α :=
  { Equiv.sumComm α β with map_rel_iff' := swap_le_swap_iff }

@[simp]
theorem sumComm_symm (α β : Type*) [LE α] [LE β] :
    (OrderIso.sumComm α β).symm = OrderIso.sumComm β α :=
  rfl

/-- `Equiv.sumAssoc` promoted to an order isomorphism. -/
def sumAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α ⊕ β) ⊕ γ ≃o α ⊕ (β ⊕ γ) :=
  { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} => by
      rcases a with ((_ | _) | _) <;> rcases b with ((_ | _) | _) <;>
      simp [Equiv.sumAssoc] }

@[simp]
theorem sumAssoc_apply_inl_inl : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
theorem sumAssoc_apply_inl_inr : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
theorem sumAssoc_apply_inr : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl

@[simp]
theorem sumAssoc_symm_apply_inl : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
theorem sumAssoc_symm_apply_inr_inl : (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
theorem sumAssoc_symm_apply_inr_inr : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- `orderDual` is distributive over `⊕` up to an order isomorphism. -/
def sumDualDistrib (α β : Type*) [LE α] [LE β] : (α ⊕ β)ᵒᵈ ≃o αᵒᵈ ⊕ βᵒᵈ :=
  { Equiv.refl _ with
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · change inl (toDual a) ≤ inl (toDual b) ↔ toDual (inl a) ≤ toDual (inl b)
        simp [toDual_le_toDual, inl_le_inl_iff]
      · exact iff_of_false (@not_inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _) not_inr_le_inl
      · exact iff_of_false (@not_inr_le_inl (OrderDual α) (OrderDual β) _ _ _ _) not_inl_le_inr
      · change inr (toDual a) ≤ inr (toDual b) ↔ toDual (inr a) ≤ toDual (inr b)
        simp [toDual_le_toDual, inr_le_inr_iff] }

@[simp]
theorem sumDualDistrib_inl : sumDualDistrib α β (toDual (inl a)) = inl (toDual a) :=
  rfl

@[simp]
theorem sumDualDistrib_inr : sumDualDistrib α β (toDual (inr b)) = inr (toDual b) :=
  rfl

@[simp]
theorem sumDualDistrib_symm_inl : (sumDualDistrib α β).symm (inl (toDual a)) = toDual (inl a) :=
  rfl

@[simp]
theorem sumDualDistrib_symm_inr : (sumDualDistrib α β).symm (inr (toDual b)) = toDual (inr b) :=
  rfl

/-- `Equiv.sumCongr` promoted to an order isomorphism between lexicographic sums. -/
@[simps! apply]
def sumLexCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ ⊕ₗ β₁ ≃o α₂ ⊕ₗ β₂ where
  toEquiv := ofLex.trans ((Equiv.sumCongr ea eb).trans toLex)
  map_rel_iff' := by simp_rw [Lex.forall]; rintro (a | a) (b | b) <;> simp

@[simp]
theorem sumLexCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂) :
    (e₁.sumLexCongr e₂).trans (f₁.sumLexCongr f₂) = (e₁.trans f₁).sumLexCongr (e₂.trans f₂) := by
  ext; simp

@[simp]
theorem sumLexCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) :
    (ea.sumLexCongr eb).symm = ea.symm.sumLexCongr eb.symm :=
  rfl

@[simp]
theorem sumLexCongr_refl : sumLexCongr (.refl α) (.refl β) = .refl _ := by
  ext; simp

/-- `Equiv.sumAssoc` promoted to an order isomorphism. -/
def sumLexAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α ⊕ₗ β) ⊕ₗ γ ≃o α ⊕ₗ β ⊕ₗ γ :=
  { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} =>
      ⟨fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl h => Lex.inl <| Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.sep _ _ => Lex.inl <| Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
        | inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inr (Lex.inl h) => Lex.inl <| Lex.inr h
        | inlₗ (inrₗ _), inrₗ _, Lex.inr (Lex.sep _ _) => Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr (Lex.inr h) => Lex.inr h,
        fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl (Lex.inl h) => Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.inl (Lex.sep _ _) => Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
        | inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inl (Lex.inr h) => Lex.inr <| Lex.inl h
        | inlₗ (inrₗ _), inrₗ _, Lex.sep _ _ => Lex.inr <| Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr h => Lex.inr <| Lex.inr h⟩ }

@[simp]
theorem sumLexAssoc_apply_inl_inl :
    sumLexAssoc α β γ (toLex <| inl <| toLex <| inl a) = toLex (inl a) :=
  rfl

@[simp]
theorem sumLexAssoc_apply_inl_inr :
    sumLexAssoc α β γ (toLex <| inl <| toLex <| inr b) = toLex (inr <| toLex <| inl b) :=
  rfl

@[simp]
theorem sumLexAssoc_apply_inr :
    sumLexAssoc α β γ (toLex <| inr c) = toLex (inr <| toLex <| inr c) :=
  rfl

@[simp]
theorem sumLexAssoc_symm_apply_inl : (sumLexAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
theorem sumLexAssoc_symm_apply_inr_inl : (sumLexAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
theorem sumLexAssoc_symm_apply_inr_inr : (sumLexAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- `OrderDual` is antidistributive over `⊕ₗ` up to an order isomorphism. -/
def sumLexDualAntidistrib (α β : Type*) [LE α] [LE β] : (α ⊕ₗ β)ᵒᵈ ≃o βᵒᵈ ⊕ₗ αᵒᵈ :=
  { Equiv.sumComm α β with
    map_rel_iff' := fun {a b} => by
      rcases a with (a | a) <;> rcases b with (b | b)
      · simp
        change
          toLex (inr <| toDual a) ≤ toLex (inr <| toDual b) ↔
            toDual (toLex <| inl a) ≤ toDual (toLex <| inl b)
        simp [toDual_le_toDual]
      · exact iff_of_false (@Lex.not_inr_le_inl (OrderDual β) (OrderDual α) _ _ _ _)
          Lex.not_inr_le_inl
      · exact iff_of_true (@Lex.inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _)
          (Lex.inl_le_inr _ _)
      · change
          toLex (inl <| toDual a) ≤ toLex (inl <| toDual b) ↔
            toDual (toLex <| inr a) ≤ toDual (toLex <| inr b)
        simp [toDual_le_toDual] }

@[simp]
theorem sumLexDualAntidistrib_inl :
    sumLexDualAntidistrib α β (toDual (inl a)) = inr (toDual a) :=
  rfl

@[simp]
theorem sumLexDualAntidistrib_inr :
    sumLexDualAntidistrib α β (toDual (inr b)) = inl (toDual b) :=
  rfl

@[simp]
theorem sumLexDualAntidistrib_symm_inl :
    (sumLexDualAntidistrib α β).symm (inl (toDual b)) = toDual (inr b) :=
  rfl

@[simp]
theorem sumLexDualAntidistrib_symm_inr :
    (sumLexDualAntidistrib α β).symm (inr (toDual a)) = toDual (inl a) :=
  rfl

end OrderIso

variable [LE α]

namespace WithBot

/-- `WithBot α` is order-isomorphic to `PUnit ⊕ₗ α`, by sending `⊥` to `Unit` and `↑a` to
`a`. -/
def orderIsoPUnitSumLex : WithBot α ≃o PUnit ⊕ₗ α :=
  ⟨(Equiv.optionEquivSumPUnit α).trans <| (Equiv.sumComm _ _).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Equiv.sumComm_apply, swap, Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [elim_inr, lex_inl_inl, bot_le]
    · simp only [elim_inr, elim_inl, Lex.sep, bot_le]
    · simp only [elim_inl, elim_inr, lex_inr_inl, false_iff]
      exact not_coe_le_bot _
    · simp only [elim_inl, lex_inr_inr, coe_le_coe]
  ⟩

@[simp]
theorem orderIsoPUnitSumLex_bot : @orderIsoPUnitSumLex α _ ⊥ = toLex (inl PUnit.unit) :=
  rfl

@[simp]
theorem orderIsoPUnitSumLex_toLex (a : α) : orderIsoPUnitSumLex ↑a = toLex (inr a) :=
  rfl

@[simp]
theorem orderIsoPUnitSumLex_symm_inl (x : PUnit) :
    (@orderIsoPUnitSumLex α _).symm (toLex <| inl x) = ⊥ :=
  rfl

@[simp]
theorem orderIsoPUnitSumLex_symm_inr (a : α) : orderIsoPUnitSumLex.symm (toLex <| inr a) = a :=
  rfl

end WithBot

namespace WithTop

/-- `WithTop α` is order-isomorphic to `α ⊕ₗ PUnit`, by sending `⊤` to `Unit` and `↑a` to
`a`. -/
def orderIsoSumLexPUnit : WithTop α ≃o α ⊕ₗ PUnit :=
  ⟨(Equiv.optionEquivSumPUnit α).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [lex_inr_inr, le_top]
    · simp only [lex_inr_inl, false_iff]
      exact not_top_le_coe _
    · simp only [Lex.sep, le_top]
    · simp only [lex_inl_inl, coe_le_coe]⟩

@[simp]
theorem orderIsoSumLexPUnit_top : @orderIsoSumLexPUnit α _ ⊤ = toLex (inr PUnit.unit) :=
  rfl

@[simp]
theorem orderIsoSumLexPUnit_toLex (a : α) : orderIsoSumLexPUnit ↑a = toLex (inl a) :=
  rfl

@[simp]
theorem orderIsoSumLexPUnit_symm_inr (x : PUnit) :
    (@orderIsoSumLexPUnit α _).symm (toLex <| inr x) = ⊤ :=
  rfl

@[simp]
theorem orderIsoSumLexPUnit_symm_inl (a : α) : orderIsoSumLexPUnit.symm (toLex <| inl a) = a :=
  rfl

end WithTop
