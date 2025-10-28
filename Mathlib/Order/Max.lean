/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Order.Synonym

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `IsBot`: An element is *bottom* if all elements are greater than it.
* `IsTop`: An element is *top* if all elements are less than it.
* `IsMin`: An element is *minimal* if no element is strictly less than it.
* `IsMax`: An element is *maximal* if no element is strictly greater than it.

See also `isBot_iff_isMin` and `isTop_iff_isMax` for the equivalences in a (co)directed order.

## Typeclasses

* `NoBotOrder`: An order without bottom elements.
* `NoTopOrder`: An order without top elements.
* `NoMinOrder`: An order without minimal elements.
* `NoMaxOrder`: An order without maximal elements.
-/


open OrderDual

universe u v

variable {α β : Type*}

/-- Order without bottom elements. -/
class NoBotOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly smaller. -/
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b

/-- Order without top elements. -/
class NoTopOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly larger. -/
  exists_not_le (a : α) : ∃ b, ¬b ≤ a

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class NoMinOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly smaller `b`. -/
  exists_lt (a : α) : ∃ b, b < a

/-- Order without maximal elements. Sometimes called cofinal. -/
class NoMaxOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly greater `b`. -/
  exists_gt (a : α) : ∃ b, a < b

export NoBotOrder (exists_not_ge)

export NoTopOrder (exists_not_le)

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

instance nonempty_gt [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)

instance IsEmpty.toNoMaxOrder [LT α] [IsEmpty α] : NoMaxOrder α := ⟨isEmptyElim⟩
instance IsEmpty.toNoMinOrder [LT α] [IsEmpty α] : NoMinOrder α := ⟨isEmptyElim⟩

instance OrderDual.noBotOrder [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => exists_not_le (α := α) a⟩

instance OrderDual.noTopOrder [LE α] [NoBotOrder α] : NoTopOrder αᵒᵈ :=
  ⟨fun a => exists_not_ge (α := α) a⟩

instance OrderDual.noMinOrder [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => exists_gt (α := α) a⟩

instance OrderDual.noMaxOrder [LT α] [NoMinOrder α] : NoMaxOrder αᵒᵈ :=
  ⟨fun a => exists_lt (α := α) a⟩

-- See note [lower instance priority]
instance (priority := 100) [Preorder α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_gt⟩

-- See note [lower instance priority]
instance (priority := 100) [Preorder α] [NoMaxOrder α] : NoTopOrder α :=
  ⟨fun a => (exists_gt a).imp fun _ => not_le_of_gt⟩

instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩

instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩

instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩

instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩

instance {ι : Type u} {π : ι → Type*} [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMaxOrder (π i)] :
    NoMaxOrder (∀ i, π i) :=
  ⟨fun a => by
    classical
    obtain ⟨b, hb⟩ := exists_gt (a <| Classical.arbitrary _)
    exact ⟨_, lt_update_self_iff.2 hb⟩⟩

instance {ι : Type u} {π : ι → Type*} [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMinOrder (π i)] :
    NoMinOrder (∀ i, π i) :=
  ⟨fun a => by
    classical
    obtain ⟨b, hb⟩ := exists_lt (a <| Classical.arbitrary _)
    exact ⟨_, update_lt_self_iff.2 hb⟩⟩

theorem NoBotOrder.to_noMinOrder (α : Type*) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }

theorem NoTopOrder.to_noMaxOrder (α : Type*) [LinearOrder α] [NoTopOrder α] : NoMaxOrder α :=
  { exists_gt := fun a => by simpa [not_le] using exists_not_le a }

theorem noBotOrder_iff_noMinOrder (α : Type*) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun _ => NoBotOrder.to_noMinOrder α, fun _ => inferInstance⟩

theorem noTopOrder_iff_noMaxOrder (α : Type*) [LinearOrder α] : NoTopOrder α ↔ NoMaxOrder α :=
  ⟨fun _ => NoTopOrder.to_noMaxOrder α, fun _ => inferInstance⟩

theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn

theorem NoMaxOrder.not_acc [LT α] [NoMaxOrder α] (a : α) : ¬Acc (· > ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_gt x).recOn

section LE

variable [LE α] {a : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`NoMinOrder α` within a proof. -/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`NoMaxOrder α` within a proof. -/
def IsTop (a : α) : Prop :=
  ∀ b, b ≤ a

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `isMin_iff_forall_not_lt` does the
conversion. -/
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b

/-- `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `isMax_iff_forall_not_lt` does the
conversion. -/
def IsMax (a : α) : Prop :=
  ∀ ⦃b⦄, a ≤ b → b ≤ a

@[simp]
theorem not_isBot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
  hb <| h _

@[simp]
theorem not_isTop [NoTopOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨_, hb⟩ := exists_not_le a
  hb <| h _

protected theorem IsBot.isMin (h : IsBot a) : IsMin a := fun b _ => h b

protected theorem IsTop.isMax (h : IsTop a) : IsMax a := fun b _ => h b

theorem IsTop.isMax_iff {α} [PartialOrder α] {i j : α} (h : IsTop i) : IsMax j ↔ j = i := by
  simp_rw [le_antisymm_iff, h j, true_and]
  exact ⟨(· (h j)), Function.swap (fun _ ↦ h · |>.trans ·)⟩

theorem IsBot.isMin_iff {α} [PartialOrder α] {i j : α} (h : IsBot i) : IsMin j ↔ j = i := by
  simp_rw [le_antisymm_iff, h j, and_true]
  exact ⟨fun a ↦ a (h j), fun a h' ↦ fun _ ↦ Preorder.le_trans j i h' a (h h')⟩

@[simp]
theorem isBot_toDual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl

@[simp]
theorem isTop_toDual_iff : IsTop (toDual a) ↔ IsBot a :=
  Iff.rfl

@[simp]
theorem isMin_toDual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl

@[simp]
theorem isMax_toDual_iff : IsMax (toDual a) ↔ IsMin a :=
  Iff.rfl

@[simp]
theorem isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl

@[simp]
theorem isTop_ofDual_iff {a : αᵒᵈ} : IsTop (ofDual a) ↔ IsBot a :=
  Iff.rfl

@[simp]
theorem isMin_ofDual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl

@[simp]
theorem isMax_ofDual_iff {a : αᵒᵈ} : IsMax (ofDual a) ↔ IsMin a :=
  Iff.rfl

alias ⟨_, IsTop.toDual⟩ := isBot_toDual_iff

alias ⟨_, IsBot.toDual⟩ := isTop_toDual_iff

alias ⟨_, IsMax.toDual⟩ := isMin_toDual_iff

alias ⟨_, IsMin.toDual⟩ := isMax_toDual_iff

alias ⟨_, IsTop.ofDual⟩ := isBot_ofDual_iff

alias ⟨_, IsBot.ofDual⟩ := isTop_ofDual_iff

alias ⟨_, IsMax.ofDual⟩ := isMin_ofDual_iff

alias ⟨_, IsMin.ofDual⟩ := isMax_ofDual_iff

end LE

section Preorder

variable [Preorder α] {a b : α}

theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun _ => h.trans <| ha _

theorem IsTop.mono (ha : IsTop a) (h : a ≤ b) : IsTop b := fun _ => (ha _).trans h

theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun _ hc => h.trans <| ha <| hc.trans h

theorem IsMax.mono (ha : IsMax a) (h : a ≤ b) : IsMax b := fun _ hc => (ha <| h.trans hc).trans h

theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_ge <| h hb.le

theorem IsMax.not_lt (h : IsMax a) : ¬a < b := fun hb => hb.not_ge <| h hb.le

theorem not_isMin_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h

theorem not_isMax_of_lt (h : a < b) : ¬IsMax a := fun ha => ha.not_lt h

alias LT.lt.not_isMin := not_isMin_of_lt

alias LT.lt.not_isMax := not_isMax_of_lt

theorem isMin_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_ge hab⟩

theorem isMax_iff_forall_not_lt : IsMax a ↔ ∀ b, ¬a < b :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_ge hab⟩

@[simp]
theorem not_isMin_iff : ¬IsMin a ↔ ∃ b, b < a := by
  simp [lt_iff_le_not_ge, IsMin, not_forall]

@[simp]
theorem not_isMax_iff : ¬IsMax a ↔ ∃ b, a < b := by
  simp [lt_iff_le_not_ge, IsMax, not_forall]

@[simp]
theorem not_isMin [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_isMin_iff.2 <| exists_lt a

@[simp]
theorem not_isMax [NoMaxOrder α] (a : α) : ¬IsMax a :=
  not_isMax_iff.2 <| exists_gt a

namespace Subsingleton

variable [Subsingleton α]

protected theorem isBot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le

protected theorem isTop (a : α) : IsTop a := fun _ => (Subsingleton.elim _ _).le

protected theorem isMin (a : α) : IsMin a :=
  (Subsingleton.isBot _).isMin

protected theorem isMax (a : α) : IsMax a :=
  (Subsingleton.isTop _).isMax

end Subsingleton

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b ≤ a) : b = a :=
  h.antisymm <| ha h

protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b ≤ a) : a = b :=
  h.antisymm' <| ha h

protected theorem IsMax.eq_of_le (ha : IsMax a) (h : a ≤ b) : a = b :=
  h.antisymm <| ha h

protected theorem IsMax.eq_of_ge (ha : IsMax a) (h : a ≤ b) : b = a :=
  h.antisymm' <| ha h

protected theorem IsBot.lt_of_ne (ha : IsBot a) (h : a ≠ b) : a < b :=
  (ha b).lt_of_ne h

protected theorem IsTop.lt_of_ne (ha : IsTop a) (h : b ≠ a) : b < a :=
  (ha b).lt_of_ne h

protected theorem IsBot.not_isMax [Nontrivial α] (ha : IsBot a) : ¬ IsMax a := by
  intro ha'
  obtain ⟨b, hb⟩ := exists_ne a
  exact hb <| ha'.eq_of_ge (ha.lt_of_ne hb.symm).le

protected theorem IsTop.not_isMin [Nontrivial α] (ha : IsTop a) : ¬ IsMin a :=
  ha.toDual.not_isMax

protected theorem IsBot.not_isTop [Nontrivial α] (ha : IsBot a) : ¬ IsTop a :=
  mt IsTop.isMax ha.not_isMax

protected theorem IsTop.not_isBot [Nontrivial α] (ha : IsTop a) : ¬ IsBot a :=
  ha.toDual.not_isTop

end PartialOrder

section Prod

variable [Preorder α] [Preorder β] {a : α} {b : β} {x : α × β}

theorem IsBot.prodMk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun _ => ⟨ha _, hb _⟩

theorem IsTop.prodMk (ha : IsTop a) (hb : IsTop b) : IsTop (a, b) := fun _ => ⟨ha _, hb _⟩

theorem IsMin.prodMk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩

theorem IsMax.prodMk (ha : IsMax a) (hb : IsMax b) : IsMax (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩

theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1

theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2

theorem IsTop.fst (hx : IsTop x) : IsTop x.1 := fun c => (hx (c, x.2)).1

theorem IsTop.snd (hx : IsTop x) : IsTop x.2 := fun c => (hx (x.1, c)).2

theorem IsMin.fst (hx : IsMin x) : IsMin x.1 :=
  fun c hc => (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1

theorem IsMin.snd (hx : IsMin x) : IsMin x.2 :=
  fun c hc => (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2

theorem IsMax.fst (hx : IsMax x) : IsMax x.1 :=
  fun c hc => (hx <| show x ≤ (c, x.2) from (and_iff_left le_rfl).2 hc).1

theorem IsMax.snd (hx : IsMax x) : IsMax x.2 :=
  fun c hc => (hx <| show x ≤ (x.1, c) from (and_iff_right le_rfl).2 hc).2

theorem Prod.isBot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

theorem Prod.isTop_iff : IsTop x ↔ IsTop x.1 ∧ IsTop x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

theorem Prod.isMin_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

theorem Prod.isMax_iff : IsMax x ↔ IsMax x.1 ∧ IsMax x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

end Prod
