/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Inclusion.Core.ToSet

/-!
# (possibly unbounded) intervals

This file defines the `Interval` type for computation in the `inclusion` tactic. This
type represents a possibly unbounded interval with closed endpoints.
-/

@[expose] public section

namespace Inclusion

variable {α β : Type*}

/-- An `Interval` represents a possibly unbounded interval with closed endpoints. -/
structure Interval (α : Type*) where
  /-- The lower endpoint, or `⊥` if the interval is unbounded below. -/
  lb : WithBot α
  /-- The upper endpoint, or `⊤` if the interval is unbounded above. -/
  ub : WithTop α
  deriving Inhabited

/-- Maps `I` to `{a | I.lb ≤ a ∧ a ≤ I.ub}` -/
def Interval.toSet [Preorder α] (I : Interval α) : Set α := {a | I.lb ≤ a ∧ a ≤ I.ub}

instance [Preorder α] : ToSet (Interval α) α := ⟨Interval.toSet⟩

@[simp, grind =]
theorem Interval.mem_def [Preorder α] {x : α} {I : Interval α} :
    x ∈ I ↔ I.lb ≤ x ∧ x ≤ I.ub := Iff.rfl

/-- Apply a function to the finite endpoints of an interval. -/
def Interval.map (I : Interval α) (f : α → β) : Interval β :=
  ⟨WithBot.map f I.lb, WithTop.map f I.ub⟩

/-- The interval unbounded on both sides. -/
def Interval.univ (α : Type*) : Interval α := ⟨⊥, ⊤⟩

instance [Preorder α] : Univ (Interval α) α where
  univ := Interval.univ α
  mem_univ _ := ⟨bot_le, le_top⟩

theorem Interval.mem_map_univ [Preorder β] (f : α → β) (x : β) :
    x ∈ (Interval.univ α).map f := ⟨bot_le, le_top⟩

/-- The interval whose two endpoints are `a`. -/
def Interval.singleton (a : α) : Interval α := ⟨a, a⟩

theorem Interval.mem_map_singleton [Preorder β] (a : α) (f : α → β) :
    f a ∈ (Interval.singleton a).map f := ⟨le_rfl, le_rfl⟩

/-- The interval with lower endpoint `lb` and upper endpoint `ub`. -/
def Interval.Icc (lb : WithBot α) (ub : WithTop α) : Interval α := ⟨lb, ub⟩

theorem Interval.mem_map_Icc [Preorder β] (f : α → β) {lb ub : α} {x : β}
    (hl : f lb ≤ x) (hu : x ≤ f ub) : x ∈ (Interval.Icc lb ub).map f :=
  ⟨WithBot.coe_le_coe.mpr hl, WithTop.coe_le_coe.mpr hu⟩

theorem Interval.map_lb_le [Preorder β] (f : α → β) {lb : α} {ub : WithTop α} {x : β}
    (hx : x ∈ (Interval.Icc lb ub).map f) : f lb ≤ x :=
  WithBot.coe_le_coe.mp hx.1

theorem Interval.le_map_ub [Preorder β] (f : α → β) {lb : WithBot α} {ub : α} {x : β}
    (hx : x ∈ (Interval.Icc lb ub).map f) : x ≤ f ub :=
  WithTop.coe_le_coe.mp hx.2

/-- The interval unbounded below with upper endpoint `ub`. -/
def Interval.Iic (ub : WithTop α) : Interval α := ⟨⊥, ub⟩

/-- The interval unbounded above with lower endpoint `lb`. -/
def Interval.Ici (lb : WithBot α) : Interval α := ⟨lb, ⊤⟩

theorem Interval.mem_Iic_of_le [Preorder α] {x y : α} {I : Interval α}
    (hxy : x ≤ y) (hy : y ∈ I) : x ∈ Interval.Iic I.ub := by
  grind [Iic, bot_le, WithTop.coe_le_coe.mpr hxy]

theorem Interval.mem_Ici_of_le [Preorder α] {x y : α} {I : Interval α}
    (hxy : x ≤ y) (hx : x ∈ I) : y ∈ Interval.Ici I.lb := by
  grind [Ici, le_top, WithBot.coe_le_coe.mpr hxy]

theorem Interval.mem_Icc_of_le [Preorder α] {a b x : α} {I J : Interval α}
    (ha : a ∈ I) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ∈ J) :
    x ∈ Interval.Icc I.lb J.ub := by
  grind [Icc, WithBot.coe_le_coe.mpr hax, WithTop.coe_le_coe.mpr hxb]

theorem Interval.mem_Iic_of_lt [Preorder α] {x y : α} {I : Interval α}
    (hxy : x < y) (hy : y ∈ I) : x ∈ Interval.Iic I.ub :=
  Interval.mem_Iic_of_le hxy.le hy

theorem Interval.mem_Ici_of_lt [Preorder α] {x y : α} {I : Interval α}
    (hxy : x < y) (hx : x ∈ I) : y ∈ Interval.Ici I.lb :=
  Interval.mem_Ici_of_le hxy.le hx

theorem Interval.mem_Ici_of_mem_Ici [Preorder α] {a x : α} {I : Interval α}
    (hx : x ∈ Set.Ici a) (ha : a ∈ I) : x ∈ Interval.Ici I.lb :=
  Interval.mem_Ici_of_le hx ha

theorem Interval.mem_Ici_of_mem_Ioi [Preorder α] {a x : α} {I : Interval α}
    (hx : x ∈ Set.Ioi a) (ha : a ∈ I) : x ∈ Interval.Ici I.lb :=
  Interval.mem_Ici_of_le hx.le ha

theorem Interval.mem_Iic_of_mem_Iic [Preorder α] {b x : α} {I : Interval α}
    (hx : x ∈ Set.Iic b) (hb : b ∈ I) : x ∈ Interval.Iic I.ub :=
  Interval.mem_Iic_of_le hx hb

theorem Interval.mem_Iic_of_mem_Iio [Preorder α] {b x : α} {I : Interval α}
    (hx : x ∈ Set.Iio b) (hb : b ∈ I) : x ∈ Interval.Iic I.ub :=
  Interval.mem_Iic_of_le hx.le hb

theorem Interval.mem_Icc_of_mem_Ico [Preorder α] {a b x : α} {I J : Interval α}
    (hx : x ∈ Set.Ico a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_le ha hx.1 hx.2.le hb

theorem Interval.mem_Icc_of_mem_Ioc [Preorder α] {a b x : α} {I J : Interval α}
    (hx : x ∈ Set.Ioc a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_le ha hx.1.le hx.2 hb

theorem Interval.mem_Icc_of_mem_Icc [Preorder α] {a b x : α} {I J : Interval α}
    (hx : x ∈ Set.Icc a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_le ha hx.1 hx.2 hb

theorem Interval.mem_Icc_of_mem_Ioo [Preorder α] {a b x : α} {I J : Interval α}
    (hx : x ∈ Set.Ioo a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_le ha hx.1.le hx.2.le hb

/-- The intersection of two intervals. -/
def Interval.inter [LinearOrder α] (I J : Interval α) : Interval α :=
  ⟨max I.lb J.lb, min I.ub J.ub⟩

instance [LinearOrder α] : Refine (Interval α) α where
  refine := Interval.inter
  mem_refine hs ht := ⟨max_le hs.1 ht.1, le_min hs.2 ht.2⟩

theorem Interval.map_inter [LinearOrder α] [LinearOrder β] (f : α ↪o β) (I J : Interval α) :
    (I.inter J).map f = (I.map f).inter (J.map f) := by
  simp [f.monotone.withBot_map.map_max, f.monotone.withTop_map.map_min,
    Interval.inter, Interval.map]

theorem Interval.inter_mem [LinearOrder α] [LinearOrder β] (f : α ↪o β)
    {x : β} {I J : Interval α} (hxI : x ∈ I.map f) (hxJ : x ∈ J.map f) :
    x ∈ (I.inter J).map f := by
  rw [Interval.map_inter]
  exact Refine.mem_refine hxI hxJ

/-- The convex hull of two intervals. -/
def Interval.hull [LinearOrder α] (I J : Interval α) : Interval α :=
  ⟨min I.lb J.lb, max I.ub J.ub⟩

theorem Interval.mem_hull_left [LinearOrder α] {x : α} {I J : Interval α} (hx : x ∈ I) :
    x ∈ I.hull J := by
  grind [Interval.hull]

theorem Interval.mem_hull_right [LinearOrder α] {x : α} {I J : Interval α} (hx : x ∈ J) :
    x ∈ I.hull J := by
  grind [Interval.hull]

instance [LinearOrder α] : Coarsen (Interval α) α where
  coarsen := Interval.hull
  mem_coarsen_left := Interval.mem_hull_left
  mem_coarsen_right := Interval.mem_hull_right

theorem Interval.map_hull [LinearOrder α] [LinearOrder β] (f : α ↪o β) (I J : Interval α) :
    (I.hull J).map f = (I.map f).hull (J.map f) := by
  simp [f.monotone.withBot_map.map_min, f.monotone.withTop_map.map_max,
    Interval.hull, Interval.map]

theorem Interval.hull_mem_left [LinearOrder α] [LinearOrder β] (f : α ↪o β)
    {x : β} {I J : Interval α} (hx : x ∈ I.map f) : x ∈ (I.hull J).map f := by
  rw [Interval.map_hull]
  exact Interval.mem_hull_left hx

theorem Interval.hull_mem_right [LinearOrder α] [LinearOrder β] (f : α ↪o β)
    {x : β} {I J : Interval α} (hx : x ∈ J.map f) : x ∈ (I.hull J).map f := by
  rw [Interval.map_hull]
  exact Interval.mem_hull_right hx

/-- Add two intervals. -/
def Interval.add [Add α] (I J : Interval α) : Interval α where
  lb := match I.lb, J.lb with
    | some a, some b => some (a + b)
    | _, _ => ⊥
  ub := match I.ub, J.ub with
    | some a, some b => some (a + b)
    | _, _ => ⊤

@[simp]
theorem Interval.add_lb [AddZero α] (I J : Interval α) : (I.add J).lb = I.lb + J.lb := by
  rcases I with ⟨_ | il, iu⟩ <;> rcases J with ⟨_ | jl, ju⟩ <;> rfl

@[simp]
theorem Interval.add_ub [AddZero α] (I J : Interval α) : (I.add J).ub = I.ub + J.ub := by
  rcases I with ⟨il, _ | iu⟩ <;> rcases J with ⟨jl, _ | ju⟩ <;> rfl

theorem Interval.add_mem [AddZero α] [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    (f : α →+ β) {x y : β} {I J : Interval α} (hx : x ∈ I.map f) (hy : y ∈ J.map f) :
    x + y ∈ (I.add J).map f := by
  constructor
  · simpa [Interval.map] using add_le_add hx.1 hy.1
  · simpa [Interval.map] using add_le_add hx.2 hy.2

/-- Negate an interval. -/
def Interval.neg [Neg α] (I : Interval α) : Interval α where
  lb := match I.ub with
    | some a => some (-a)
    | ⊤ => ⊥
  ub := match I.lb with
    | some a => some (-a)
    | ⊥ => ⊤

theorem Interval.neg_mem [AddGroup α] [AddCommGroup β] [Preorder β] [IsOrderedAddMonoid β]
    (f : α →+ β) {x : β} {I : Interval α} (hx : x ∈ I.map f) : -x ∈ I.neg.map f := by
  constructor
  · rcases I with ⟨il, _ | iu⟩
    · simp [Interval.neg, Interval.map]
    apply WithBot.coe_le_coe.mpr
    simpa using neg_le_neg_iff.mpr (WithTop.coe_le_coe.mp hx.2)
  · rcases I with ⟨_ | il, iu⟩
    · simp [Interval.neg, Interval.map]
    apply WithTop.coe_le_coe.mpr
    simpa using neg_le_neg_iff.mpr (WithBot.coe_le_coe.mp hx.1)

/-- Subtract one interval from another. -/
def Interval.sub [Sub α] (I J : Interval α) : Interval α where
  lb := match I.lb, J.ub with
    | some a, some b => some (a - b)
    | _, _ => ⊥
  ub := match I.ub, J.lb with
    | some a, some b => some (a - b)
    | _, _ => ⊤

theorem Interval.sub_eq_add_neg [AddGroup α] (I J : Interval α) : I.sub J = I.add J.neg := by
  rcases I with ⟨_ | il, _ | iu⟩ <;>
    rcases J with ⟨_ | jl, _ | ju⟩ <;>
      simp [Interval.sub, Interval.add, Interval.neg, _root_.sub_eq_add_neg]

theorem Interval.sub_mem [AddGroup α] [AddCommGroup β] [Preorder β] [IsOrderedAddMonoid β]
    (f : α →+ β) {x y : β} {I J : Interval α}
    (hx : x ∈ I.map f) (hy : y ∈ J.map f) : x - y ∈ (I.sub J).map f := by
  rw [_root_.sub_eq_add_neg, Interval.sub_eq_add_neg]
  exact Interval.add_mem f hx (Interval.neg_mem f hy)

/-- Check if `r x y` is false is implied by `x ∈ I` and `y ∈ J` -/
def Interval.orderRelFalse (r : α → α → Prop) [DecidableRel r]
    (I J : Interval α) : IntervalBool :=
  match I.lb, J.ub with
  | some il, some ju => if r il ju then .undetermined else .false
  | _, _ => .undetermined

theorem Interval.orderRelFalse_mem [Preorder β] {r : α → α → Prop} {s : β → β → Prop}
    [DecidableRel r] [Trans (· ≤ ·) s s] [Trans s (· ≤ ·) s] (f : r ↪r s)
    {x y : β} {I J : Interval α} (hx : x ∈ I.map f) (hy : y ∈ J.map f) :
    s x y ∈ Interval.orderRelFalse r I J := by
  rcases I with ⟨_ | il, iu⟩
  · simp [Interval.orderRelFalse]
  rcases J with ⟨jl, _ | ju⟩
  · simp [Interval.orderRelFalse]
  dsimp [Interval.orderRelFalse]
  split_ifs with h
  · simp
  · exact IntervalBool.mem_false fun hxy ↦ h <| f.map_rel_iff.mp <|
      trans (Interval.map_lb_le f hx) (trans hxy (Interval.le_map_ub f hy))

/-- Check if `r x y` is implied (true or false) by `x ∈ I` and `y ∈ J`. -/
def Interval.orderRel (r : α → α → Prop) [DecidableRel r]
    (I J : Interval α) : IntervalBool :=
  match I.ub, J.lb with
  | some iu, some jl =>
      if r iu jl then
        .true
      else
        Interval.orderRelFalse r I J
  | _, _ => Interval.orderRelFalse r I J

theorem Interval.orderRel_mem [Preorder β] {r : α → α → Prop} {s : β → β → Prop}
    [DecidableRel r] [Trans (· ≤ ·) s s] [Trans s (· ≤ ·) s] (f : r ↪r s)
    {x y : β} {I J : Interval α} (hx : x ∈ I.map f) (hy : y ∈ J.map f) :
    s x y ∈ Interval.orderRel r I J := by
  have hFalse := Interval.orderRelFalse_mem f hx hy
  rcases I with ⟨il, _ | iu⟩
  · exact hFalse
  rcases J with ⟨_ | jl, ju⟩
  · exact hFalse
  dsimp [Interval.orderRel]
  split_ifs with h
  · apply IntervalBool.mem_true
    exact trans (Interval.le_map_ub f hx) <| trans (f.map_rel_iff.mpr h) (Interval.map_lb_le f hy)
  · exact hFalse

/-- Check if `x ≤ y` is implied (true or false) by `x ∈ I` and `y ∈ J` -/
def Interval.le [LE α] [DecidableLE α] (I J : Interval α) : IntervalBool :=
  match I.ub, J.lb with
  | some iu, some jl =>
      if iu ≤ jl then .true
      else
        match I.lb, J.ub with
        | some il, some ju => if il ≤ ju then .undetermined else .false
        | _, _ => .undetermined
  | _, _ =>
      match I.lb, J.ub with
      | some il, some ju => if il ≤ ju then .undetermined else .false
      | _, _ => .undetermined

theorem Interval.le_mem [Preorder α] [Preorder β] [DecidableLE α] (f : α ↪o β)
    {x y : β} {I J : Interval α} (hx : x ∈ I.map f) (hy : y ∈ J.map f) :
    (x ≤ y) ∈ I.le J :=
  Interval.orderRel_mem f hx hy

/-- Check if `x < y` is implied (true or false) by `x ∈ I` and `y ∈ J`. -/
def Interval.lt [LT α] [DecidableLT α] (I J : Interval α) : IntervalBool :=
  match I.ub, J.lb with
  | some iu, some jl =>
      if iu < jl then .true
      else
        match I.lb, J.ub with
        | some il, some ju => if il < ju then .undetermined else .false
        | _, _ => .undetermined
  | _, _ =>
      match I.lb, J.ub with
      | some il, some ju => if il < ju then .undetermined else .false
      | _, _ => .undetermined

theorem Interval.lt_mem [Preorder α] [Preorder β] [DecidableLT α] (f : α ↪o β)
    {x y : β} {I J : Interval α} (hx : x ∈ I.map f) (hy : y ∈ J.map f) :
    (x < y) ∈ I.lt J :=
  Interval.orderRel_mem f.ltEmbedding hx hy

/-- Check if `x = y` is implied (true or false) by `x ∈ I` and `y ∈ J`. -/
def Interval.eq [LE α] [DecidableLE α] (I J : Interval α) : IntervalBool :=
  (I.le J).and (J.le I)

theorem Interval.eq_mem [Preorder α] [PartialOrder β] [DecidableLE α] (f : α ↪o β)
    {x y : β} {I J : Interval α} (hx : x ∈ I.map f) (hy : y ∈ J.map f) :
    (x = y) ∈ I.eq J := by
  apply ToSet.mem_of_eq_of_mem (propext le_antisymm_iff)
  exact IntervalBool.and_mem (Interval.le_mem f hx hy) (Interval.le_mem f hy hx)

theorem Interval.mem_Ici [Preorder α] [Preorder β] [DecidableLE α] (f : α ↪o β)
    {a x : β} {I J : Interval α} (ha : a ∈ I.map f) (hx : x ∈ J.map f) :
    (x ∈ Set.Ici a) ∈ I.le J := Interval.le_mem f ha hx

theorem Interval.mem_Ioi [Preorder α] [Preorder β] [DecidableLT α] (f : α ↪o β)
    {a x : β} {I J : Interval α} (ha : a ∈ I.map f) (hx : x ∈ J.map f) :
    (x ∈ Set.Ioi a) ∈ I.lt J := Interval.lt_mem f ha hx

theorem Interval.mem_Iic [Preorder α] [Preorder β] [DecidableLE α] (f : α ↪o β)
    {b x : β} {I J : Interval α} (hx : x ∈ I.map f) (hb : b ∈ J.map f) :
    (x ∈ Set.Iic b) ∈ I.le J := Interval.le_mem f hx hb

theorem Interval.mem_Iio [Preorder α] [Preorder β] [DecidableLT α] (f : α ↪o β)
    {b x : β} {I J : Interval α} (hx : x ∈ I.map f) (hb : b ∈ J.map f) :
    (x ∈ Set.Iio b) ∈ I.lt J := Interval.lt_mem f hx hb

theorem Interval.mem_Icc [Preorder α] [Preorder β] [DecidableLE α] (f : α ↪o β)
    {a b x : β} {I J K : Interval α}
    (ha : a ∈ I.map f) (hx : x ∈ J.map f) (hb : b ∈ K.map f) :
    (x ∈ Set.Icc a b) ∈ (I.le J).and (J.le K) :=
  IntervalBool.and_mem (Interval.le_mem f ha hx) (Interval.le_mem f hx hb)

theorem Interval.mem_Ico [Preorder α] [Preorder β] [DecidableLE α] [DecidableLT α]
    (f : α ↪o β) {a b x : β} {I J K : Interval α}
    (ha : a ∈ I.map f) (hx : x ∈ J.map f) (hb : b ∈ K.map f) :
    (x ∈ Set.Ico a b) ∈ (I.le J).and (J.lt K) :=
  IntervalBool.and_mem (Interval.le_mem f ha hx) (Interval.lt_mem f hx hb)

theorem Interval.mem_Ioc [Preorder α] [Preorder β] [DecidableLE α] [DecidableLT α]
    (f : α ↪o β) {a b x : β} {I J K : Interval α}
    (ha : a ∈ I.map f) (hx : x ∈ J.map f) (hb : b ∈ K.map f) :
    (x ∈ Set.Ioc a b) ∈ (I.lt J).and (J.le K) :=
  IntervalBool.and_mem (Interval.lt_mem f ha hx) (Interval.le_mem f hx hb)

theorem Interval.mem_Ioo [Preorder α] [Preorder β] [DecidableLT α] (f : α ↪o β)
    {a b x : β} {I J K : Interval α} (ha : a ∈ I.map f) (hx : x ∈ J.map f)
    (hb : b ∈ K.map f) : (x ∈ Set.Ioo a b) ∈ (I.lt J).and (J.lt K) :=
  IntervalBool.and_mem (Interval.lt_mem f ha hx) (Interval.lt_mem f hx hb)

end Inclusion
