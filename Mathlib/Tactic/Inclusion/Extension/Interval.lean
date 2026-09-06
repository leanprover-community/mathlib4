/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Ring.Defs
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

/-- Multiply two finite or infinite interval bounds. -/
def Interval.mulBound [Mul α] [Zero α] [DecidableEq α] :
    Option α → Option α → Option α
  | some a, some b => some (a * b)
  | some a, none => if a = 0 then some 0 else none
  | none, some b => if b = 0 then some 0 else none
  | none, none => none

-- `WithBot α` and `WithTop α` are definitionally `Option α`, so `mulBound` handles both.
/-- Multiply two intervals. -/
def Interval.mul [Mul α] [Zero α] [LinearOrder α] (I J : Interval α) : Interval α :=
  if 0 ≤ I.lb then
    if 0 ≤ J.lb then
      ⟨Interval.mulBound I.lb J.lb, Interval.mulBound I.ub J.ub⟩
    else if J.ub ≤ 0 then
      ⟨Interval.mulBound I.ub J.lb, Interval.mulBound I.lb J.ub⟩
    else
      ⟨Interval.mulBound I.ub J.lb, Interval.mulBound I.ub J.ub⟩
  else if I.ub ≤ 0 then
    if 0 ≤ J.lb then
      ⟨Interval.mulBound I.lb J.ub, Interval.mulBound I.ub J.lb⟩
    else if J.ub ≤ 0 then
      ⟨Interval.mulBound I.ub J.ub, Interval.mulBound I.lb J.lb⟩
    else
      ⟨Interval.mulBound I.lb J.ub, Interval.mulBound I.lb J.lb⟩
  else
    if 0 ≤ J.lb then
      ⟨Interval.mulBound I.lb J.ub, Interval.mulBound I.ub J.ub⟩
    else if J.ub ≤ 0 then
      ⟨Interval.mulBound I.ub J.lb, Interval.mulBound I.lb J.lb⟩
    else
      ⟨min (Interval.mulBound I.lb J.ub) (Interval.mulBound I.ub J.lb),
        max (Interval.mulBound I.lb J.lb) (Interval.mulBound I.ub J.ub)⟩

private theorem map_mulBound_le [Mul α] [Zero α] [DecidableEq α] [Preorder β]
    (f : α → β) (a b : Option α) {z : β}
    (hmul : ∀ x y, a = some x → b = some y → f (x * y) ≤ z)
    (hzero : (a = none ∧ b = some 0 ∨ a = some 0 ∧ b = none) → f 0 ≤ z) :
    WithBot.map f (Interval.mulBound a b : WithBot α) ≤ z := by
  rcases a with _ | a <;> rcases b with _ | b <;>
    simp only [Interval.mulBound] <;> try split_ifs
  all_goals first | exact bot_le | apply WithBot.coe_le_coe.mpr
  all_goals first
    | exact hzero (by simp_all [WithBot.none_eq_bot]; rfl)
    | exact hmul _ _ rfl rfl

private theorem le_map_mulBound [Mul α] [Zero α] [DecidableEq α] [Preorder β]
    (f : α → β) (a b : Option α) {z : β}
    (hmul : ∀ x y, a = some x → b = some y → z ≤ f (x * y))
    (hzero : (a = none ∧ b = some 0 ∨ a = some 0 ∧ b = none) → z ≤ f 0) :
    z ≤ WithTop.map f (Interval.mulBound a b : WithTop α) := by
  rcases a with _ | a <;> rcases b with _ | b <;>
    simp only [Interval.mulBound] <;> try split_ifs
  all_goals first | exact le_top | apply WithTop.coe_le_coe.mpr
  all_goals first
    | exact hzero (by simp_all [WithTop.none_eq_top]; rfl)
    | exact hmul _ _ rfl rfl

private theorem nonneg_of_mem_map [Preorder α] [Preorder β] [Zero α] [Zero β] (f : α ↪o β)
    (map_zero : f 0 = 0) {x : β} {I : Interval α} (hI : 0 ≤ I.lb)
    (hx : x ∈ I.map f) : 0 ≤ x := by
  simpa [map_zero] using (f.monotone.withBot_map hI).trans hx.1

private theorem nonpos_of_mem_map [Preorder α] [Preorder β] [Zero α] [Zero β] (f : α ↪o β)
    (map_zero : f 0 = 0) {x : β} {I : Interval α} (hI : I.ub ≤ 0)
    (hx : x ∈ I.map f) : x ≤ 0 := by
  simpa [map_zero] using hx.2.trans (f.monotone.withTop_map hI)

private theorem map_lb_le_of_eq [Preorder β] (f : α → β) {a : α} {x : β}
    {I : Interval α} (hx : x ∈ I.map f) (h : I.lb = some a) : f a ≤ x := by
  rw [Interval.map, h] at hx
  exact WithBot.coe_le_coe.mp hx.1

private theorem le_map_ub_of_eq [Preorder β] (f : α → β) {a : α} {x : β}
    {I : Interval α} (hx : x ∈ I.map f) (h : I.ub = some a) : x ≤ f a := by
  rw [Interval.map, h] at hx
  exact WithTop.coe_le_coe.mp hx.2

private theorem zero_le_map_lb_iff [LinearOrder α] [LinearOrder β] [Zero α] [Zero β]
    (f : α ↪o β) (map_zero : f 0 = 0) {a : α} {I : Interval α}
    (h : I.lb = some a) : 0 ≤ f a ↔ 0 ≤ I.lb := by
  rw [h, ← map_zero, f.le_iff_le]
  exact (WithBot.coe_le_coe (a := (0 : α)) (b := a)).symm

private theorem map_ub_le_zero_iff [LinearOrder α] [LinearOrder β] [Zero α] [Zero β]
    (f : α ↪o β) (map_zero : f 0 = 0) {a : α} {I : Interval α}
    (h : I.ub = some a) : f a ≤ 0 ↔ I.ub ≤ 0 := by
  rw [h, ← map_zero, f.le_iff_le]
  exact (WithTop.coe_le_coe (a := (0 : α)) (b := a)).symm

private theorem eq_zero_of_nonneg_of_ub_eq [PartialOrder β] [Zero α] [Zero β]
    (f : α → β) (map_zero : f 0 = 0) {x : β} {I : Interval α} (hx0 : 0 ≤ x)
    (hx : x ∈ I.map f) (h : I.ub = some 0) : x = 0 :=
  le_antisymm (by simpa [map_zero] using le_map_ub_of_eq f hx h) hx0

private theorem eq_zero_of_lb_eq_of_nonpos [PartialOrder β] [Zero α] [Zero β]
    (f : α → β) (map_zero : f 0 = 0) {x : β} {I : Interval α} (hx0 : x ≤ 0)
    (hx : x ∈ I.map f) (h : I.lb = some 0) : x = 0 :=
  le_antisymm hx0 (by simpa [map_zero] using map_lb_le_of_eq f hx h)

theorem Interval.mul_mem [Mul α] [Zero α] [LinearOrder α] [Ring β] [LinearOrder β]
    [IsStrictOrderedRing β] (f : α ↪o β) (map_zero : f 0 = 0)
    (map_mul : ∀ a b, f (a * b) = f a * f b) {x y : β} {I J : Interval α}
    (hx : x ∈ I.map f) (hy : y ∈ J.map f) : x * y ∈ (I.mul J).map f := by
  rw [Interval.mem_def]
  have hxl {a : α} (h : I.lb = some a) : f a ≤ x := map_lb_le_of_eq f hx h
  have hxu {a : α} (h : I.ub = some a) : x ≤ f a := le_map_ub_of_eq f hx h
  have hyl {a : α} (h : J.lb = some a) : f a ≤ y := map_lb_le_of_eq f hy h
  have hyu {a : α} (h : J.ub = some a) : y ≤ f a := le_map_ub_of_eq f hy h
  by_cases hIl : 0 ≤ I.lb
  · have hx0 := nonneg_of_mem_map f map_zero hIl hx
    by_cases hJl : 0 ≤ J.lb
    · have hy0 := nonneg_of_mem_map f map_zero hJl hy
      simp only [Interval.mul, hIl, hJl, ite_true]
      constructor
      · apply map_mulBound_le
        · grind [mul_le_mul, zero_le_map_lb_iff]
        · rintro (⟨ha, -⟩ | ⟨-, hb⟩)
          all_goals simp_all [WithBot.none_eq_bot]
      · apply le_map_mulBound <;>
          grind [mul_le_mul, eq_zero_of_nonneg_of_ub_eq]
    · by_cases hJu : J.ub ≤ 0
      · have hy0 := nonpos_of_mem_map f map_zero hJu hy
        simp only [Interval.mul, hIl, hJl, hJu, ite_true, ite_false]
        constructor
        · apply map_mulBound_le
          · grind [mul_le_mul_of_nonneg_of_nonpos]
          · rintro (⟨-, hb⟩ | ⟨ha, -⟩) <;>
              grind [eq_zero_of_lb_eq_of_nonpos, eq_zero_of_nonneg_of_ub_eq]
        · apply le_map_mulBound
          · grind [mul_le_mul_of_nonneg_of_nonpos, zero_le_map_lb_iff]
          · rintro (⟨ha, -⟩ | ⟨-, hb⟩)
            · simp [ha, WithBot.none_eq_bot] at hIl
            · simp [hb, WithTop.none_eq_top] at hJu
      · simp only [Interval.mul, hIl, hJl, hJu, ite_false]
        constructor
        · apply map_mulBound_le
          · grind [mul_le_mul_of_nonneg_of_nonpos, zero_le_map_lb_iff]
          · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
            · simp [hb, WithBot.some_eq_coe] at hJl
            · rw [map_zero, eq_zero_of_nonneg_of_ub_eq f map_zero hx0 hx ha, zero_mul]
        · apply le_map_mulBound
          · intro a b ha hb
            rw [map_mul]
            exact (mul_le_mul_of_nonneg_left (hyu hb) hx0).trans
              (mul_le_mul_of_nonneg_right (hxu ha)
                (le_of_not_ge <| (map_ub_le_zero_iff f map_zero hb).not.mpr hJu))
          · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
            · simp [hb, WithTop.some_eq_coe] at hJu
            · rw [map_zero, eq_zero_of_nonneg_of_ub_eq f map_zero hx0 hx ha, zero_mul]
  · by_cases hIu : I.ub ≤ 0
    · have hx0 := nonpos_of_mem_map f map_zero hIu hx
      by_cases hJl : 0 ≤ J.lb
      · have hy0 := nonneg_of_mem_map f map_zero hJl hy
        simp only [Interval.mul, hIl, hIu, hJl, ite_true, ite_false]
        constructor
        · apply map_mulBound_le
          · grind [mul_le_mul_of_nonpos_of_nonneg]
          · rintro (⟨-, hb⟩ | ⟨ha, -⟩) <;>
              grind [eq_zero_of_nonneg_of_ub_eq, eq_zero_of_lb_eq_of_nonpos]
        · apply le_map_mulBound
          · grind [mul_le_mul_of_nonpos_of_nonneg, map_ub_le_zero_iff]
          · rintro (⟨ha, -⟩ | ⟨-, hb⟩)
            · simp [ha, WithTop.none_eq_top] at hIu
            · simp [hb, WithBot.none_eq_bot] at hJl
      · by_cases hJu : J.ub ≤ 0
        · have hy0 := nonpos_of_mem_map f map_zero hJu hy
          simp only [Interval.mul, hIl, hIu, hJl, hJu, ite_true, ite_false]
          constructor
          · apply map_mulBound_le
            · grind [mul_le_mul_of_nonpos_of_nonpos', map_ub_le_zero_iff]
            · rintro (⟨ha, -⟩ | ⟨-, hb⟩)
              all_goals simp_all [WithTop.none_eq_top]
          · apply le_map_mulBound
            · grind [mul_le_mul_of_nonpos_of_nonpos]
            · rintro (⟨-, hb⟩ | ⟨ha, -⟩) <;>
                grind [eq_zero_of_lb_eq_of_nonpos]
        · simp only [Interval.mul, hIl, hIu, hJl, hJu, ite_false]
          constructor
          · apply map_mulBound_le
            · grind [mul_le_mul_of_nonpos_of_nonneg, map_ub_le_zero_iff]
            · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
              · exact (hJu (hb.symm ▸ WithTop.coe_le_coe.mpr le_rfl)).elim
              · rw [map_zero, eq_zero_of_lb_eq_of_nonpos f map_zero hx0 hx ha, zero_mul]
          · apply le_map_mulBound
            · grind [mul_le_mul_of_nonpos_of_nonpos', zero_le_map_lb_iff]
            · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
              · exact (hJl (hb.symm ▸ WithBot.coe_le_coe.mpr le_rfl)).elim
              · rw [map_zero, eq_zero_of_lb_eq_of_nonpos f map_zero hx0 hx ha, zero_mul]
    · by_cases hJl : 0 ≤ J.lb
      · have hy0 := nonneg_of_mem_map f map_zero hJl hy
        simp only [Interval.mul, hIl, hIu, hJl, ite_true, ite_false]
        constructor
        · apply map_mulBound_le
          · intro a b ha hb
            rw [map_mul]
            exact (mul_le_mul_of_nonpos_left (hyu hb)
              (le_of_not_ge <| (zero_le_map_lb_iff f map_zero ha).not.mpr hIl)).trans
                (mul_le_mul_of_nonneg_right (hxl ha) hy0)
          · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
            · rw [map_zero, eq_zero_of_nonneg_of_ub_eq f map_zero hy0 hy hb, mul_zero]
            · exact (hIl (ha.symm ▸ WithBot.coe_le_coe.mpr le_rfl)).elim
        · apply le_map_mulBound
          · grind [mul_le_mul, map_ub_le_zero_iff]
          · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
            · rw [map_zero, eq_zero_of_nonneg_of_ub_eq f map_zero hy0 hy hb, mul_zero]
            · exact (hIu (ha.symm ▸ WithTop.coe_le_coe.mpr le_rfl)).elim
      · by_cases hJu : J.ub ≤ 0
        · have hy0 := nonpos_of_mem_map f map_zero hJu hy
          simp only [Interval.mul, hIl, hIu, hJl, hJu, ite_true, ite_false]
          constructor
          · apply map_mulBound_le
            · grind [mul_le_mul_of_nonneg_of_nonpos', map_ub_le_zero_iff]
            · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
              · rw [map_zero, eq_zero_of_lb_eq_of_nonpos f map_zero hy0 hy hb, mul_zero]
              · simp [ha, WithTop.some_eq_coe] at hIu
          · apply le_map_mulBound
            · grind [mul_le_mul_of_nonpos_of_nonpos, zero_le_map_lb_iff]
            · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
              · rw [map_zero, eq_zero_of_lb_eq_of_nonpos f map_zero hy0 hy hb, mul_zero]
              · simp [ha, WithBot.some_eq_coe] at hIl
        · simp only [Interval.mul, hIl, hIu, hJl, hJu, ite_false]
          constructor
          · simp only [Interval.map]
            by_cases hy0 : 0 ≤ y
            · refine (f.monotone.withBot_map (min_le_left _ _)).trans
                (map_mulBound_le f I.lb J.ub ?_ ?_)
              · intro a b ha hb
                rw [map_mul]
                exact (mul_le_mul_of_nonpos_left (hyu hb)
                  (le_of_not_ge <| (zero_le_map_lb_iff f map_zero ha).not.mpr hIl)).trans
                    (mul_le_mul_of_nonneg_right (hxl ha) hy0)
              · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
                · simp [hb, WithTop.some_eq_coe] at hJu
                · simp [ha, WithBot.some_eq_coe] at hIl
            · refine (f.monotone.withBot_map (min_le_right _ _)).trans
                (map_mulBound_le f I.ub J.lb ?_ ?_)
              · intro a b ha hb
                rw [map_mul]
                by_cases hx0 : 0 ≤ x
                · exact mul_le_mul_of_nonneg_of_nonpos (hxu ha) (hyl hb) hx0
                    (le_of_not_ge <| (zero_le_map_lb_iff f map_zero hb).not.mpr hJl)
                · exact (mul_nonpos_of_nonneg_of_nonpos
                    (le_of_not_ge <| (map_ub_le_zero_iff f map_zero ha).not.mpr hIu)
                    (le_of_not_ge <| (zero_le_map_lb_iff f map_zero hb).not.mpr hJl)).trans
                      (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx0) (le_of_not_ge hy0))
              · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
                · simp [hb, WithBot.some_eq_coe] at hJl
                · simp [ha, WithTop.some_eq_coe] at hIu
          · simp only [Interval.map]
            by_cases hy0 : 0 ≤ y
            · refine (le_map_mulBound f I.ub J.ub ?_ ?_).trans
                (f.monotone.withTop_map (le_max_right _ _))
              · grind [mul_le_mul, map_ub_le_zero_iff]
              · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
                all_goals simp_all [WithTop.some_eq_coe]
            · refine (le_map_mulBound f I.lb J.lb ?_ ?_).trans
                (f.monotone.withTop_map (le_max_left _ _))
              · grind [mul_le_mul_of_nonpos_of_nonpos, zero_le_map_lb_iff]
              · rintro (⟨-, hb⟩ | ⟨ha, -⟩)
                all_goals simp_all [WithBot.some_eq_coe]

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
