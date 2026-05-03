/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Order.WithBot

/-!
## Interval Type for Interval Arithmetic Tactics

This file defines the `Interval` type used in the interval arithmetic tactics defined in ths folder
and develops the API necessary to support the tactic.
-/

@[expose] public section

open Set

namespace IntervalArithmetic

variable {α β : Type*}

section Bound

/-- Represents a open or closed finite lower bound of an interval. -/
structure FiniteLowerBound (α : Type*) where
  /-- If `isClosed` then the bound is considered closed, otherwise it is considered open. -/
  isClosed : Bool
  /-- The value of the finite lower bound. -/
  bound : α
  deriving DecidableEq

/-- Represents a open or closed finite upper bound of an interval. -/
structure FiniteUpperBound (α : Type*) where
  /-- If `isClosed` then the bound is considered closed, otherwise it is considered open. -/
  isClosed : Bool
  /-- The value of the finite upper bound. -/
  bound : α
  deriving DecidableEq

/-- Defines the le relation on `FiniteLowerBound`s -/
def FiniteLowerBound.le [LE α] [LT α] (lb₁ lb₂ : FiniteLowerBound α) : Prop :=
  if ! lb₁.isClosed && lb₂.isClosed then
    lb₁.bound < lb₂.bound
  else
    lb₁.bound ≤ lb₂.bound

/-- Defines the le relation on `FiniteUpperBound`s -/
def FiniteUpperBound.le [LE α] [LT α] (ub₁ ub₂ : FiniteUpperBound α) : Prop :=
  if ub₁.isClosed && !ub₂.isClosed then
    ub₁.bound < ub₂.bound
  else
    ub₁.bound ≤ ub₂.bound

/-- Defines the lt relation on `FiniteLowerBound`s -/
def FiniteLowerBound.lt [LE α] [LT α] (lb₁ lb₂ : FiniteLowerBound α) : Prop :=
  if lb₁.isClosed && !lb₂.isClosed then
    lb₁.bound ≤ lb₂.bound
  else
    lb₁.bound < lb₂.bound

/-- Defines the lt relation on `FiniteUpperBound`s -/
def FiniteUpperBound.lt [LE α] [LT α] (ub₁ ub₂ : FiniteUpperBound α) : Prop :=
  if !ub₁.isClosed && ub₂.isClosed then
    ub₁.bound ≤ ub₂.bound
  else
    ub₁.bound < ub₂.bound

instance [LE α] [LT α] : LE (FiniteLowerBound α) where
  le := FiniteLowerBound.le

instance [LE α] [LT α] : LE (FiniteUpperBound α) where
  le := FiniteUpperBound.le

instance [LE α] [LT α] : LT (FiniteLowerBound α) where
  lt := FiniteLowerBound.lt

instance [LE α] [LT α] : LT (FiniteUpperBound α) where
  lt := FiniteUpperBound.lt

instance [LE α] [LT α] [DecidableLE α] [DecidableLT α] :
  DecidableLE (FiniteLowerBound α) :=
  fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ inferInstanceAs (Decidable (if !c₁ && c₂ then a₁ < a₂ else a₁ ≤ a₂))

instance [LE α] [LT α] [DecidableLE α] [DecidableLT α] :
  DecidableLE (FiniteUpperBound α) :=
  fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ inferInstanceAs (Decidable (if c₁ && !c₂ then a₁ < a₂ else a₁ ≤ a₂))

instance [LE α] [LT α] [DecidableLE α] [DecidableLT α] :
  DecidableLT (FiniteLowerBound α) :=
  fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ inferInstanceAs (Decidable (if c₁ && !c₂ then a₁ ≤ a₂ else a₁ < a₂))

instance [LE α] [LT α] [DecidableLE α] [DecidableLT α] :
  DecidableLT (FiniteUpperBound α) :=
  fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ inferInstanceAs (Decidable (if !c₁ && c₂ then a₁ ≤ a₂ else a₁ < a₂))

instance [Preorder α] : Preorder (FiniteLowerBound α) where
  le_refl := by simp [LE.le, FiniteLowerBound.le]
  le_trans := by simp [LE.le, FiniteLowerBound.le]; grind
  lt_iff_le_not_ge := by
    simp [LE.le, LT.lt, FiniteLowerBound.le, FiniteLowerBound.lt]
    grind [lt_iff_le_not_ge]

instance [Preorder α] : Preorder (FiniteUpperBound α) where
  le_refl := by simp [LE.le, FiniteUpperBound.le]
  le_trans := by simp [LE.le, FiniteUpperBound.le]; grind
  lt_iff_le_not_ge := by
    simp [LE.le, LT.lt, FiniteUpperBound.le, FiniteUpperBound.lt]
    grind [lt_iff_le_not_ge]

instance [PartialOrder α] : PartialOrder (FiniteLowerBound α) where
  toPreorder := inferInstance
  le_antisymm := fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ by
    simp [LE.le, FiniteLowerBound.le]; cases c₁ <;> cases c₂ <;> grind

instance [PartialOrder α] : PartialOrder (FiniteUpperBound α) where
  toPreorder := inferInstance
  le_antisymm := fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ by
    simp [LE.le, FiniteUpperBound.le]; cases c₁ <;> cases c₂ <;> grind

instance [LinearOrder α] : LinearOrder (FiniteLowerBound α) where
  toPartialOrder := inferInstance
  toDecidableLE := inferInstance
  le_total := by simp [LE.le, FiniteLowerBound.le]; grind

instance [LinearOrder α] : LinearOrder (FiniteUpperBound α) where
  toPartialOrder := inferInstance
  toDecidableLE := inferInstance
  le_total := by simp [LE.le, FiniteUpperBound.le]; grind

@[simp]
theorem FiniteLowerBound.le_def [Preorder α] (lb₁ lb₂ : FiniteLowerBound α) :
    lb₁ ≤ lb₂ ↔
    if ! lb₁.isClosed && lb₂.isClosed then lb₁.bound < lb₂.bound else lb₁.bound ≤ lb₂.bound := by
  rfl

@[simp]
theorem FiniteUpperBound.le_def [Preorder α] (ub₁ ub₂ : FiniteUpperBound α) :
    ub₁ ≤ ub₂ ↔
    if ub₁.isClosed && !ub₂.isClosed then ub₁.bound < ub₂.bound else ub₁.bound ≤ ub₂.bound := by
  rfl

/-- Represents the lower bound of an interval. Can be `⊥` representing an interval unbounded
from below or an open or closed finite lower bound. -/
abbrev LowerBound (α : Type*) := WithBot (FiniteLowerBound α)

/-- Represents the upper bound of an interval. Can be `⊤` representing an interval unbounded
from above or an open or closed finite upper bound. -/
abbrev UpperBound (α : Type*) := WithTop (FiniteUpperBound α)

/-- Converts a lower bound to an upper bound. -/
def LowerBound.toUpperBound (lb : LowerBound α) : UpperBound α :=
  match lb with
  | ⊥ => ⊤
  | some ⟨c, a⟩ => some ⟨c, a⟩

/-- Converts an upper bound to a lower bound. -/
def UpperBound.toLowerBound (lb : UpperBound α) : LowerBound α :=
  match lb with
  | ⊤ => ⊥
  | some ⟨c, a⟩ => some ⟨c, a⟩

/-- Definition of a lower bound bounding an element of the target type. -/
def LowerBound.Bounds [Preorder β] (φ : α → β) (lb : LowerBound α) (b : β) : Prop :=
  match lb with
  | ⊥ => True
  | (⟨isClosed, a⟩ : FiniteLowerBound α) => if isClosed then φ a ≤ b else φ a < b

/-- Definition of a upper bound bounding an element of the target type. -/
def UpperBound.Bounds [Preorder β] (φ : α → β) (ub : UpperBound α) (b : β) : Prop :=
  match ub with
  | ⊤ => True
  | (⟨isClosed, a⟩ : FiniteUpperBound α) => if isClosed then b ≤ φ a else b < φ a

lemma LowerBound.bounds_of_bounds [PartialOrder α] [Preorder β] {φ : α → β} (hf : StrictMono φ)
    {lb₁ lb₂ : LowerBound α} (h_le : lb₁ ≤ lb₂) {b : β} (hb : lb₂.Bounds φ b) :
    lb₁.Bounds φ b := by
  match lb₁, lb₂ with
  | ⊥, _ => simp [Bounds]
  | _, ⊥ => simp [Bounds, WithBot.le_bot_iff.mp h_le]
  | (⟨c₁, a₁⟩ : FiniteLowerBound α), (⟨c₂, a₂⟩ : FiniteLowerBound α) =>
    cases c₁ <;> cases c₂ <;> simp only [Bounds, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    case false.true => have : φ a₁ < φ a₂ := hf (by simpa using h_le); grind
    all_goals (have : φ a₁ ≤ φ a₂ := hf.monotone (by simpa using h_le); grind)

lemma UpperBound.bounds_of_bounds [PartialOrder α] [Preorder β] {φ : α → β} (hf : StrictMono φ)
    {ub₁ ub₂ : UpperBound α} (h_le : ub₁ ≤ ub₂) {b : β} (hb : ub₁.Bounds φ b) :
    ub₂.Bounds φ b := by
  match ub₁, ub₂ with
  | _, ⊤ => simp [Bounds]
  | ⊤, _ => simp [Bounds, WithTop.top_le_iff.mp h_le]
  | (⟨c₁, a₁⟩ : FiniteUpperBound α), (⟨c₂, a₂⟩ : FiniteUpperBound α) =>
    cases c₁ <;> cases c₂ <;> simp only [Bounds, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    case true.false => have : φ a₁ < φ a₂ := hf (by simpa using h_le); grind
    all_goals (have : φ a₁ ≤ φ a₂ := hf.monotone (by simpa using h_le); grind)

/-- Converts a lower bound to an open lower bound. -/
def LowerBound.open (lb : LowerBound α) : LowerBound α :=
  match lb with
  | ⊥ => ⊥
  | (⟨_, a⟩ : FiniteLowerBound α) => (⟨false, a⟩ : FiniteLowerBound α)

/-- Converts an upper bound to an open upper bound. -/
def UpperBound.open (ub : UpperBound α) : UpperBound α :=
  match ub with
  | ⊤ => ⊤
  | (⟨_, a⟩ : FiniteUpperBound α) => (⟨false, a⟩ : FiniteUpperBound α)

lemma LowerBound.bounds_of_le [Preorder β] {φ : α → β} {r s : β}
  {lb : LowerBound α} (hrs : r ≤ s) (hr : lb.Bounds φ r) : lb.Bounds φ s := by
  match lb with
  | ⊥ => simp [Bounds]
  | (⟨c, a⟩ : FiniteLowerBound α) => cases c <;> simp [Bounds] at hr ⊢ <;> grind

lemma UpperBound.bounds_of_le [Preorder β] {φ : α → β} {r s : β}
  {ub : UpperBound α} (hrs : r ≤ s) (hs : ub.Bounds φ s) : ub.Bounds φ r := by
  match ub with
  | ⊤ => simp [Bounds]
  | (⟨c, a⟩ : FiniteUpperBound α) => cases c <;> simp [Bounds] at hs ⊢ <;> grind

lemma LowerBound.open_bounds_of_lt [Preorder β] {φ : α → β} {r s : β}
  {lb : LowerBound α} (hrs : r < s) (hr : lb.Bounds φ r) : lb.open.Bounds φ s := by
  match lb with
  | ⊥ => simp [Bounds, LowerBound.open]
  | (⟨c, a⟩ : FiniteLowerBound α) => cases c <;> simp [Bounds, LowerBound.open] at hr ⊢ <;> grind

lemma UpperBound.open_bounds_of_lt [Preorder β] {φ : α → β} {r s : β}
  {ub : UpperBound α} (hrs : r < s) (hs : ub.Bounds φ s) : ub.open.Bounds φ r := by
  match ub with
  | ⊤ => simp [Bounds, UpperBound.open]
  | (⟨c, a⟩ : FiniteUpperBound α) => cases c <;> simp [Bounds, UpperBound.open] at hs ⊢ <;> grind

end Bound

section Interval

/-- Represents an interval of type `α`. The bounds can be open, closed or unbounded. -/
structure Interval (α : Type*) where
  /-- Lower bound of the interval. -/
  lb : LowerBound α
  /-- Upper bound of the interval -/
  ub : UpperBound α
  deriving Inhabited, DecidableEq


/-- Interval representing `Set.univ` -/
def Interval.univ (α : Type*) : Interval α := ⟨⊥, ⊤⟩

/-- Maps an interval -/
def Interval.toSet [Preorder β] (φ : α → β) (x : Interval α) : Set β :=
  {b | x.lb.Bounds φ b ∧ x.ub.Bounds φ b}

lemma Interval.mem_toSet [Preorder β] (φ : α → β) (b : β) (x : Interval α) :
  b ∈ (x.toSet φ) ↔ x.lb.Bounds φ b ∧ x.ub.Bounds φ b := by rfl

lemma Interval.univ_eq_univ [Preorder β] (φ : α → β) : (univ α).toSet φ = .univ := by
  ext
  simp [mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.univ]

lemma Interval.mem_toSet_univ [Preorder β] (φ : α → β) (b : β) : b ∈ (univ α).toSet φ := by
  simp [univ_eq_univ]

/-- (Computable) definition of the subset relation on intervals. -/
def Interval.subset [Preorder α] (x y : Interval α) : Prop := y.lb ≤ x.lb ∧ x.ub ≤ y.ub

lemma Interval.subset_def [Preorder α] (x y : Interval α) :
    x.subset y ↔ y.lb ≤ x.lb ∧ x.ub ≤ y.ub := by
  simp [subset]

lemma mem_toSet_of_mem_toSet_le [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r ≤ s) (hr : r ∈ x.toSet φ) :
    s ∈ (⟨x.lb, ⊤⟩ : Interval α).toSet φ := by
  simp [Interval.mem_toSet, UpperBound.Bounds, LowerBound.bounds_of_le hrs hr.1]

lemma mem_toSet_of_le_mem_toSet [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r ≤ s) (hs : s ∈ x.toSet φ) :
  r ∈ (⟨⊥, x.ub⟩ : Interval α).toSet φ := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.bounds_of_le hrs hs.2]

lemma mem_toSet_of_mem_toSet_lt [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r < s) (hr : r ∈ x.toSet φ) :
  s ∈ (⟨x.lb.open, ⊤⟩ : Interval α).toSet φ := by
  simp [Interval.mem_toSet, UpperBound.Bounds, LowerBound.open_bounds_of_lt hrs hr.1]

lemma mem_toSet_of_lt_mem_toSet [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r < s) (hs : s ∈ x.toSet φ) :
  r ∈ (⟨⊥, x.ub.open⟩ : Interval α).toSet φ := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.open_bounds_of_lt hrs hs.2]

lemma Interval.subset_of_subset [PartialOrder α] [Preorder β] (φ : α → β) (hφ : StrictMono φ)
    {x y : Interval α} (hxy : x.subset y) :
    x.toSet φ ⊆ y.toSet φ := by
  intro b hb
  rw [mem_toSet] at hb ⊢
  exact ⟨LowerBound.bounds_of_bounds hφ hxy.1 hb.1, UpperBound.bounds_of_bounds hφ hxy.2 hb.2⟩

lemma mem_toSet_of_mem_toSet_eq [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r = s) (hr : r ∈ x.toSet φ) : s ∈ x.toSet φ := by
  simp [← hrs, hr]

lemma mem_toSet_of_eq_mem_toSet [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r = s) (hs : s ∈ x.toSet φ) : r ∈ x.toSet φ := by
  simp [hrs, hs]

section Inter

def Interval.inter [LinearOrder α] (x y : Interval α) : Interval α :=
  ⟨max x.lb y.lb, min x.ub y.ub⟩

theorem Interval.inter_inclusion [LinearOrder α] [Preorder β] {φ : α → β}
    {x y : Interval α} {b : β} (hbx : b ∈ x.toSet φ) (hby : b ∈ y.toSet φ) :
    b ∈ (x.inter y).toSet φ := by
  grind [mem_toSet, Interval.inter]

end Inter

section Order

/- (Computable) definition of the eq relation on Intervals. If `x.eq y` this means that
all elements of `x` are less than or equal to all elements of `y`. -/
def Interval.le [Preorder α] : Interval α → Interval α → Prop
  | ⟨_, _⟩, ⟨⊥, _⟩ => False
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => False
  | ⟨_, some ⟨_, x_ub⟩⟩, ⟨some ⟨_, y_lb⟩, _⟩ => x_ub ≤ y_lb

instance [Preorder α] [DecidableLE α]
    (x y : Interval α) : Decidable (x.le y) :=
  match x, y with
  | ⟨_, _⟩, ⟨⊥, _⟩ => isFalse id
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => isFalse id
  | ⟨_, some ⟨_, x_ub⟩⟩, ⟨some ⟨_, y_lb⟩, _⟩ => inferInstanceAs (Decidable (x_ub ≤ y_lb))

/- (Computable) definition of the lt relation on Intervals. If `x.lt y` this means that
all elements of `x` are less than all elements of `y`. -/
def Interval.lt [Preorder α] : Interval α → Interval α → Prop
  | ⟨_, _⟩, ⟨⊥, _⟩ => False
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => False
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => x_ub < y_lb
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => x_ub ≤ y_lb
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => x_ub ≤ y_lb
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => x_ub ≤ y_lb

instance [Preorder α] [DecidableLE α] [DecidableLT α]
    (x y : Interval α) : Decidable (x.lt y) :=
  match x, y with
  | ⟨_, _⟩, ⟨⊥, _⟩ => isFalse id
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => isFalse id
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => inferInstanceAs (Decidable (x_ub < y_lb))
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => inferInstanceAs (Decidable (x_ub ≤ y_lb))
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => inferInstanceAs (Decidable (x_ub ≤ y_lb))
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => inferInstanceAs (Decidable (x_ub ≤ y_lb))


lemma Interval.le_of_le [PartialOrder α] [Preorder β] {φ : α → β} (hφ : StrictMono φ) {r s : β}
    {x y : Interval α} (hrx : r ∈ x.toSet φ) (hsy : s ∈ y.toSet φ) (hxy : x.le y) :
    r ≤ s := by
  match x, y with
  | ⟨_, _⟩, ⟨⊥, _⟩ | ⟨_, ⊤⟩, ⟨some _, _⟩ => simp [le] at hxy
  | ⟨_, some ⟨x_c, x_ub⟩⟩, ⟨some ⟨y_c, y_lb⟩, _⟩ =>
    cases hx : x_c <;> cases hy : y_c
    all_goals simp [toSet, LowerBound.Bounds, UpperBound.Bounds, hx, hy] at hrx hsy hxy
    all_goals grind [hφ.monotone hxy]

lemma Interval.lt_of_lt [PartialOrder α] [Preorder β] {φ : α → β} (hφ : StrictMono φ) {r s : β}
    {x y : Interval α} (hrx : r ∈ x.toSet φ) (hsy : s ∈ y.toSet φ) (hxy : x.lt y) :
    r < s := by
  match x, y with
  | ⟨_, _⟩, ⟨⊥, _⟩ | ⟨_, ⊤⟩, ⟨some _, _⟩ => simp [lt] at hxy
  | ⟨_, some ⟨x_c,  x_ub⟩⟩, ⟨some ⟨y_c,  y_lb⟩, _⟩ =>
    cases hx : x_c <;> cases hy : y_c
    all_goals simp only [toSet, LowerBound.Bounds, UpperBound.Bounds, hx, Bool.false_eq_true,
      ↓reduceIte, mem_setOf_eq, hy, lt] at hrx hsy hxy
    case true.true => grind [hφ hxy]
    all_goals grind [hφ.monotone hxy]

/- (Computable) definition of a "strict" `eq` relation on Intervals. If `x.strict_eq y` this means
that `x` and `y` both contain exactly one equal element. -/
def Interval.strict_eq [DecidableEq α] (x y : Interval α) : Prop :=
  match x, y with
  | ⟨⊥, _⟩, _ => False
  | ⟨some _ , ⊤⟩, _ => False
  | ⟨some _, some _⟩, ⟨⊥, _⟩ => False
  | ⟨some _, some _⟩, ⟨some _, ⊤⟩ => False
  | ⟨some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩⟩, ⟨some ⟨c₃, a₃⟩, some ⟨c₄, a₄⟩⟩ =>
      if c₁ && c₂ && c₃ && c₄ && a₁ = a₂ && a₂ = a₃ && a₃ = a₄ then True else False

instance [DecidableEq α] (x y : Interval α) : Decidable (x.strict_eq y) :=
  match x, y with
  | ⟨⊥, _⟩, _ => isFalse id
  | ⟨some _, ⊤⟩, _ => isFalse id
  | ⟨some _, some _⟩, ⟨⊥, _⟩ => isFalse id
  | ⟨some _, some _⟩, ⟨some _, ⊤⟩ => isFalse id
  | ⟨some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩⟩, ⟨some ⟨c₃, a₃⟩, some ⟨c₄, a₄⟩⟩ =>
      inferInstanceAs (Decidable (
        if c₁ && c₂ && c₃ && c₄ && a₁ = a₂ && a₂ = a₃ && a₃ = a₄ then True else False))

lemma Interval.eq_of_strict_eq [LinearOrder α] [PartialOrder β] {φ : α → β} {r s : β}
    {x y : Interval α} (hrx : r ∈ x.toSet φ) (hsy : s ∈ y.toSet φ) (hxy : x.strict_eq y) :
    r = s := by
  match x, y with
  | ⟨⊥, _⟩, _ | ⟨some _, ⊤⟩, _ | ⟨some _, some _⟩, ⟨⊥, _⟩ | ⟨some _, some _⟩, ⟨some _, ⊤⟩ =>
    simp [strict_eq] at hxy
  | ⟨some ⟨x_lc, _⟩, some ⟨x_uc, _⟩⟩, ⟨some ⟨y_lc, _⟩, some ⟨y_uc, _⟩⟩ =>
      cases hx_lc : x_lc <;> cases hx_uc : x_uc <;> cases hy_lc : y_lc <;> cases hy_uc : y_uc
      all_goals simp [strict_eq, toSet, LowerBound.Bounds, UpperBound.Bounds,
        hx_lc, hx_uc, hy_lc, hy_uc] at hrx hsy hxy
      all_goals grind

end Order

instance [Repr α] : Repr (Interval α) where
  reprPrec x _ :=
    let left := match x.lb with
    | ⊥ => f!"(-∞"
    | some ⟨c, a⟩ => if c then f!"[{repr a}" else f!"({repr a}"
    let right := match x.ub with
    | ⊤ => f!"∞)"
    | some ⟨c, a⟩ => if c then f!"{repr a}]" else f!"{repr a})"
    f!"{left},{right}"

end Interval

end IntervalArithmetic
