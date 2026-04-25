module

import Mathlib.Order.TypeTags
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.WithBot
public import Mathlib.Data.List.Basic

set_option linter.style.header false

@[expose] public section

open Set

namespace IntervalArithmetic

universe u

variable {α β : Type*}

section Bound

structure FiniteLowerBound (α : Type*) where
  isClosed : Bool
  bound : α

structure FiniteUpperBound (α : Type*) where
  isClosed : Bool
  bound : α

def FiniteLowerBound.le [Preorder α] (lb₁ lb₂ : FiniteLowerBound α) : Prop :=
  if ! lb₁.isClosed && lb₂.isClosed then
    lb₁.bound < lb₂.bound
  else
    lb₁.bound ≤ lb₂.bound

def FiniteUpperBound.le [Preorder α] (ub₁ ub₂ : FiniteUpperBound α) : Prop :=
  if ub₁.isClosed && !ub₂.isClosed then
    ub₁.bound < ub₂.bound
  else
    ub₁.bound ≤ ub₂.bound

instance [Preorder α] : Preorder (FiniteLowerBound α) where
  le := FiniteLowerBound.le
  le_refl lb := by simp [FiniteLowerBound.le]
  le_trans lb₁ lb₂ lb₃ := by grind [FiniteLowerBound.le]

instance [Preorder α] : Preorder (FiniteUpperBound α) where
  le := FiniteUpperBound.le
  le_refl ub₁ := by simp [FiniteUpperBound.le]
  le_trans ub₁ ub₂ ub₃ := by grind [FiniteUpperBound.le]

instance [Preorder α]
    [DecidableRel (fun a₁ a₂ : α => a₁ ≤ a₂)] [DecidableRel (fun a₁ a₂ : α => a₁ < a₂)] :
    DecidableRel (fun lb₁ lb₂ : FiniteLowerBound α => lb₁ ≤ lb₂) :=
  fun ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ inferInstanceAs (Decidable (if !c₁ && c₂ then a₁ < a₂ else a₁ ≤ a₂))

instance [Preorder α]
    [DecidableRel (fun a₁ a₂ : α => a₁ ≤ a₂)] [DecidableRel (fun a₁ a₂ : α => a₁ < a₂)] :
    DecidableRel (fun ub₁ ub₂ : FiniteUpperBound α => ub₁ ≤ ub₂) :=
  fun⟨c₁, a₁⟩ ⟨c₂, a₂⟩ ↦ inferInstanceAs (Decidable (if c₁ && !c₂ then a₁ < a₂ else a₁ ≤ a₂))

@[simp]
def FiniteLowerBound.le_def [Preorder α] (lb₁ lb₂ : FiniteLowerBound α) :
    lb₁ ≤ lb₂ ↔
    if ! lb₁.isClosed && lb₂.isClosed then lb₁.bound < lb₂.bound else lb₁.bound ≤ lb₂.bound := by
  rfl

@[simp]
def FiniteUpperBound.le_def [Preorder α] (ub₁ ub₂ : FiniteUpperBound α) :
    ub₁ ≤ ub₂ ↔
    if ub₁.isClosed && !ub₂.isClosed then ub₁.bound < ub₂.bound else ub₁.bound ≤ ub₂.bound := by
  rfl

abbrev LowerBound (α : Type*) := WithBot (FiniteLowerBound α)

abbrev UpperBound (α : Type*) := WithTop (FiniteUpperBound α)

def LowerBound.Bounds [Preorder β] (φ : α → β) (lb : LowerBound α) (b : β) : Prop :=
  match lb with
  | ⊥ => True
  | (⟨isClosed, a⟩ : FiniteLowerBound α) => if isClosed then φ a ≤ b else φ a < b

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

def LowerBound.open (lb : LowerBound α) : LowerBound α :=
  match lb with
  | ⊥ => ⊥
  | (⟨_, a⟩ : FiniteLowerBound α) => (⟨false, a⟩ : FiniteLowerBound α)

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

structure Interval (α : Type*) where
  lb : LowerBound α
  ub : UpperBound α

instance [Repr α] : Repr (Interval α) where
  reprPrec x _ :=
    let left := match x.lb with
    | ⊥ => f!"(-∞"
    | some ⟨c, a⟩ => if c then f!"[{repr a}" else f!"({repr a}"
    let right := match x.ub with
    | ⊤ => f!"∞)"
    | some ⟨c, a⟩ => if c then f!"{repr a}]" else f!"{repr a})"
    f!"{left},{right}"

def Interval.univ (α : Type*) : Interval α := ⟨⊥, ⊤⟩

def Interval.toSet [Preorder β] (φ : α → β) (x : Interval α) : Set β :=
  {b | x.lb.Bounds φ b ∧ x.ub.Bounds φ b}

lemma Interval.mem_toSet [Preorder β] (φ : α → β) (b : β) (x : Interval α) :
  b ∈ (x.toSet φ) ↔ x.lb.Bounds φ b ∧ x.ub.Bounds φ b := by rfl

lemma Interval.univ_eq_univ [Preorder β] (φ : α → β) : (univ α).toSet φ = .univ := by
  ext
  simp [mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.univ]

lemma Interval.mem_toSet_univ [Preorder β] (φ : α → β) (b : β) : b ∈ (univ α).toSet φ := by
  simp [Interval.univ_eq_univ]

def Interval.subset [Preorder α] (x y : Interval α) : Prop := y.lb ≤ x.lb ∧ x.ub ≤ y.ub

lemma Interval.subset_def [Preorder α] (x y : Interval α) :
    x.subset y ↔ y.lb ≤ x.lb ∧ x.ub ≤ y.ub := by
  simp [subset]

lemma mem_toSet_of_mem_toSet_le [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r ≤ s) (hr : r ∈ x.toSet φ) :
    s ∈ (⟨x.lb, ⊤⟩ : Interval α).toSet φ := by
  simp [Interval.toSet, UpperBound.Bounds, LowerBound.bounds_of_le hrs hr.1]

lemma mem_toSet_of_le_mem_toSet [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r ≤ s) (hs : s ∈ x.toSet φ) :
  r ∈ (⟨⊥, x.ub⟩ : Interval α).toSet φ := by
  simp [Interval.toSet, LowerBound.Bounds, UpperBound.bounds_of_le hrs hs.2]

lemma mem_toSet_of_mem_toSet_lt [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r < s) (hr : r ∈ x.toSet φ) :
  s ∈ (⟨x.lb.open, ⊤⟩ : Interval α).toSet φ := by
  simp [Interval.toSet, UpperBound.Bounds, LowerBound.open_bounds_of_lt hrs hr.1]

lemma mem_toSet_of_lt_mem_toSet [Preorder β] {φ : α → β} {r s : β}
    {x : Interval α} (hrs : r < s) (hs : s ∈ x.toSet φ) :
  r ∈ (⟨⊥, x.ub.open⟩ : Interval α).toSet φ := by
  simp [Interval.toSet, LowerBound.Bounds, UpperBound.open_bounds_of_lt hrs hs.2]

lemma Interval.subset_of_subset [PartialOrder α] [Preorder β] (φ : α → β) (hφ : StrictMono φ)
    {x y : Interval α} (hxy : x.subset y) :
    x.toSet φ ⊆ y.toSet φ := by
  intro b hb
  rw [mem_toSet] at hb ⊢
  exact ⟨LowerBound.bounds_of_bounds hφ hxy.1 hb.1, UpperBound.bounds_of_bounds hφ hxy.2 hb.2⟩

section Inter

instance [Preorder α]
    [DecidableRel (fun a b : α => a ≤ b)]
    [DecidableRel (fun a b : α => a < b)] :
    Max (LowerBound α) := maxOfLe

instance [Preorder α]
    [DecidableRel (fun a b : α => a ≤ b)]
    [DecidableRel (fun a b : α => a < b)] :
    Min (UpperBound α) := minOfLe

def Interval.inter [Preorder α]
    [DecidableRel (fun a b : α => a ≤ b)]
    [DecidableRel (fun a b : α => a < b)]
    (x y : Interval α) : Interval α := ⟨max x.lb y.lb, min x.ub y.ub⟩

theorem Interval.inter_inclusion [Preorder α] [Preorder β] {φ : α → β}
    [DecidableRel (fun a b : α => a ≤ b)]
    [DecidableRel (fun a b : α => a < b)]
    {x y : Interval α} {b : β} (hbx : b ∈ x.toSet φ) (hby : b ∈ y.toSet φ) :
    b ∈ (x.inter y).toSet φ := by
  -- CHATGPT proof:
  rw [Interval.mem_toSet] at hbx hby ⊢
  rcases hbx with ⟨hlx, hux⟩
  rcases hby with ⟨hly, huy⟩
  constructor
  · by_cases h : x.lb ≤ y.lb
    · have hmax : max x.lb y.lb = y.lb := by
        change (if x.lb ≤ y.lb then y.lb else x.lb) = y.lb
        simp [h]
      simpa [Interval.inter, hmax] using hly
    · have hmax : max x.lb y.lb = x.lb := by
        change (if x.lb ≤ y.lb then y.lb else x.lb) = x.lb
        simp [h]
      simpa [Interval.inter, hmax] using hlx
  · by_cases h : x.ub ≤ y.ub
    · have hmin : min x.ub y.ub = x.ub := by
        change (if x.ub ≤ y.ub then x.ub else y.ub) = x.ub
        simp [h]
      simpa [Interval.inter, hmin] using hux
    · have hmin : min x.ub y.ub = y.ub := by
        change (if x.ub ≤ y.ub then x.ub else y.ub) = y.ub
        simp [h]
      simpa [Interval.inter, hmin] using huy

end Inter

section Order

def Interval.le [Preorder α] : Interval α → Interval α → Prop
  | ⟨_, _⟩, ⟨⊥, _⟩ => False
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => False
  | ⟨_, some ⟨_, x_ub⟩⟩, ⟨some ⟨_, y_lb⟩, _⟩ => x_ub ≤ y_lb

instance [Preorder α] [h_le : DecidableRel (fun a b : α => a ≤ b)]
    (x y : Interval α) : Decidable (x.le y) :=
  match x, y with
  | ⟨_, _⟩, ⟨⊥, _⟩ => isFalse id
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => isFalse id
  | ⟨_, some ⟨_, x_ub⟩⟩, ⟨some ⟨_, y_lb⟩, _⟩ => h_le x_ub y_lb

def Interval.lt [Preorder α] : Interval α → Interval α → Prop
  | ⟨_, _⟩, ⟨⊥, _⟩ => False
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => False
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => x_ub < y_lb
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => x_ub ≤ y_lb
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => x_ub ≤ y_lb
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => x_ub ≤ y_lb

instance [Preorder α]
    [h_le : DecidableRel (fun a b : α => a ≤ b)]
    [h_lt : DecidableRel (fun a b : α => a < b)]
    (x y : Interval α) : Decidable (x.lt y) :=
  match x, y with
  | ⟨_, _⟩, ⟨⊥, _⟩ => isFalse id
  | ⟨_, ⊤⟩, ⟨some _, _⟩ => isFalse id
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => h_lt x_ub y_lb
  | ⟨_, some ⟨true,  x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => h_le x_ub y_lb
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨true,  y_lb⟩, _⟩ => h_le x_ub y_lb
  | ⟨_, some ⟨false, x_ub⟩⟩, ⟨some ⟨false, y_lb⟩, _⟩ => h_le x_ub y_lb

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

end Order


end Interval

end IntervalArithmetic
