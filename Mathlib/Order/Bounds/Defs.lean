/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.TypeStar
public import Mathlib.Tactic.ToDual

/-!
# Definitions about upper/lower bounds

In this file we define:
* `upperBounds`, `lowerBounds` : the set of upper bounds (resp., lower bounds) of a set;
* `BddAbove s`, `BddBelow s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `IsLeast s a`, `IsGreatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `IsLUB s a`, `IsGLB s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.
* `IsCofinal s`: for every `a`, there exists a member of `s` greater or equal to it.
* `IsCofinalFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `a ≤ b`
* `IsCoinitial s`: for every `a`, there exists a member of `s` less than or equal to it.
* `IsCoinitialFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `b ≤ a`
-/

@[expose] public section

variable {α : Type*} [LE α]

/-- The set of upper bounds of a set. -/
@[to_dual /-- The set of lower bounds of a set. -/]
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- A set is bounded above if there exists an upper bound. -/
@[to_dual /-- A set is bounded below if there exists a lower bound. -/]
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/]
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

/-- A set `s` is said to be cofinal for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
such that `a ≤ b`. -/
@[to_dual /-- A set `s` is said to be coinitial for a set `t` if, for all `a ∈ s` there exists
`b ∈ t` such that `b ≤ a`. -/]
def IsCofinalFor (s t : Set α) := ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, a ≤ b

/-- A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`. -/
@[to_dual /-- A set is coinitial when for every `x : α` there exists `y ∈ s` with `y ≤ x`. -/]
def IsCofinal (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, x ≤ y

class OrderSupInfSet (α : Type*) [LE α] extends SupSet α, InfSet α where
  protected isLUB_sSup_of_exists_isLUB s : (∃ a, IsLUB s a) → IsLUB s (sSup s)
  protected isGLB_sInf_of_exists_isGLB s : (∃ a, IsGLB s a) → IsGLB s (sInf s)

attribute [to_dual self (reorder := 3 4, 5 6)] OrderSupInfSet.mk
attribute [to_dual existing] OrderSupInfSet.toSupSet
attribute [to_dual existing] OrderSupInfSet.isLUB_sSup_of_exists_isLUB

@[to_dual]
theorem subset_upperBounds_lowerBounds (s : Set α) : s ⊆ upperBounds (lowerBounds s) :=
  fun _ hx _ hy => hy hx

@[to_dual]
theorem IsGreatest.isLUB {s : Set α} {a : α} (h : IsGreatest s a) : IsLUB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual (attr := simp)]
theorem isLUB_lowerBounds {s : Set α} {a : α} : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

@[to_dual]
abbrev OrderSupInfSet.ofSupSet {α : Type*} [SupSet α] [LE α]
    (isLUB_sSup_of_exists_isLUB : ∀ s : Set α, (∃ a, IsLUB s a) → IsLUB s (sSup s)) :
    OrderSupInfSet α where
  isLUB_sSup_of_exists_isLUB := isLUB_sSup_of_exists_isLUB
  sInf s := sSup (lowerBounds s)
  isGLB_sInf_of_exists_isGLB _ h :=
    isLUB_lowerBounds.mp (isLUB_sSup_of_exists_isLUB _ (h.imp fun _ ↦ IsGreatest.isLUB))

open Classical in
noncomputable abbrev OrderSupInfSet.choose {α : Type*} [LE α] (d : α) :
    OrderSupInfSet α where
  sSup s := if h : ∃ x, IsLUB s x then h.choose else d
  sInf s := if h : ∃ x, IsGLB s x then h.choose else d
  isLUB_sSup_of_exists_isLUB _ h := dif_pos h ▸ Exists.choose_spec _
  isGLB_sInf_of_exists_isGLB _ h := dif_pos h ▸ Exists.choose_spec _
