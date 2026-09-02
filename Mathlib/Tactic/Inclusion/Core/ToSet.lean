/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Set.Insert

/-!
# Definition of `ToSet` and basic API

This file defines the `ToSet` class and its API needed for the `inclusion` tactic.

## Implimentation Notes

* `Inclusion.IntervalBool` is nearly identical to `Lean.LBool` but with a seperate API and
documentation which is catered to the needs of the inclusion tactic.

-/

@[expose] public section

namespace Inclusion

/-- A `ToSet Iα α` instance provides a way of interpreting elements of `Iα` as sets of `α`,
through a function `toSet : Iα → Set α`. In its use in the `inclusion` tactic, `Iα` will be
a type with good computational properties (such as `Interval Dyadic`) and `α` will be some
type that appears in the user's expression, such as `ℝ`. -/
class ToSet (Iα : Type*) (α : outParam Type*) where
  /-- The mapping of elements of `Iα` to sets in `α`. -/
  toSet : Iα → Set α

instance {Iα α : Type*} [ToSet Iα α] : Membership α Iα where
  mem s a := ToSet.toSet s a

lemma ToSet.mem_def {Iα α : Type*} [ToSet Iα α] (a : α) (s : Iα) :
    a ∈ s ↔ a ∈ ToSet.toSet s := Iff.rfl

lemma ToSet.mem_of_eq_of_mem {Iα α : Type*} [ToSet Iα α] {x y : α} {s : Iα}
    (hxy : x = y) (hy : y ∈ s) : x ∈ s := hxy ▸ hy

lemma ToSet.mem_of_mem_of_eq {Iα α : Type*} [ToSet Iα α] {x y : α} {s : Iα}
    (hxy : x = y) (hx : x ∈ s) : y ∈ s := hxy ▸ hx

/-- A `Univ Iα α` instance is a specification of an element `univ : Iα` such that
every element of `α` belongs to `univ`. This is useful for assigning a container to
inclusion variables that have no inclusion hypotheses. -/
class Univ (Iα α : Type*) [ToSet Iα α] where
  /-- A (computational) representative of the universal set. -/
  univ : Iα
  /-- Every element of `α` belongs to `univ`. -/
  mem_univ (x : α) : x ∈ univ

/-- A `Refine Iα α` instance is a specification of a (computable) function `refine : Iα → Iα → Iα`
such that for any `s t : Iα`, `s ∩ t ⊆ refine s t` as sets of `α`. This is useful for merging
multiple inclusion hypotheses of a single inclusion variable. -/
class Refine (Iα α : Type*) [ToSet Iα α] where
  /-- A (computable) function to refine two inclusion hypotheses. -/
  refine : Iα → Iα → Iα
  /-- If `x ∈ s` and `x ∈ t` then `x ∈ refine s t`. -/
  mem_refine {x : α} {s t : Iα} (hs : x ∈ s) (ht : x ∈ t) : x ∈ refine s t

/-- A `Coarsen Iα α` instance is a specification of a (computable) function `coarsen : Iα → Iα → Iα`
such that for any `s t : Iα`, `s ∪ t ⊆ coarsen s t`. This is useful for applying an inclusion
function to a cover of the input and then merging the results. -/
class Coarsen (Iα α : Type*) [ToSet Iα α] where
  /-- A represented set containing both input sets. -/
  coarsen : Iα → Iα → Iα
  /-- If `x ∈ s` then `x ∈ coarsen s t`. -/
  mem_coarsen_left {x : α} {s t : Iα} (hx : x ∈ s) : x ∈ coarsen s t
  /-- If `x ∈ t` then `x ∈ coarsen s t`. -/
  mem_coarsen_right {x : α} {s t : Iα} (hx : x ∈ t) : x ∈ coarsen s t

universe u

/-- A `Cover Iα α` specifies a function `coverMap` to compute a "refined" inclusion of `F s`
for `s : Iα` and an inclusion function `F : Iα → Iβ`, by computing `F` on each element of a
cover of `s` and then using `coarsen` to merge the results. Schematically

`coverMap s F = fold coarsen (map F (cover s))`

where `cover : Iα → Array Iα` would specify the underlying cover, but the `coverMap` formulation
allows this function to be implemented more efficiently for kernel reduction. -/
structure Cover (Iα α : Type*) [ToSet Iα α] where
  /-- Compute an inclusion for `F s` using a cover of `s`. -/
  coverMap {Iβ β : Type u} [ToSet Iβ β] [Coarsen Iβ β] (s : Iα) (F : Iα → Iβ) : Iβ
  /-- If `x ∈ s` and `∀ t, x ∈ t → y ∈ F t` then `y ∈ coverMap s F`. -/
  mem_coverMap {Iβ β : Type u} [ToSet Iβ β] [Coarsen Iβ β] {s : Iα} {F : Iα → Iβ} {x : α} {y : β}
    (hx : x ∈ s) (hy : ∀ t, x ∈ t → y ∈ F t) : y ∈ coverMap s F

section IntervalBool

/-- An `IntervalBool` represents the result of a `Prop` inclusion and is either
`true` (if the proposition is computed true), `false` (if the proposition is computed false),
or `undetermined` (if the computation is indeterminate). -/
inductive IntervalBool
  | true
  | false
  | undetermined

/-- The mapping from `IntervalBool` to `Set Prop` which identifies each option
(`true`, `false`, `undetermined`) with its set of possible outcomes
(`{True}`, `{False}`, `{True, False}` respectively). -/
def IntervalBool.toPropSet : IntervalBool → Set Prop
  | true => {True}
  | false => {False}
  | undetermined => {True, False}

instance : ToSet IntervalBool Prop := ⟨IntervalBool.toPropSet⟩

@[simp]
theorem IntervalBool.mem_true_iff {p : Prop} : p ∈ IntervalBool.true ↔ p := by
  simp [ToSet.mem_def, ToSet.toSet, IntervalBool.toPropSet]

@[simp]
theorem IntervalBool.mem_false_iff {p : Prop} : p ∈ IntervalBool.false ↔ ¬p := by
  simp [ToSet.mem_def, ToSet.toSet, IntervalBool.toPropSet]

theorem IntervalBool.mem_true {p : Prop} (hp : p) : p ∈ IntervalBool.true :=
  IntervalBool.mem_true_iff.mpr hp

theorem IntervalBool.mem_false {p : Prop} (hp : ¬p) : p ∈ IntervalBool.false :=
  IntervalBool.mem_false_iff.mpr hp

@[simp]
theorem IntervalBool.mem_undetermined (p : Prop) : p ∈ IntervalBool.undetermined := by
  simpa [ToSet.mem_def, ToSet.toSet, IntervalBool.toPropSet] using Classical.em p

/-- Negation of an `IntervalBool` value. -/
def IntervalBool.not : IntervalBool → IntervalBool
  | .true => .false
  | .false => .true
  | .undetermined => .undetermined

theorem IntervalBool.not_mem {p : Prop} {a : IntervalBool}
    (hp : p ∈ a) : (¬p) ∈ a.not := by
  cases a <;> by_cases hp' : p <;> simp_all [IntervalBool.not]

/-- Conjunction of two `IntervalBool` values. -/
@[macro_inline]
def IntervalBool.and : IntervalBool → IntervalBool → IntervalBool
  | .true, .true => .true
  | .false, _ | _, .false => .false
  | _, _ => .undetermined

theorem IntervalBool.and_mem {p q : Prop} {a b : IntervalBool}
    (hp : p ∈ a) (hq : q ∈ b) : (p ∧ q) ∈ a.and b := by
  cases a <;> cases b <;> simp_all [IntervalBool.and]

/-- Disjunction of two `IntervalBool` values. -/
@[macro_inline]
def IntervalBool.or : IntervalBool → IntervalBool → IntervalBool
  | .true, _ | _, .true => .true
  | .false, .false => .false
  | _, _ => .undetermined

theorem IntervalBool.or_mem {p q : Prop} {a b : IntervalBool}
    (hp : p ∈ a) (hq : q ∈ b) : (p ∨ q) ∈ a.or b := by
  cases a <;> cases b <;> by_cases hp' : p <;> by_cases hq' : q <;>
    simp_all [IntervalBool.or]

theorem true_of_mem_intervalBool_true {p : Prop} (hp : p ∈ IntervalBool.true) : p :=
  IntervalBool.mem_true_iff.mp hp

theorem true_of_mem_intervalBool_eq_true {p : Prop} {b : IntervalBool} (hp : p ∈ b)
    (hb : b = IntervalBool.true) : p :=
  true_of_mem_intervalBool_true (hb ▸ hp)

/-- Return `true` exactly when the input is `IntervalBool.true`. -/
def IntervalBool.isTrue : IntervalBool → Bool
  | .true => Bool.true
  | .false | .undetermined => Bool.false

theorem IntervalBool.eq_true_of_isTrue_eq_true {b : IntervalBool}
    (h : b.isTrue = Bool.true) : b = .true := by
  cases b <;> simp_all [IntervalBool.isTrue]

/-- Union of two `IntervalBool`s. -/
@[macro_inline]
def IntervalBool.union : IntervalBool → IntervalBool → IntervalBool
  | .true, .true => .true
  | .false, .false => .false
  | _, _ => .undetermined

instance : Coarsen IntervalBool Prop where
  coarsen := IntervalBool.union
  mem_coarsen_left := by
    intro p s t hp
    cases s <;> cases t <;> simp_all [IntervalBool.union]
  mem_coarsen_right := by
    intro p s t hp
    cases s <;> cases t <;> simp_all [IntervalBool.union]

end IntervalBool

end Inclusion
