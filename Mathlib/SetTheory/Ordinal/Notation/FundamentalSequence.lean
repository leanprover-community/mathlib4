/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Set.Operations

/-!
# Fundamental sequences

If `o` is an ordinal, a fundamental sequence for `o` is a strictly monotonic function
`Iio o.cof.ord → Iio o` with cofinal range.

For `o` a countable ordinal, there are only three possible lengths for such a sequence: 0, 1, or
`ω`. To nicely manage these three different cases, we define `Sequence α` as an inductive type with
the respective constructors. At the moment, the file contains only the basic API for this type.

The `Sequence` API is intended to be used constructively in the context of ordinal notations. For a
more general but non-constructive notion of fundamental sequences for values with arbitrary
cofinalities, see `Ordinal.IsFundamentalSequence`.

## Todo

- Define fundamental sequences.
- Define the slow and fast-growing hierarchies.
- Replace the definitions in `Mathlib.SetTheory.Ordinal.Notation.Cantor` by the ones in this file.
-/

universe u

variable {α β : Type*}

namespace Ordinal

/-- The type of sequences with length 0, 1, or `ω`. These are the possible different lengths for a
fundamental sequence. -/
inductive Sequence (α : Type u) : Type u
  /-- The empty sequence, whose limit is the bottom element. -/
  | empty : Sequence α
  /-- The sequence consisting only of `x`, whose limit is the succesor of `x`. -/
  | singleton (x : α) : Sequence α
  /-- A sequence `ℕ → α`, whose limit is its least strict upper bound, or equivalently for strictly
  monotonic sequences, its supremum. -/
  | ofFun (f : ℕ → α) : Sequence α

namespace Sequence

instance : EmptyCollection (Sequence α) := ⟨empty⟩
instance : Inhabited (Sequence α) := ⟨∅⟩
@[simp] theorem empty_def : @empty α = ∅ := rfl

instance : Singleton α (Sequence α) := ⟨singleton⟩
@[simp] theorem singleton_def (x : α) : singleton x = {x} := rfl

@[simp] theorem singleton_ne_empty (x : α) : ({x} : Sequence α) ≠ ∅ := fun h ↦ by injection h
@[simp] theorem empty_ne_singleton (x : α) : ∅ ≠ ({x} : Sequence α) := fun h ↦ by injection h

@[simp] theorem ofFun_ne_empty (f : ℕ → α) : ofFun f ≠ ∅ := fun h ↦ by injection h
@[simp] theorem empty_ne_ofFun (f : ℕ → α) : ∅ ≠ ofFun f := fun h ↦ by injection h

@[simp] theorem singleton_ne_ofFun (x : α) (f : ℕ → α) : {x} ≠ ofFun f := fun h ↦ by injection h
@[simp] theorem ofFun_ne_singleton (f : ℕ → α) (x : α) : ofFun f ≠ {x} := fun h ↦ by injection h

/-- The range of a sequence is the set of values it contains -/
def range : Sequence α → Set α
  | empty => ∅
  | singleton x => {x}
  | ofFun f => Set.range f

@[simp] theorem range_empty : range (∅ : Sequence α) = ∅ := rfl
@[simp] theorem range_singleton (x : α) : range {x} = {x} := rfl
@[simp] theorem range_ofFun (f : ℕ → α) : range (ofFun f) = Set.range f := rfl

/-- Membership predicate for sequences -/
instance : Membership α (Sequence α) :=
  ⟨fun s x ↦ x ∈ s.range⟩

@[simp] theorem not_mem_empty (x : α) : x ∉ (∅ : Sequence α) := id
@[simp] theorem mem_singleton_iff {x y : α} : x ∈ ({y} : Sequence α) ↔ x = y := Iff.rfl
@[simp] theorem mem_ofFun_iff {x : α} {f : ℕ → α} : x ∈ ofFun f ↔ x ∈ Set.range f := Iff.rfl
@[simp] theorem mem_range_iff {s : Sequence α} {x : α} : x ∈ s.range ↔ x ∈ s := Iff.rfl

theorem mem_singleton (x : α) : x ∈ ({x} : Sequence α) := mem_singleton_iff.2 rfl
theorem mem_ofFun {f : ℕ → α} (n : ℕ) : f n ∈ ofFun f := ⟨n, rfl⟩

/-- Maps a sequence through a function -/
def map (s : Sequence α) (g : α → β) : Sequence β :=
  match s with
  | empty => ∅
  | singleton x => {g x}
  | ofFun f => ofFun (g ∘ f)

@[simp] theorem map_empty (g : α → β) : map ∅ g = ∅ := rfl
@[simp] theorem map_singleton (x : α) (g : α → β) : map {x} g = {g x} := rfl
@[simp] theorem map_ofFun (f : ℕ → α) (g : α → β) : map (ofFun f) g = ofFun (g ∘ f) := rfl

@[simp]
theorem map_eq_empty_iff {s : Sequence α} {g : α → β} : s.map g = ∅ ↔ s = ∅ := by
  cases s <;> simp

@[simp]
theorem mem_map {s : Sequence α} {f : α → β} {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  match s with
  | empty => by simp
  | singleton x => by simp [eq_comm]
  | ofFun f => by simp

/-- Attach to a sequence the proof that it contains all its elements -/
def attach : (s : Sequence α) → Sequence {a : α // a ∈ s}
  | empty => ∅
  | singleton x => {⟨x, rfl⟩}
  | ofFun f => ofFun fun n ↦ ⟨f n, n, rfl⟩

@[simp] theorem attach_empty : (∅ : Sequence α).attach = ∅ := rfl
@[simp] theorem attach_singleton (x : α) : ({x} : Sequence α).attach = {⟨x, rfl⟩} := rfl
@[simp] theorem attach_ofFun (f : ℕ → α) : (ofFun f).attach = ofFun fun n ↦ ⟨f n, n, rfl⟩ := rfl

@[simp]
theorem attach_eq_empty_iff {s : Sequence α} : s.attach = ∅ ↔ s = ∅ := by
  cases s <;> simp

@[simp]
theorem mem_attach {s : Sequence α} {x : α} : ∀ h : x ∈ s, ⟨x, h⟩ ∈ s.attach := by
  cases s <;> simp

/-- Partial map -/
def pmap (s : Sequence α) (f : ∀ x ∈ s, β) : Sequence β :=
  s.attach.map fun x ↦ f x.1 x.2

@[simp]
theorem pmap_empty (f : ∀ x ∈ (∅ : Sequence α), β) : pmap ∅ f = ∅ :=
  rfl

@[simp]
theorem pmap_singleton (y : α) (f : ∀ x ∈ ({y} : Sequence α), β) : pmap _ f = {f y rfl} :=
  rfl

@[simp]
theorem pmap_ofFun (g : ℕ → α) (f : ∀ x ∈ ofFun g, β) :
    pmap _ f = ofFun fun n ↦ f (g n) (Set.mem_range_self _) :=
  rfl

@[simp]
theorem pmap_eq_empty_iff {s : Sequence α} : {f : ∀ x ∈ s, β} → pmap _ f = ∅ ↔ s = ∅ := by
  cases s <;> simp

@[simp]
theorem mem_pmap {s : Sequence α} {f : ∀ x ∈ s, β} {b : β} :
    b ∈ s.pmap f ↔ ∃ (a : α) (h : a ∈ s), f a h = b := by
  simp [pmap]

/-- Builds a list with the first `n` elements of the sequence. This can be used to print the
sequence. -/
def toList (s : Sequence α) (n : ℕ) : List α :=
  match s with
  | empty => []
  | singleton x => [x]
  | ofFun f => (List.range n).map f

@[simp] theorem toList_empty (n : ℕ) : @toList α ∅ n = [] := rfl
@[simp] theorem toList_singleton (x : α) (n : ℕ) : toList {x} n = [x] := rfl
@[simp] theorem toList_ofFun (f : ℕ → α) (n : ℕ) : toList (ofFun f) n = (List.range n).map f := rfl

end Sequence

end Ordinal
