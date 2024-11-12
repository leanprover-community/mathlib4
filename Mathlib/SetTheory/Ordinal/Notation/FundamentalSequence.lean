/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Set.Operations

/-!
# Fundamental sequences

If `x` is a successor limit in a linear order `α`, a fundamental sequence for `x` is a strictly
monotonic sequence `ℕ → α` whose supremum is `x`.

If `x` is not a successor limit, we can define two other types of fundamental sequences: the empty
sequence `∅` with limit `⊥`, and the singleton sequence `{x}` with limit `succ x` (the limit here is
more properly the least strict upper bound). This ensures that every countable ordinal
(nonconstructively) has a fundamental sequence, and it simplifies the definition of the fast-growing
hierarchy.

To nicely manage these three different cases, we define `Sequence α = Option α ⊕ (ℕ → α)` as the
type of sequences with length 0, 1, or `ω`. At the moment, the file contains only the basic API for
this type.

The `Sequence` API is intended to be used constructively in the context of ordinal notations. For a
more general but non-constructive notion of fundamental sequences for values with arbitrary
cofinalities, see `Ordinal.IsFundamentalSequence`.

## Todo

- Define fundamental sequences
- Define the slow and fast-growing hierarchies
- Replace the definitions in `Mathlib.SetTheory.Ordinal.Notation.Cantor` by the ones in this file.
-/

universe u

variable {α β : Type*}

namespace Ordinal

/-- The type of sequences with length 0, 1, or `ω`. These are the possible different lengths for a
fundamental sequence. -/
def Sequence (α : Type u) : Type u :=
  Option α ⊕ (ℕ → α)

namespace Sequence

/-- The empty sequence, whose limit is the bottom element. -/
instance : EmptyCollection (Sequence α) :=
  ⟨Sum.inl none⟩

instance : Inhabited (Sequence α) :=
  ⟨∅⟩

/-- The sequence consisting only of `x`, whose limit is the succesor of `x`. -/
instance : Singleton α (Sequence α) :=
  ⟨fun x ↦ Sum.inl (some x)⟩

/-- A sequence `ℕ → α`, whose limit is its least strict upper bound, or equivalently for strictly
monotonic sequences, its supremum. -/
def ofFun (f : ℕ → α) : Sequence α :=
  Sum.inr f

@[simp]
theorem singleton_ne_empty (x : α) : ({x} : Sequence α) ≠ ∅ := by
  change Sum.inl _ ≠ Sum.inl _
  simp

@[simp] theorem ofFun_ne_empty (f : ℕ → α) : ofFun f ≠ ∅ := Sum.inr_ne_inl
@[simp] theorem ofFun_ne_singleton (f : ℕ → α) (x : α) : ofFun f ≠ {x} := Sum.inr_ne_inl

@[simp] theorem empty_ne_singleton (x : α) : ∅ ≠ ({x} : Sequence α) := (singleton_ne_empty x).symm
@[simp] theorem empty_ne_ofFun (f : ℕ → α) : ∅ ≠ ofFun f := Sum.inl_ne_inr
@[simp] theorem singleton_ne_ofFun (x : α) (f : ℕ → α) : {x} ≠ ofFun f := Sum.inl_ne_inr

@[simp] theorem sum_inl_none_def : Sum.inl none = (∅ : Sequence α) := rfl
@[simp] theorem sum_inl_some_def (x : α) : Sum.inl (some x) = ({x} : Sequence α) := rfl
@[simp] theorem sum_inr_def (f : ℕ → α) : Sum.inr f = ofFun f := rfl

/-- Recursion on sequences, using the preferred forms of the constructors. -/
def recOn {p : Sequence α → Sort*} (s : Sequence α) (empty : p ∅) (singleton : ∀ x, p {x})
    (ofFun : ∀ f, p (ofFun f)) : p s :=
  match s with
  | Sum.inl none => empty
  | Sum.inl (some x) => singleton x
  | Sum.inr f => ofFun f

/-- The range of a sequence is the set of values it contains -/
def range : Sequence α → Set α
  | Sum.inl none => ∅
  | Sum.inl (some x) => {x}
  | Sum.inr f => Set.range f

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
  | Sum.inl none => ∅
  | Sum.inl (some x) => {g x}
  | Sum.inr f => ofFun (g ∘ f)

@[simp] theorem map_empty (g : α → β) : map ∅ g = ∅ := rfl
@[simp] theorem map_singleton (x : α) (g : α → β) : map {x} g = {g x} := rfl
@[simp] theorem map_ofFun (f : ℕ → α) (g : α → β) : map (ofFun f) g = ofFun (g ∘ f) := rfl

@[simp]
theorem map_eq_empty_iff {s : Sequence α} {g : α → β} : s.map g = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_map {s : Sequence α} {f : α → β} {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  match s with
  | Sum.inl none => by simp
  | Sum.inl (some x) => by simp [eq_comm]
  | Sum.inr g => by simp

/-- Attach to a sequence the proof that it contains all its elements -/
def attach : (s : Sequence α) → Sequence {a : α // a ∈ s}
  | Sum.inl none => ∅
  | Sum.inl (some x) => {⟨x, rfl⟩}
  | Sum.inr f => ofFun fun n ↦ ⟨f n, n, rfl⟩

@[simp] theorem attach_empty : (∅ : Sequence α).attach = ∅ := rfl
@[simp] theorem attach_singleton (x : α) : ({x} : Sequence α).attach = {⟨x, rfl⟩} := rfl
@[simp] theorem attach_ofFun (f : ℕ → α) : (ofFun f).attach = ofFun fun n ↦ ⟨f n, n, rfl⟩ := rfl

@[simp]
theorem attach_eq_empty_iff {s : Sequence α} : s.attach = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_attach {s : Sequence α} {x : α} : ∀ h : x ∈ s, ⟨x, h⟩ ∈ s.attach := by
  apply s.recOn <;> simp

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
  apply s.recOn <;> simp

@[simp]
theorem mem_pmap {s : Sequence α} {f : ∀ x ∈ s, β} {b : β} :
    b ∈ s.pmap f ↔ ∃ (a : α) (h : a ∈ s), f a h = b := by
  simp [pmap]

/-- Builds a list with the first `n` elements of the sequence. This can be used to print the
sequence. -/
def toList (s : Sequence α) (n : ℕ) : List α :=
  match s with
  | Sum.inl none => []
  | Sum.inl (some x) => [x]
  | Sum.inr f => (List.range n).map f

end Sequence

end Ordinal
