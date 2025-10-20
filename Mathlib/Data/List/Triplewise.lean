/-
Copyright (c) 2025 Joseph Myers, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yaël Dillies
-/
import Aesop
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Triplewise predicates on list.

## Main definitions

* `List.Triplewise` says that a predicate applies to all ordered triples of elements of a list.

-/


namespace List

variable {α β : Type*}

/-- Whether a predicate holds for all ordered triples of elements of a list. -/
@[mk_iff]
inductive Triplewise (p : α → α → α → Prop) : List α → Prop
  | nil : [].Triplewise p
  | cons {a : α} {l : List α} : l.Pairwise (p a) → l.Triplewise p → (a :: l).Triplewise p

attribute [simp, grind ←] Triplewise.nil

variable {a b c : α} {l l₁ l₂ : List α} {p q : α → α → α → Prop} {f : α → β} {p' : β → β → β → Prop}

@[grind =]
lemma triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwise (p a) ∧ l.Triplewise p := by
  rw [triplewise_iff]; aesop

variable (a b p)

@[simp] lemma triplewise_singleton : [a].Triplewise p := by
  simp [triplewise_cons]

@[simp] lemma triplewise_pair : [a, b].Triplewise p := by
  simp [triplewise_cons]

variable {a b p}

@[simp] lemma triplewise_triple : [a, b, c].Triplewise p ↔ p a b c := by
  simp [triplewise_cons]

lemma Triplewise.imp (h : ∀ {a b c}, p a b c → q a b c) (hl : l.Triplewise p) :
    l.Triplewise q := by
  induction hl with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.imp h) ih

lemma triplewise_map :
    (l.map f).Triplewise p' ↔ l.Triplewise (fun a b c ↦ p' (f a) (f b) (f c)) := by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, triplewise_cons, ih, pairwise_map]

lemma Triplewise.of_map
    (h : ∀ {a b c}, p' (f a) (f b) (f c) → p a b c) (hl : (l.map f).Triplewise p') :
    l.Triplewise p := by
  rw [triplewise_map] at hl
  exact hl.imp h

lemma Triplewise.map (h : ∀ {a b c}, p a b c → p' (f a) (f b) (f c)) (hl : l.Triplewise p) :
    (l.map f).Triplewise p' :=
  triplewise_map.2 (hl.imp h)

lemma triplewise_iff_getElem : l.Triplewise p ↔ ∀ i j k (hij : i < j) (hjk : j < k)
    (hk : k < l.length), p l[i] l[j] l[k] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [triplewise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk ↦ ?_,
            fun h ↦ ⟨fun i j hi hj hij ↦ ?_, fun i j k hij hjk hk ↦ ?_⟩⟩
    · grind
    · simpa using h 0 (i + 1) (j + 1) (by cutsat) (by cutsat) (by cutsat)
    · simpa using h (i + 1) (j + 1) (k + 1) (by cutsat) (by cutsat) (by cutsat)

lemma triplewise_append : (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplewise p ∧
    (∀ a ∈ l₁, l₂.Pairwise (p a)) ∧ ∀ a ∈ l₂, l₁.Pairwise fun x y ↦ p x y a := by
  induction l₁ with
  | nil => simp
  | cons h t ih =>
    simp [triplewise_cons, ih, pairwise_append]
    aesop

lemma triplewise_reverse : l.reverse.Triplewise p ↔ l.Triplewise fun a b c ↦ p c b a := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [triplewise_append, pairwise_reverse, triplewise_cons, ih, and_comm]

end List
