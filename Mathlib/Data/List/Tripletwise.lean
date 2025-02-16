/-
Copyright (c) 2025 Joseph Myers, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yaël Dillies
-/
import Aesop
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Tripletwise predicates on list.

## Main definitions

* `List.Tripletwise` says that a predicate applies to all ordered triples of elements of a list.

-/


namespace List

variable {α β : Type*}

/-- Whether a predicate holds for all ordered triples of elements of a list. -/
@[mk_iff]
inductive Tripletwise (p : α → α → α → Prop) : List α → Prop
  | nil : [].Tripletwise p
  | cons {a : α} {l : List α} : l.Pairwise (p a) → l.Tripletwise p → (a :: l).Tripletwise p

attribute [simp] Tripletwise.nil

variable {a b c : α} {l : List α} {p q : α → α → α → Prop} {f : α → β} {p' : β → β → β → Prop}

lemma tripletwise_cons : (a :: l).Tripletwise p ↔ l.Pairwise (p a) ∧ l.Tripletwise p := by
  rw [tripletwise_iff]; aesop

variable (a b p)

@[simp] lemma tripletwise_singleton : [a].Tripletwise p := by
  simp [tripletwise_cons]

@[simp] lemma tripletwise_pair : [a, b].Tripletwise p := by
  simp [tripletwise_cons]

variable {a b p}

@[simp] lemma tripletwise_triple : [a, b, c].Tripletwise p ↔ p a b c := by
  simp [tripletwise_cons]

lemma Tripletwise.imp (h : ∀ {a b c}, p a b c → q a b c) (hl : l.Tripletwise p) :
    l.Tripletwise q := by
  induction hl with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.imp h) ih

lemma tripletwise_map :
    (l.map f).Tripletwise p' ↔ l.Tripletwise (fun a b c ↦ p' (f a) (f b) (f c)) := by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, tripletwise_cons, ih, pairwise_map]

lemma Tripletwise.of_map
    (h : ∀ {a b c}, p' (f a) (f b) (f c) → p a b c) (hl : (l.map f).Tripletwise p') :
    l.Tripletwise p := by
  rw [tripletwise_map] at hl
  exact hl.imp h

lemma Tripletwise.map (h : ∀ {a b c}, p a b c → p' (f a) (f b) (f c)) (hl : l.Tripletwise p) :
    (l.map f).Tripletwise p' :=
  tripletwise_map.2 (hl.imp h)

lemma tripletwise_iff_getElem : l.Tripletwise p ↔ ∀ i j k (hij : i < j) (hjk : j < k)
    (hk : k < l.length), p l[i] l[j] l[k] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [tripletwise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk ↦ ?_,
            fun h ↦ ⟨fun i j hi hj hij ↦ ?_, fun i j k hij hjk hk ↦ ?_⟩⟩
    · rcases i with - | i <;> rcases j with - | j
      · simp at hij
      · rcases k with - | k
        · omega
        · simpa using hh j k (by omega) (by omega) (by omega)
      · simp at hij
      · rcases k with - | k
        · omega
        · simpa using ht i j k (by omega) (by omega) (by omega)
    · simpa using h 0 (i + 1) (j + 1) (by omega) (by omega) (by omega)
    · simpa using h (i + 1) (j + 1) (k + 1) (by omega) (by omega) (by omega)

end List
