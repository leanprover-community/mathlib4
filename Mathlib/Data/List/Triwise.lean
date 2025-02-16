/-
Copyright (c) 2025 Joseph Myers, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yaël Dillies
-/
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Triwise predicates on list.

## Main definitions

* `List.Triwise` says that a predicate applies to all ordered triples of elements of a list.

-/


namespace List

variable {α β : Type*}

/-- Whether a predicate holds for all ordered triples of elements of a list. -/
@[mk_iff]
inductive Triwise (p : α → α → α → Prop) : List α → Prop
  | nil : [].Triwise p
  | cons {a : α} {l : List α} : l.Pairwise (p a) → l.Triwise p → (a :: l).Triwise p

attribute [simp] Triwise.nil

variable {a b c : α} {l : List α} {p q : α → α → α → Prop} {f : α → β} {p' : β → β → β → Prop}

lemma triwise_cons : (a :: l).Triwise p ↔ l.Pairwise (p a) ∧ l.Triwise p := by
  refine ⟨fun h ↦ ?_, fun h ↦ Triwise.cons h.1 h.2⟩
  cases h with
  | cons hp ht => exact ⟨hp, ht⟩

variable (a b p)

@[simp] lemma triwise_singleton : [a].Triwise p := by
  simp [triwise_cons]

@[simp] lemma triwise_pair : [a, b].Triwise p := by
  simp [triwise_cons]

variable {a b p}

@[simp] lemma triwise_triple : [a, b, c].Triwise p ↔ p a b c := by
  simp [triwise_cons]

lemma Triwise.imp (h : ∀ {a b c}, p a b c → q a b c) (hl : l.Triwise p) : l.Triwise q := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    rw [triwise_cons] at hl ⊢
    exact ⟨hl.1.imp h, ih hl.2⟩

lemma triwise_map : (l.map f).Triwise p' ↔ l.Triwise (fun a b c ↦ p' (f a) (f b) (f c)) := by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, triwise_cons, ih, pairwise_map]

lemma Triwise.of_map (h : ∀ {a b c}, p' (f a) (f b) (f c) → p a b c) (hl : (l.map f).Triwise p') :
    l.Triwise p := by
  rw [triwise_map] at hl
  exact hl.imp h

lemma Triwise.map (h : ∀ {a b c}, p a b c → p' (f a) (f b) (f c)) (hl : l.Triwise p) :
    (l.map f).Triwise p' :=
  triwise_map.2 (hl.imp h)

lemma triwise_iff_getElem : l.Triwise p ↔ ∀ i j k (hij : i < j) (hjk : j < k) (hk : k < l.length),
    p l[i] l[j] l[k] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [triwise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk ↦ ?_,
            fun h ↦ ⟨fun i j hi hj hij ↦ ?_, fun i j k hij hjk hk ↦ ?_⟩⟩
    · rcases i with - | i
      · rcases j with - | j
        · simp at hij
        · rcases k with - | k
          · omega
          · simpa using hh j k (by omega) (by omega) (by omega)
      · rcases j with - | j
        · simp at hij
        · rcases k with - | k
          · omega
          · simpa using ht i j k (by omega) (by omega) (by omega)
    · simpa using h 0 (i + 1) (j + 1) (by omega) (by omega) (by omega)
    · simpa using h (i + 1) (j + 1) (k + 1) (by omega) (by omega) (by omega)

end List
