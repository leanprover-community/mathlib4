/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amir Livne Bar-on, Bernhard Reinke
-/
import Mathlib.Data.List.Chain
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
This file defines some extra lemmas for free groups, in particular about (cyclically) reduced words.

## Main declarations

* `FreeGroup.Red.reduced`: the predicate for reduced words

-/
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}

namespace Red

/-- Predicate asserting that the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel. -/
@[to_additive "Predicate asserting the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel."]
def reduced (L : List (α × Bool)) : Prop := List.Chain' (fun a b => ¬(a.1 = b.1 ∧ (!a.2) = b.2)) L

@[to_additive (attr := simp)]
theorem reduced_nil : reduced ([] : List (α × Bool)) := List.chain'_nil

@[to_additive (attr := simp)]
theorem reduced_singleton {a : (α × Bool)} : reduced [a] := List.chain'_singleton a

@[to_additive (attr := simp)]
theorem reduced_cons {a b: (α × Bool)} :
    reduced (a :: b :: L) ↔ ¬(a.1 = b.1 ∧ (!a.2) = b.2) ∧ reduced (b :: L) :=
  List.chain'_cons

@[to_additive]
theorem not_step_reduced : reduced L₁ → ¬ Step L₁ L₂
| red, step => by induction step; simp [reduced] at red

@[to_additive]
theorem not_step_reduced_iff : reduced L₁ ↔ ∀ L₂, ¬ Step L₁ L₂ where
  mp h _ := not_step_reduced h
  mpr hL := by
    induction L₁ with
    | nil => exact reduced_nil
    | cons x l ih =>
      cases l with
      | nil => exact reduced_singleton
      | cons y l' =>
        rw [reduced_cons]
        constructor
        · intro ⟨eq1, eq2⟩
          obtain ⟨x1, x2⟩ := x
          obtain ⟨y1, y2⟩ := y
          simp only at eq1 eq2
          apply hL l'
          rw [eq1, ← eq2]
          apply Step.cons_not
        · apply ih
          intro L₂ step
          apply hL (x :: L₂)
          exact Step.cons step

@[to_additive]
theorem reduced_infix : reduced L₂ → L₁ <:+: L₂ → reduced L₁ := Chain'.infix

@[to_additive]
theorem reduced_min (h : reduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => not_step_reduced h

@[to_additive]
theorem reduced_cons_append_chain {x : α × Bool} {L₁ L₂ : List (α × Bool)} (h : L₁ ≠ []) :
    reduced (x :: L₁) → reduced (L₁ ++ L₂) → reduced (x :: L₁ ++ L₂) := by
  intro h1 h2
  induction L₁
  · contradiction
  · apply reduced_cons.mp at h1
    apply reduced_cons.mpr
    tauto

@[to_additive]
theorem reduced_append_chain {L₁ L₂ L₃ : List (α × Bool)} (h : L₂ ≠ []) :
    reduced (L₁ ++ L₂) → reduced (L₂ ++ L₃) → reduced (L₁ ++ L₂ ++ L₃) := by
  intro h1 h2
  induction L₁
  case nil => simp [h2]
  case cons head tail ih =>
    refine reduced_cons_append_chain (by simp [h]) h1 (ih (reduced_infix h1 ⟨[head], [], by simp⟩))

variable [DecidableEq α]

@[to_additive]
theorem reduced_iff_eq_reduce : reduced L ↔ reduce L = L := by
  constructor
  · intro h
    rw [← reduced_min h]
    exact reduce.red
  · intro h
    unfold reduced
    rw [List.chain'_iff_forall_rel_of_append_cons_cons]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl hx
    simp only at hl hx
    rw [hx.1, ← hx.2] at hl
    nth_rw 2 [hl] at h
    apply reduce.not h

@[to_additive]
theorem reduced_toWord {x : FreeGroup α} : Red.reduced (x.toWord) := by
  rw [Red.reduced_iff_eq_reduce]
  simp

end Red

end FreeGroup
