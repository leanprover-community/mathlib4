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

* `FreeGroup.IsReduced`: the predicate for reduced words

-/
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}

/-- Predicate asserting that the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel. -/
@[to_additive "Predicate asserting the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel."]
def IsReduced (L : List (α × Bool)) : Prop := List.Chain' (fun a b => ¬(a.1 = b.1 ∧ (!a.2) = b.2)) L

@[to_additive (attr := simp)]
theorem isReduced_nil : IsReduced ([] : List (α × Bool)) := List.chain'_nil

@[to_additive (attr := simp)]
theorem isReduced_singleton {a : (α × Bool)} : IsReduced [a] := List.chain'_singleton a

@[to_additive (attr := simp)]
theorem isReduced_cons {a b : (α × Bool)} :
    IsReduced (a :: b :: L) ↔ ¬(a.1 = b.1 ∧ (!a.2) = b.2) ∧ IsReduced (b :: L) :=
  List.chain'_cons

@[to_additive]
theorem IsReduced.not_step (h : IsReduced L₁) : ¬ Red.Step L₁ L₂ := fun step ↦ by
  induction step
  simp [IsReduced] at h

@[to_additive]
theorem isReduced_iff_not_step : IsReduced L₁ ↔ ∀ L₂, ¬ Red.Step L₁ L₂ where
  mp h _ := h.not_step
  mpr hL := by
    induction L₁ with
    | nil => exact isReduced_nil
    | cons x l ih =>
      cases l with
      | nil => exact isReduced_singleton
      | cons y l' =>
        rw [isReduced_cons]
        refine ⟨fun ⟨eq₁, eq₂⟩ ↦ ?_, ih <| fun L₂ step => hL (x :: L₂) <| Red.Step.cons step⟩
        obtain ⟨x₁, x₂⟩ := x
        obtain ⟨y₁, y₂⟩ := y
        simp only at eq₁ eq₂
        apply hL l'
        rw [eq₁, ← eq₂]
        apply Red.Step.cons_not


@[to_additive]
theorem IsReduced.infix (h : IsReduced L₂) (h' : L₁ <:+: L₂) : IsReduced L₁ := Chain'.infix h h'

@[to_additive]
theorem IsReduced.min (h : IsReduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]
theorem IsReduced.cons_append {x : α × Bool} {L₁ L₂ : List (α × Bool)} (h : L₁ ≠ [])
    (h₁ : IsReduced (x :: L₁)) (h₁₂ : IsReduced (L₁ ++ L₂)) : IsReduced (x :: L₁ ++ L₂) := by
  induction L₁ <;> simp_all

@[to_additive]
theorem IsReduced.append_append {L₁ L₂ L₃ : List (α × Bool)} (h : L₂ ≠ [])
    (h₁₂ : IsReduced (L₁ ++ L₂)) (h₂₃ : IsReduced (L₂ ++ L₃)) : IsReduced (L₁ ++ L₂ ++ L₃) := by
  induction L₁
  case nil => simp [h₂₃]
  case cons head tail ih =>
    exact h₁₂.cons_append (by simp [h]) (ih (h₁₂.infix ⟨[head], [], by simp⟩))

variable [DecidableEq α]

@[to_additive]
theorem isReduced_iff_reduce_eq : IsReduced L ↔ reduce L = L where
  mp h := by
    rw [← h.min]
    exact reduce.red
  mpr h := by
    unfold IsReduced
    rw [List.chain'_iff_forall_rel_of_append_cons_cons]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl hx
    simp only at hl hx
    rw [hx.1, ← hx.2] at hl
    nth_rw 2 [hl] at h
    exact reduce.not h

@[to_additive]
theorem isReduced_toWord {x : FreeGroup α} : IsReduced (x.toWord) := by
  simp [isReduced_iff_reduce_eq]

end FreeGroup
