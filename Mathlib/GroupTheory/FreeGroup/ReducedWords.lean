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
theorem isReduced_cons {a b: (α × Bool)} :
    IsReduced (a :: b :: L) ↔ ¬(a.1 = b.1 ∧ (!a.2) = b.2) ∧ IsReduced (b :: L) :=
  List.chain'_cons

@[to_additive]
theorem IsReduced.not_step : IsReduced L₁ → ¬ Red.Step L₁ L₂
| red, step => by induction step; simp [IsReduced] at red

@[to_additive]
theorem isReduced_not_step_iff : IsReduced L₁ ↔ ∀ L₂, ¬ Red.Step L₁ L₂ where
  mp h _ := h.not_step
  mpr hL := by
    induction L₁ with
    | nil => exact isReduced_nil
    | cons x l ih =>
      cases l with
      | nil => exact isReduced_singleton
      | cons y l' =>
        rw [isReduced_cons]
        constructor
        · intro ⟨eq1, eq2⟩
          obtain ⟨x1, x2⟩ := x
          obtain ⟨y1, y2⟩ := y
          simp only at eq1 eq2
          apply hL l'
          rw [eq1, ← eq2]
          apply Red.Step.cons_not
        · apply ih
          intro L₂ step
          apply hL (x :: L₂)
          exact Red.Step.cons step

@[to_additive]
theorem IsReduced.infix : IsReduced L₂ → L₁ <:+: L₂ → IsReduced L₁ := Chain'.infix

@[to_additive]
theorem IsReduced.min (h : IsReduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]
theorem IsReduced.cons_append_chain {x : α × Bool} {L₁ L₂ : List (α × Bool)} (h : L₁ ≠ []) :
    IsReduced (x :: L₁) → IsReduced (L₁ ++ L₂) → IsReduced (x :: L₁ ++ L₂) := by
  intro h1 h2
  induction L₁
  · contradiction
  · apply isReduced_cons.mp at h1
    apply isReduced_cons.mpr
    tauto

@[to_additive]
theorem IsReduced.append_chain {L₁ L₂ L₃ : List (α × Bool)} (h : L₂ ≠ []) :
    IsReduced (L₁ ++ L₂) → IsReduced (L₂ ++ L₃) → IsReduced (L₁ ++ L₂ ++ L₃) := by
  intro h1 h2
  induction L₁
  case nil => simp [h2]
  case cons head tail ih =>
    refine h1.cons_append_chain (by simp [h]) (ih (h1.infix ⟨[head], [], by simp⟩))

variable [DecidableEq α]

@[to_additive]
theorem isReduced_iff_reduce_eq : IsReduced L ↔ reduce L = L := by
  constructor
  · intro h
    rw [← h.min]
    exact reduce.red
  · intro h
    unfold IsReduced
    rw [List.chain'_iff_forall_rel_of_append_cons_cons]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl hx
    simp only at hl hx
    rw [hx.1, ← hx.2] at hl
    nth_rw 2 [hl] at h
    apply reduce.not h

@[to_additive]
theorem isReduced_toWord {x : FreeGroup α} : IsReduced (x.toWord) := by
  rw [isReduced_iff_reduce_eq]
  simp

end FreeGroup
