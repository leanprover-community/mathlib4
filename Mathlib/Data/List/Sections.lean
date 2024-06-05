/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Forall2

#align_import data.list.sections from "leanprover-community/mathlib"@"26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2"
/-!
# List sections

This file proves some stuff about `List.sections` (definition in `Data.List.Defs`). A section of a
list of lists `[l₁, ..., lₙ]` is a list whose `i`-th element comes from the `i`-th list.
-/


open Nat Function

namespace List

variable {α β : Type*}

theorem mem_sections {L : List (List α)} {f} : f ∈ sections L ↔ Forall₂ (· ∈ ·) f L := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction L generalizing f
    · cases mem_singleton.1 h
      exact Forall₂.nil
    simp only [sections, bind_eq_bind, mem_bind, mem_map] at h
    rcases h with ⟨_, _, _, _, rfl⟩
    simp only [*, forall₂_cons, true_and_iff]
  · induction' h with a l f L al fL fs
    · simp only [sections, mem_singleton]
    simp only [sections, bind_eq_bind, mem_bind, mem_map]
    exact ⟨f, fs, a, al, rfl⟩
#align list.mem_sections List.mem_sections

theorem mem_sections_length {L : List (List α)} {f} (h : f ∈ sections L) : length f = length L :=
  (mem_sections.1 h).length_eq
#align list.mem_sections_length List.mem_sections_length

theorem rel_sections {r : α → β → Prop} :
    (Forall₂ (Forall₂ r) ⇒ Forall₂ (Forall₂ r)) sections sections
  | _, _, Forall₂.nil => Forall₂.cons Forall₂.nil Forall₂.nil
  | _, _, Forall₂.cons h₀ h₁ =>
    rel_bind (rel_sections h₁) fun _ _ hl => rel_map (fun _ _ ha => Forall₂.cons ha hl) h₀
#align list.rel_sections List.rel_sections

end List
