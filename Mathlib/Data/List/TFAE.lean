/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Data.List.Basic
public import Mathlib.Init

/-!
# The Following Are Equivalent

This file allows to state that all propositions in a list are equivalent. It is used by
`Mathlib/Tactic/Tfae.lean`.
-/

@[expose] public section


namespace List

variable {a b : Prop} {l l₁ l₂ : List Prop}

/-- TFAE: The Following (propositions) Are Equivalent.

The `tfae_have` and `tfae_finish` tactics can be useful in proofs with `TFAE` goals.
-/
def TFAE (l : List Prop) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x ↔ y

theorem tfae_nil : TFAE [] :=
  forall_mem_nil _

@[simp]
theorem tfae_singleton (p) : TFAE [p] := by simp [TFAE, -eq_iff_iff]

theorem TFAE.subset (h : TFAE l₂) (hl : l₁ ⊆ l₂) : TFAE l₁ :=
  fun p hp q hq ↦ h p (hl hp) q (hl hq)

theorem tfae_congr (h₁₂ : l₁ ⊆ l₂) (h₂₁ : l₂ ⊆ l₁) : TFAE l₁ ↔ TFAE l₂ :=
  ⟨fun h ↦ h.subset h₂₁, fun h ↦ h.subset h₁₂⟩

theorem Perm.tfae_iff (h : l₁ ~ l₂) : TFAE l₁ ↔ TFAE l₂ := tfae_congr h.subset h.symm.subset

@[simp]
theorem tfae_reverse : TFAE l.reverse ↔ TFAE l := (reverse_perm l).tfae_iff

theorem tfae_of_forall (h : ∀ a ∈ l, a ↔ b) : TFAE l :=
  fun _a₁ h₁ _a₂ h₂ => (h _ h₁).trans (h _ h₂).symm

/-- `(TFAE [P₁, P₂, P₃, ...]).out i j`, where `i`, `j` are the **1-indexed** indices for TFAE
statements, yields a proof of `Pᵢ ↔ Pⱼ`. Indices therefore must be greater than `0`. This
convention matches the statement numbering in `tfae` tactics. -/
theorem TFAE.out {l} (h : TFAE l) (i j : Nat) {a b}
    (h₁ : l[i - 1]? = some a := by rfl)
    (h₂ : l[j - 1]? = some b := by rfl)
    (_ : i ≠ 0 := by first | decide +kernel | fail "TFAE indices start at 1.")
    (_ : j ≠ 0 := by first | decide +kernel | fail "TFAE indices start at 1.") :
    a ↔ b :=
  h _ (List.mem_of_getElem? h₁) _ (List.mem_of_getElem? h₂)

/-- If `P₁ x ↔ ... ↔ Pₙ x` for all `x`, then `(∀ x, P₁ x) ↔ ... ↔ (∀ x, Pₙ x)`.
Note: in concrete cases, Lean has trouble finding the list `[P₁, ..., Pₙ]` from the list
`[(∀ x, P₁ x), ..., (∀ x, Pₙ x)]`, but simply providing a list of underscores with the right
length makes it happier.

Example:
```lean
example (P₁ P₂ P₃ : ℕ → Prop) (H : ∀ n, [P₁ n, P₂ n, P₃ n].TFAE) :
    [∀ n, P₁ n, ∀ n, P₂ n, ∀ n, P₃ n].TFAE :=
  forall_tfae [_, _, _] H
```
-/
theorem forall_tfae {α : Type*} (l : List (α → Prop)) (H : ∀ a : α, (l.map (fun p ↦ p a)).TFAE) :
    (l.map (fun p ↦ ∀ a, p a)).TFAE := by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact forall_congr' fun a ↦ H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

/-- If `P₁ x ↔ ... ↔ Pₙ x` for all `x`, then `(∃ x, P₁ x) ↔ ... ↔ (∃ x, Pₙ x)`.
Note: in concrete cases, Lean has trouble finding the list `[P₁, ..., Pₙ]` from the list
`[(∃ x, P₁ x), ..., (∃ x, Pₙ x)]`, but simply providing a list of underscores with the right
length makes it happier.

Example:
```lean
example (P₁ P₂ P₃ : ℕ → Prop) (H : ∀ n, [P₁ n, P₂ n, P₃ n].TFAE) :
    [∃ n, P₁ n, ∃ n, P₂ n, ∃ n, P₃ n].TFAE :=
  exists_tfae [_, _, _] H
```
-/
theorem exists_tfae {α : Type*} (l : List (α → Prop)) (H : ∀ a : α, (l.map (fun p ↦ p a)).TFAE) :
    (l.map (fun p ↦ ∃ a, p a)).TFAE := by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact exists_congr fun a ↦ H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

theorem tfae_not_iff : TFAE (l.map Not) ↔ TFAE l := by
  classical
  simp only [TFAE, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Decidable.not_iff_not]

alias ⟨_, TFAE.not⟩ := tfae_not_iff

end List
