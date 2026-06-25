/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Data.List.Perm
public import Mathlib.Init

/-!
# The Following Are Equivalent

This file allows to state that all propositions in a list are equivalent. It is used by
`Mathlib/Tactic/Tfae.lean`.
`TFAE l` means `∀ x ∈ l, ∀ y ∈ l, x ↔ y`. This is equivalent to `Pairwise (↔) l`.
-/

@[expose] public section


namespace List

/-- TFAE: The Following (propositions) Are Equivalent.

The `tfae_have` and `tfae_finish` tactics can be useful in proofs with `TFAE` goals.
-/
def TFAE (l : List Prop) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x ↔ y

theorem tfae_nil : TFAE [] :=
  forall_mem_nil _

@[simp]
theorem tfae_singleton (p) : TFAE [p] := by simp [TFAE, -eq_iff_iff]

theorem TFAE.sublist {l₁ l₂ : List Prop} (h : TFAE l₂) (hl : l₁ <+ l₂) : TFAE l₁ :=
  fun p hp q hq => h p (hl.subset hp) q (hl.subset hq)

theorem tfae_congr {l₁ l₂ : List Prop} (hp : l₁.Perm l₂) : TFAE l₁ ↔ TFAE l₂ :=
  ⟨fun h p hp₁ q hp₂ => h p (hp.mem_iff.2 hp₁) q (hp.mem_iff.2 hp₂),
    fun h p hp₁ q hp₂ => h p (hp.mem_iff.1 hp₁) q (hp.mem_iff.1 hp₂)⟩

theorem tfae_append_of_mem {a b} {l₁ l₂ : List Prop} (ha : a ∈ l₁) (hb : b ∈ l₂) :
    TFAE (l₁ ++ l₂) ↔ (a ↔ b) ∧ TFAE l₁ ∧ TFAE l₂ where
  mp h := by
    refine ⟨h a (mem_append_left l₂ ha) b (mem_append_right l₁ hb), ?_, ?_⟩
    · exact h.sublist (sublist_append_left l₁ l₂)
    · exact h.sublist (sublist_append_right l₁ l₂)
  mpr := by
    rintro ⟨hab, h₁, h₂⟩ p hp q hq
    rcases mem_append.1 hp with hp | hp <;> rcases mem_append.1 hq with hq | hq
    · exact h₁ p hp q hq
    · exact (h₁ p hp a ha).trans (hab.trans (h₂ b hb q hq))
    · exact (h₂ p hp b hb).trans (hab.symm.trans (h₁ a ha q hq))
    · exact h₂ p hp q hq

theorem tfae_cons_of_mem {a b} {l : List Prop} (h : b ∈ l) :
    TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l := by
  simpa using tfae_append_of_mem (l₁ := [a]) (by simp) h

theorem tfae_append_singleton_of_mem {a b} {l : List Prop} (h : b ∈ l) :
    TFAE (l ++ [a]) ↔ (a ↔ b) ∧ TFAE l := by
  simp [tfae_append_of_mem (l₁ := l) (l₂ := [a]) (a := b) (b := a) h (by simp), iff_comm]

theorem tfae_cons_cons {a b} {l : List Prop} : TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l) :=
  tfae_cons_of_mem (Mem.head _)

@[simp]
theorem tfae_cons_self {a} {l : List Prop} : TFAE (a :: a :: l) ↔ TFAE (a :: l) := by
  simp [tfae_cons_cons]

theorem tfae_of_forall (b : Prop) (l : List Prop) (h : ∀ a ∈ l, a ↔ b) : TFAE l :=
  fun _a₁ h₁ _a₂ h₂ => (h _ h₁).trans (h _ h₂).symm

theorem tfae_of_cycle {a b} {l : List Prop} (h_chain : List.IsChain (· → ·) (a :: b :: l))
    (h_last : getLastD l b → a) : TFAE (a :: b :: l) := by
  induction l generalizing a b with
  | nil => simp_all [tfae_cons_cons, iff_def]
  | cons c l IH =>
    simp only [tfae_cons_cons, getLastD_cons, isChain_cons_cons] at *
    rcases h_chain with ⟨ab, ⟨bc, ch⟩⟩
    have := IH ⟨bc, ch⟩ (ab ∘ h_last)
    exact ⟨⟨ab, h_last ∘ (this.2 c (.head _) _ getLastD_mem_cons).1 ∘ bc⟩, this⟩

theorem TFAE.out {l} (h : TFAE l) (n₁ n₂ : Nat) {a b}
    (h₁ : l[n₁]? = some a := by rfl)
    (h₂ : l[n₂]? = some b := by rfl) :
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

theorem tfae_not_iff {l : List Prop} : TFAE (l.map Not) ↔ TFAE l := by
  classical
  simp only [TFAE, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Decidable.not_iff_not]

alias ⟨_, TFAE.not⟩ := tfae_not_iff

end List
