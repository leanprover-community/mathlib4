/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
import Mathlib.Data.List.Basic
import Mathlib.Init.Data.List.Basic

#align_import data.list.tfae from "leanprover-community/mathlib"@"5a3e819569b0f12cbec59d740a2613018e7b8eec"

/-!
# The Following Are Equivalent

This file allows to state that all propositions in a list are equivalent. It is used by
`Mathlib.Tactic.Tfae`.
`TFAE l` means `∀ x ∈ l, ∀ y ∈ l, x ↔ y`. This is equivalent to `Pairwise (↔) l`.
-/


namespace List

/-- TFAE: The Following (propositions) Are Equivalent.

The `tfae_have` and `tfae_finish` tactics can be useful in proofs with `TFAE` goals.
-/
def TFAE (l : List Prop) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x ↔ y
#align list.tfae List.TFAE

theorem tfae_nil : TFAE [] :=
  forall_mem_nil _
#align list.tfae_nil List.tfae_nil

theorem tfae_singleton (p) : TFAE [p] := by simp [TFAE, -eq_iff_iff]
                                            -- 🎉 no goals
#align list.tfae_singleton List.tfae_singleton

theorem tfae_cons_of_mem {a b} {l : List Prop} (h : b ∈ l) : TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l :=
  ⟨fun H => ⟨H a (by simp) b (Mem.tail a h),
                     -- 🎉 no goals
    fun p hp q hq => H _ (Mem.tail a hp) _ (Mem.tail a hq)⟩,
      by
        rintro ⟨ab, H⟩ p (_ | ⟨_, hp⟩) q (_ | ⟨_, hq⟩)
        · rfl
          -- 🎉 no goals
        · exact ab.trans (H _ h _ hq)
          -- 🎉 no goals
        · exact (ab.trans (H _ h _ hp)).symm
          -- 🎉 no goals
        · exact H _ hp _ hq⟩
          -- 🎉 no goals
#align list.tfae_cons_of_mem List.tfae_cons_of_mem

theorem tfae_cons_cons {a b} {l : List Prop} : TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l) :=
  tfae_cons_of_mem (Mem.head _)
#align list.tfae_cons_cons List.tfae_cons_cons

theorem tfae_of_forall (b : Prop) (l : List Prop) (h : ∀ a ∈ l, a ↔ b) : TFAE l :=
  fun _a₁ h₁ _a₂ h₂ => (h _ h₁).trans (h _ h₂).symm
#align list.tfae_of_forall List.tfae_of_forall

theorem tfae_of_cycle {a b} {l : List Prop} :
    List.Chain (· → ·) a (b :: l) → (ilast' b l → a) → TFAE (a :: b :: l) := by
  induction' l with c l IH generalizing a b <;>
  -- ⊢ Chain (fun x x_1 => x → x_1) a [b] → (ilast' b [] → a) → TFAE [a, b]
    simp only [tfae_cons_cons, tfae_singleton, and_true_iff, chain_cons, Chain.nil] at *
    -- ⊢ (a → b) → (ilast' b [] → a) → (a ↔ b)
    -- ⊢ (a → b) ∧ (b → c) ∧ Chain (fun x x_1 => x → x_1) c l → (ilast' b (c :: l) →  …
  · intro a b
    -- ⊢ a✝ ↔ b✝
    exact Iff.intro a b
    -- 🎉 no goals
  rintro ⟨ab, ⟨bc, ch⟩⟩ la
  -- ⊢ (a ↔ b) ∧ (b ↔ c) ∧ TFAE (c :: l)
  have := IH ⟨bc, ch⟩ (ab ∘ la)
  -- ⊢ (a ↔ b) ∧ (b ↔ c) ∧ TFAE (c :: l)
  exact ⟨⟨ab, la ∘ (this.2 c (Mem.head _) _ (ilast'_mem _ _)).1 ∘ bc⟩, this⟩
  -- 🎉 no goals
#align list.tfae_of_cycle List.tfae_of_cycle

theorem TFAE.out {l} (h : TFAE l) (n₁ n₂) {a b} (h₁ : List.get? l n₁ = some a := by rfl)
    (h₂ : List.get? l n₂ = some b := by rfl) : a ↔ b :=
  h _ (List.get?_mem h₁) _ (List.get?_mem h₂)
#align list.tfae.out List.TFAE.out

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
  simp_rw [TFAE, List.forall_mem_map_iff]
  -- ⊢ ∀ (j : α → Prop), j ∈ l → ∀ (j_1 : α → Prop), j_1 ∈ l → ((∀ (a : α), j a) ↔  …
  intros p₁ hp₁ p₂ hp₂
  -- ⊢ (∀ (a : α), p₁ a) ↔ ∀ (a : α), p₂ a
  exact forall_congr' fun a ↦ H a (p₁ a) (mem_map_of_mem (fun p ↦ p a) hp₁)
    (p₂ a) (mem_map_of_mem (fun p ↦ p a) hp₂)

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
  simp_rw [TFAE, List.forall_mem_map_iff]
  -- ⊢ ∀ (j : α → Prop), j ∈ l → ∀ (j_1 : α → Prop), j_1 ∈ l → ((∃ a, j a) ↔ ∃ a, j …
  intros p₁ hp₁ p₂ hp₂
  -- ⊢ (∃ a, p₁ a) ↔ ∃ a, p₂ a
  exact exists_congr fun a ↦ H a (p₁ a) (mem_map_of_mem (fun p ↦ p a) hp₁)
    (p₂ a) (mem_map_of_mem (fun p ↦ p a) hp₂)

end List
