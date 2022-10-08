/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# Pairwise relations on a list
-/

namespace List

variable {α β : Type _} {R S T : α → α → Prop} {a : α} {l : List α}

theorem pairwise_append {l₁ l₂ : List α} : Pairwise R (l₁ ++ l₂) ↔
    Pairwise R l₁ ∧ Pairwise R l₂ ∧ (∀ x, x ∈ l₁ → ∀ y, y ∈ l₂ → R x y) := by
  induction l₁ with
  | nil => simp [Pairwise.nil]
  | cons a l₁ ih =>
    simp only [cons_append, Pairwise_cons, forall_mem_append, ih, forall_mem_cons,
      forall_and_distrib, and_assoc, And.left_comm]
    rfl

theorem pairwise_append_comm (s : symmetric R) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have : ∀ l₁ l₂ : List α, (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) →
    ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y := fun l₁ l₂ a x xm y ym => s (a y ym x xm)
  simp only [pairwise_append, And.left_comm] <;> rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

theorem pairwise_middle (s : symmetric R) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂) by
    rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
    simp only [mem_append, or_comm]
    rfl

theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by
  simp [Pairwise.nil]

theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (Pairwise_cons.1 p).1 _

theorem Pairwise.imp_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · exact Ball.imp_right (fun x h => H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r
    · exact ih fun {a b} m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')

theorem Pairwise.imp (H : ∀ a b, R a b → S a b) : Pairwise R l → Pairwise S l :=
  Pairwise.imp_of_mem fun {a b} _ _ => H a b

theorem pairwise_map (f : β → α) :
    ∀ {l : List β}, Pairwise R (map f l) ↔ Pairwise (fun a b : β => R (f a) (f b)) l
  | [] => by
    simp only [map, Pairwise.nil]
  | b :: l => by
    have : (∀ a b', b' ∈ l → a = f b' → R (f b) a) ↔ ∀ b' : β, b' ∈ l → R (f b) (f b') :=
      forall_swap.trans <| forall_congr' fun a => forall_swap.trans <| by
        simp only [forall_eq]
        rfl
    simp only [Pairwise_cons, map, pairwise_map, mem_map, exists_imp_distrib, and_imp, this]
    rfl

theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwise S (map f l)) : Pairwise R l :=
  ((pairwise_map f).1 p).imp H

theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    (p : Pairwise R l) : Pairwise S (map f l) :=
  (pairwise_map f).2 <| p.imp H

theorem Pairwise.iff_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : Pairwise R l ↔ Pairwise S l :=
  ⟨Pairwise.imp_of_mem fun {_ _} m m' => (H m m').1,
   Pairwise.imp_of_mem fun {_ _} m m' => (H m m').2⟩

theorem Pairwise.and_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  Pairwise.iff_of_mem (by simp (config := { contextual := true }))
