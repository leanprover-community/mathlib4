/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Lex
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Relation

#align_import data.list.pairwise from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type*} {R S T : α → α → Prop} {a : α} {l : List α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff
#align list.pairwise_iff List.pairwise_iff

/-! ### Pairwise -/

#align list.pairwise.nil List.Pairwise.nil
#align list.pairwise.cons List.Pairwise.cons

theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1 _
#align list.rel_of_pairwise_cons List.rel_of_pairwise_cons

theorem Pairwise.of_cons (p : (a :: l).Pairwise R) : Pairwise R l :=
  (pairwise_cons.1 p).2
#align list.pairwise.of_cons List.Pairwise.of_cons

theorem Pairwise.tail : ∀ {l : List α} (_p : Pairwise R l), Pairwise R l.tail
  | [], h => h
  | _ :: _, h => h.of_cons
#align list.pairwise.tail List.Pairwise.tail

theorem Pairwise.drop : ∀ {l : List α} {n : ℕ}, List.Pairwise R l → List.Pairwise R (l.drop n)
  | _, 0, h => h
  | [], _ + 1, _ => List.Pairwise.nil
  | a :: l, n + 1, h => by rw [List.drop]; exact Pairwise.drop (pairwise_cons.mp h).right
                           -- ⊢ Pairwise R (List.drop n l)
                                           -- 🎉 no goals
#align list.pairwise.drop List.Pairwise.drop

theorem Pairwise.imp_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · exact BAll.imp_right (fun x h ↦ H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r
    · exact ih fun {a b} m m' ↦ H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')
#align list.pairwise.imp_of_mem List.Pairwise.imp_of_mem

#align list.pairwise.imp List.Pairwise.impₓ -- Implicits Order

theorem pairwise_and_iff : (l.Pairwise fun a b => R a b ∧ S a b) ↔ l.Pairwise R ∧ l.Pairwise S :=
  ⟨fun h => ⟨h.imp @fun a b h => h.1, h.imp @fun a b h => h.2⟩, fun ⟨hR, hS⟩ =>
    by induction' hR with a l R1 R2 IH <;> simp only [Pairwise.nil, pairwise_cons] at *
       -- ⊢ Pairwise (fun a b => R a b ∧ S a b) []
                                           -- 🎉 no goals
                                           -- ⊢ (∀ (a' : α), a' ∈ l → R a a' ∧ S a a') ∧ Pairwise (fun a b => R a b ∧ S a b) l
       exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH ⟨R2, hS.2⟩ hS.2⟩⟩
       -- 🎉 no goals
#align list.pairwise_and_iff List.pairwise_and_iff

theorem Pairwise.and (hR : l.Pairwise R) (hS : l.Pairwise S) :
    l.Pairwise fun a b => R a b ∧ S a b :=
  pairwise_and_iff.2 ⟨hR, hS⟩
#align list.pairwise.and List.Pairwise.and

theorem Pairwise.imp₂ (H : ∀ a b, R a b → S a b → T a b) (hR : l.Pairwise R) (hS : l.Pairwise S) :
    l.Pairwise T :=
  (hR.and hS).imp fun h => (H _ _ h.1 h.2)
#align list.pairwise.imp₂ List.Pairwise.imp₂

theorem Pairwise.iff_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : Pairwise R l ↔ Pairwise S l :=
  ⟨Pairwise.imp_of_mem fun {_ _} m m' ↦ (H m m').1,
   Pairwise.imp_of_mem fun {_ _} m m' ↦ (H m m').2⟩
#align list.pairwise.iff_of_mem List.Pairwise.iff_of_mem

theorem Pairwise.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Pairwise R l ↔ Pairwise S l :=
  Pairwise.iff_of_mem fun _ _ => H _ _
#align list.pairwise.iff List.Pairwise.iff

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l <;> [exact Pairwise.nil; simp only [*, pairwise_cons, forall₂_true_iff, and_true_iff]]
  -- 🎉 no goals
#align list.pairwise_of_forall List.pairwise_of_forall

theorem Pairwise.and_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  Pairwise.iff_of_mem
    (by simp (config := { contextual := true }) only [true_and_iff, iff_self_iff, forall₂_true_iff])
        -- 🎉 no goals
#align list.pairwise.and_mem List.Pairwise.and_mem

theorem Pairwise.imp_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l → y ∈ l → R x y) l :=
  Pairwise.iff_of_mem
    (by simp (config := { contextual := true }) only [forall_prop_of_true, iff_self_iff,
        forall₂_true_iff])
#align list.pairwise.imp_mem List.Pairwise.imp_mem

#align list.pairwise.sublist List.Pairwise.sublistₓ -- Implicits order

theorem Pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : l.Pairwise R)
    (h₃ : l.Pairwise (flip R)) : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y := by
  induction' l with a l ih
  -- ⊢ ∀ ⦃x : α⦄, x ∈ [] → ∀ ⦃y : α⦄, y ∈ [] → R x y
  · exact forall_mem_nil _
    -- 🎉 no goals
  rw [pairwise_cons] at h₂ h₃
  -- ⊢ ∀ ⦃x : α⦄, x ∈ a :: l → ∀ ⦃y : α⦄, y ∈ a :: l → R x y
  simp only [mem_cons]
  -- ⊢ ∀ ⦃x : α⦄, x = a ∨ x ∈ l → ∀ ⦃y : α⦄, y = a ∨ y ∈ l → R x y
  rintro x (rfl | hx) y (rfl | hy)
  · exact h₁ _ (l.mem_cons_self _)
    -- 🎉 no goals
  · exact h₂.1 _ hy
    -- 🎉 no goals
  · exact h₃.1 _ hx
    -- 🎉 no goals
  · exact ih (fun x hx => h₁ _ <| mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy
    -- 🎉 no goals
#align list.pairwise.forall_of_forall_of_flip List.Pairwise.forall_of_forall_of_flip

theorem Pairwise.forall_of_forall (H : Symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [H.flip_eq]
                                       -- 🎉 no goals
#align list.pairwise.forall_of_forall List.Pairwise.forall_of_forall

theorem Pairwise.forall (hR : Symmetric R) (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  apply Pairwise.forall_of_forall
  · exact fun a b h hne => hR (h hne.symm)
    -- 🎉 no goals
  · exact fun _ _ hx => (hx rfl).elim
    -- 🎉 no goals
  · exact hl.imp (@fun a b h _ => by exact h)
    -- 🎉 no goals
#align list.pairwise.forall List.Pairwise.forall

theorem Pairwise.set_pairwise (hl : Pairwise R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr
#align list.pairwise.set_pairwise List.Pairwise.set_pairwise

theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by
  simp [Pairwise.nil]
  -- 🎉 no goals
#align list.pairwise_singleton List.pairwise_singleton

theorem pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp only [pairwise_cons, mem_singleton, forall_eq, forall_prop_of_false (not_mem_nil _),
    forall_true_iff, Pairwise.nil, and_true_iff]
#align list.pairwise_pair List.pairwise_pair

#align list.pairwise_append List.pairwise_append

theorem pairwise_append_comm (s : Symmetric R) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have : ∀ l₁ l₂ : List α, (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) →
    ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y := fun l₁ l₂ a x xm y ym ↦ s (a y ym x xm)
  simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]
  -- ⊢ (Pairwise R l₁ ∧ Pairwise R l₂ ∧ ∀ (a : α), a ∈ l₁ → ∀ (b : α), b ∈ l₂ → R a …
                                              -- 🎉 no goals
#align list.pairwise_append_comm List.pairwise_append_comm

theorem pairwise_middle (s : Symmetric R) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂) by
    rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
    -- ⊢ (Pairwise R ([a] ++ l₁) ∧ Pairwise R l₂ ∧ ∀ (a_1 : α), a_1 ∈ l₁ ++ [a] → ∀ ( …
    simp only [mem_append, or_comm]
    -- 🎉 no goals
#align list.pairwise_middle List.pairwise_middle

-- Porting note: Duplicate of `pairwise_map` but with `f` explicit.
@[deprecated] theorem pairwise_map' (f : β → α) :
    ∀ {l : List β}, Pairwise R (map f l) ↔ Pairwise (fun a b : β => R (f a) (f b)) l
  | [] => by simp only [map, Pairwise.nil]
             -- 🎉 no goals
  | b :: l => by
    simp only [map, pairwise_cons, mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, pairwise_map]
#align list.pairwise_map List.pairwise_map'

theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwise S (map f l)) : Pairwise R l :=
  (pairwise_map.1 p).imp (H _ _)
#align list.pairwise.of_map List.Pairwise.of_map

theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    (p : Pairwise R l) : Pairwise S (map f l) :=
  pairwise_map.2 <| p.imp (H _ _)
#align list.pairwise.map List.Pairwise.map

theorem pairwise_filterMap (f : β → Option α) {l : List β} :
    Pairwise R (filterMap f l) ↔ Pairwise (fun a a' : β => ∀ b ∈ f a, ∀ b' ∈ f a', R b b') l := by
  let _S (a a' : β) := ∀ b ∈ f a, ∀ b' ∈ f a', R b b'
  -- ⊢ Pairwise R (filterMap f l) ↔ Pairwise (fun a a' => ∀ (b : α), b ∈ f a → ∀ (b …
  simp only [Option.mem_def]; induction' l with a l IH
  -- ⊢ Pairwise R (filterMap f l) ↔ Pairwise (fun a a' => ∀ (b : α), f a = some b → …
                              -- ⊢ Pairwise R (filterMap f []) ↔ Pairwise (fun a a' => ∀ (b : α), f a = some b  …
  · simp only [filterMap, Pairwise.nil]
    -- 🎉 no goals
  cases' e : f a with b
  -- ⊢ Pairwise R (filterMap f (a :: l)) ↔ Pairwise (fun a a' => ∀ (b : α), f a = s …
  · --Porting note: Why do I need `propext IH` here?
    rw [filterMap_cons_none _ _ e, propext IH, pairwise_cons]
    -- ⊢ Pairwise (fun a a' => ∀ (b : α), f a = some b → ∀ (b' : α), f a' = some b' → …
    simp only [e, forall_prop_of_false not_false, forall₃_true_iff, true_and_iff]
    -- 🎉 no goals
  rw [filterMap_cons_some _ _ _ e]
  -- ⊢ Pairwise R (b :: filterMap f l) ↔ Pairwise (fun a a' => ∀ (b : α), f a = som …
  simp only [pairwise_cons, mem_filterMap, forall_exists_index, and_imp, IH, e, Option.some.injEq,
    forall_eq', and_congr_left_iff]
  intro _
  -- ⊢ (∀ (a' : α) (x : β), x ∈ l → f x = some a' → R b a') ↔ ∀ (a' : β), a' ∈ l →  …
  exact ⟨fun h a ha b hab => h _ _ ha hab, fun h a b ha hab => h _ ha _ hab⟩
  -- 🎉 no goals
#align list.pairwise_filter_map List.pairwise_filterMap

theorem Pairwise.filter_map {S : β → β → Prop} (f : α → Option β)
    (H : ∀ a a' : α, R a a' → ∀ b ∈ f a, ∀ b' ∈ f a', S b b') {l : List α} (p : Pairwise R l) :
    Pairwise S (filterMap f l) :=
  (pairwise_filterMap _).2 <| p.imp (H _ _)
#align list.pairwise.filter_map List.Pairwise.filter_map

theorem pairwise_filter (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter, pairwise_filterMap]
  -- ⊢ Pairwise (fun a a' => ∀ (b : α), b ∈ Option.guard (fun x => decide (p x) = t …
  apply Pairwise.iff; intros
  -- ⊢ ∀ (a b : α), (∀ (b_1 : α), b_1 ∈ Option.guard (fun x => decide (p x) = true) …
                      -- ⊢ (∀ (b : α), b ∈ Option.guard (fun x => decide (p x) = true) a✝ → ∀ (b' : α), …
  simp only [decide_eq_true_eq, Option.mem_def, Option.guard_eq_some, and_imp, forall_eq']
  -- 🎉 no goals
#align list.pairwise_filter List.pairwise_filter

--Porting note: changed Prop to Bool
theorem Pairwise.filter (p : α → Bool) : Pairwise R l → Pairwise R (filter p l) :=
  Pairwise.sublist (filter_sublist _)
#align list.pairwise.filter List.Pairwise.filterₓ

theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀ x ∈ l, p x) :
    Pairwise R (l.pmap f h) ↔
      Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l := by
  induction' l with a l ihl
  -- ⊢ Pairwise R (pmap f [] h) ↔ Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), …
  · simp
    -- 🎉 no goals
  obtain ⟨_, hl⟩ : p a ∧ ∀ b, b ∈ l → p b := by simpa using h
  -- ⊢ Pairwise R (pmap f (a :: l) h) ↔ Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ :  …
  simp only [ihl hl, pairwise_cons, bex_imp, pmap, and_congr_left_iff, mem_pmap]
  -- ⊢ Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l → …
  refine' fun _ => ⟨fun H b hb _ hpb => H _ _ hb rfl, _⟩
  -- ⊢ (∀ (a' : β), a' ∈ l → ∀ (h₁ : p a) (h₂ : p a'), R (f a h₁) (f a' h₂)) → ∀ (a …
  rintro H _ b hb rfl
  -- ⊢ R (f a (_ : p a)) (f b (_ : p b))
  exact H b hb _ _
  -- 🎉 no goals
#align list.pairwise_pmap List.pairwise_pmap

theorem Pairwise.pmap {l : List α} (hl : Pairwise R l) {p : α → Prop} {f : ∀ a, p a → β}
    (h : ∀ x ∈ l, p x) {S : β → β → Prop}
    (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) :
    Pairwise S (l.pmap f h) := by
  refine' (pairwise_pmap h).2 (Pairwise.imp_of_mem _ hl)
  -- ⊢ ∀ {a b : α}, a ∈ l → b ∈ l → R a b → ∀ (h₁ : p a) (h₂ : p b), S (f a h₁) (f  …
  intros; apply hS; assumption
  -- ⊢ S (f a✝³ h₁✝) (f b✝ h₂✝)
          -- ⊢ R a✝³ b✝
                    -- 🎉 no goals
#align list.pairwise.pmap List.Pairwise.pmap

theorem pairwise_join {L : List (List α)} :
    Pairwise R (join L) ↔
      (∀ l ∈ L, Pairwise R l) ∧ Pairwise (fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, R x y) L := by
  induction' L with l L IH
  -- ⊢ Pairwise R (join []) ↔ (∀ (l : List α), l ∈ [] → Pairwise R l) ∧ Pairwise (f …
  · simp only [join, Pairwise.nil, forall_prop_of_false (not_mem_nil _), forall_const, and_self_iff]
    -- 🎉 no goals
  have :
    (∀ x : α, x ∈ l → ∀ (y : α) (x_1 : List α), x_1 ∈ L → y ∈ x_1 → R x y) ↔
      ∀ a' : List α, a' ∈ L → ∀ x : α, x ∈ l → ∀ y : α, y ∈ a' → R x y :=
    ⟨fun h a b c d e => h c d e a b, fun h c d e a b => h a b c d e⟩
  simp only [join, pairwise_append, IH, mem_join, exists_imp, and_imp, this, forall_mem_cons,
    pairwise_cons]
  simp only [and_assoc, and_comm, and_left_comm]
  -- 🎉 no goals
#align list.pairwise_join List.pairwise_join

theorem pairwise_bind {R : β → β → Prop} {l : List α} {f : α → List β} :
    List.Pairwise R (l.bind f) ↔
      (∀ a ∈ l, Pairwise R (f a)) ∧ Pairwise (fun a₁ a₂ => ∀ x ∈ f a₁, ∀ y ∈ f a₂, R x y) l :=
  by simp [List.bind, List.pairwise_join, List.mem_map, List.pairwise_map]
     -- 🎉 no goals
#align list.pairwise_bind List.pairwise_bind

#align list.pairwise_reverse List.pairwise_reverse

theorem pairwise_of_reflexive_on_dupl_of_forall_ne [DecidableEq α] {l : List α} {r : α → α → Prop}
    (hr : ∀ a, 1 < count a l → r a a) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  induction' l with hd tl IH
  -- ⊢ Pairwise r []
  · simp
    -- 🎉 no goals
  · rw [List.pairwise_cons]
    -- ⊢ (∀ (a' : α), a' ∈ tl → r hd a') ∧ Pairwise r tl
    constructor
    -- ⊢ ∀ (a' : α), a' ∈ tl → r hd a'
    · intro x hx
      -- ⊢ r hd x
      by_cases H : hd = x
      -- ⊢ r hd x
      · rw [H]
        -- ⊢ r x x
        refine' hr _ _
        -- ⊢ 1 < count x (hd :: tl)
        simpa [count_cons, H, Nat.succ_lt_succ_iff, count_pos_iff_mem] using hx
        -- 🎉 no goals
      · exact h hd (mem_cons_self _ _) x (mem_cons_of_mem _ hx) H
        -- 🎉 no goals
    · refine' IH _ _
      -- ⊢ ∀ (a : α), 1 < count a tl → r a a
      · intro x hx
        -- ⊢ r x x
        refine' hr _ _
        -- ⊢ 1 < count x (hd :: tl)
        rw [count_cons]
        -- ⊢ 1 < count x tl + if x = hd then 1 else 0
        split_ifs
        -- ⊢ 1 < count x tl + 1
        · exact hx.trans (Nat.lt_succ_self _)
          -- 🎉 no goals
        · exact hx
          -- 🎉 no goals
      · intro x hx y hy
        -- ⊢ x ≠ y → r x y
        exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)
        -- 🎉 no goals
#align list.pairwise_of_reflexive_on_dupl_of_forall_ne List.pairwise_of_reflexive_on_dupl_of_forall_ne

theorem pairwise_of_forall_mem_list {l : List α} {r : α → α → Prop} (h : ∀ a ∈ l, ∀ b ∈ l, r a b) :
    l.Pairwise r := by
  classical
    refine'
      pairwise_of_reflexive_on_dupl_of_forall_ne (fun a ha' => _) fun a ha b hb _ => h a ha b hb
    have ha := List.count_pos_iff_mem.1 ha'.le
    exact h a ha a ha
#align list.pairwise_of_forall_mem_list List.pairwise_of_forall_mem_list

theorem pairwise_of_reflexive_of_forall_ne {l : List α} {r : α → α → Prop} (hr : Reflexive r)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  classical exact pairwise_of_reflexive_on_dupl_of_forall_ne (fun _ _ => hr _) h
  -- 🎉 no goals
#align list.pairwise_of_reflexive_of_forall_ne List.pairwise_of_reflexive_of_forall_ne

theorem pairwise_iff_get : ∀ {l : List α}, Pairwise R l ↔
    ∀ (i j) (_hij : i < j), R (get l i) (get l j)
  | [] => by
    simp only [Pairwise.nil, true_iff_iff]; exact fun i j _h => (Nat.not_lt_zero j).elim j.2
    -- ⊢ ∀ (i j : Fin (length [])), i < j → R (get [] i) (get [] j)
                                            -- 🎉 no goals
  | a :: l => by
    rw [pairwise_cons, pairwise_iff_get]
    -- ⊢ ((∀ (a' : α), a' ∈ l → R a a') ∧ ∀ (i j : Fin (length l)), i < j → R (get l  …
    refine'
      ⟨fun H i j hij => _, fun H =>
        ⟨fun a' m => _, fun i j hij => _⟩⟩
    · cases' j with j hj
      -- ⊢ R (get (a :: l) i) (get (a :: l) { val := j, isLt := hj })
      cases' j with j
      -- ⊢ R (get (a :: l) i) (get (a :: l) { val := zero, isLt := hj })
      · exact (Nat.not_lt_zero _).elim hij
        -- 🎉 no goals
      cases' i with i hi
      -- ⊢ R (get (a :: l) { val := i, isLt := hi }) (get (a :: l) { val := succ j, isL …
      cases' i with i
      -- ⊢ R (get (a :: l) { val := zero, isLt := hi }) (get (a :: l) { val := succ j,  …
      · exact H.1 _ (get_mem l _ _)
        -- 🎉 no goals
      · exact H.2 _ _ (Nat.lt_of_succ_lt_succ hij)
        -- 🎉 no goals
    · rcases get_of_mem m with ⟨n, h, rfl⟩
      -- ⊢ R a (get l n)
      have := H ⟨0, show 0 < (a::l).length from Nat.succ_pos _⟩ ⟨n.succ, Nat.succ_lt_succ n.2⟩
        (Nat.succ_pos n)
      simpa
      -- 🎉 no goals
    · simpa using H i.succ j.succ (show i.1.succ < j.1.succ from Nat.succ_lt_succ hij)
      -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated pairwise_iff_get]
theorem pairwise_iff_nthLe {R} {l : List α} : Pairwise R l ↔
    ∀ (i j) (h₁ : j < length l) (h₂ : i < j), R (nthLe l i (lt_trans h₂ h₁)) (nthLe l j h₁) :=
  pairwise_iff_get.trans
    ⟨fun h i j _ h₂ => h ⟨i, _⟩ ⟨j, _⟩ h₂,
     fun h i j hij => h i j _ hij⟩
#align list.pairwise_iff_nth_le List.pairwise_iff_nthLe

theorem pairwise_replicate {α : Type*} {r : α → α → Prop} {x : α} (hx : r x x) :
    ∀ n : ℕ, Pairwise r (List.replicate n x)
  | 0 => by simp
            -- 🎉 no goals
  | n + 1 => by simp only [replicate, add_eq, add_zero, pairwise_cons, mem_replicate, ne_eq,
    and_imp, forall_eq_apply_imp_iff', hx, implies_true, pairwise_replicate hx n, and_self]
#align list.pairwise_replicate List.pairwise_replicate

/-! ### Pairwise filtering -/


variable [DecidableRel R]

@[simp]
theorem pwFilter_nil : pwFilter R [] = [] :=
  rfl
#align list.pw_filter_nil List.pwFilter_nil

@[simp]
theorem pwFilter_cons_of_pos {a : α} {l : List α} (h : ∀ b ∈ pwFilter R l, R a b) :
    pwFilter R (a :: l) = a :: pwFilter R l :=
  if_pos h
#align list.pw_filter_cons_of_pos List.pwFilter_cons_of_pos

@[simp]
theorem pwFilter_cons_of_neg {a : α} {l : List α} (h : ¬∀ b ∈ pwFilter R l, R a b) :
    pwFilter R (a :: l) = pwFilter R l :=
  if_neg h
#align list.pw_filter_cons_of_neg List.pwFilter_cons_of_neg

theorem pwFilter_map (f : β → α) :
    ∀ l : List β, pwFilter R (map f l) = map f (pwFilter (fun x y => R (f x) (f y)) l)
  | [] => rfl
  | x :: xs =>
    if h : ∀ b ∈ pwFilter R (map f xs), R (f x) b then by
      have h' : ∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun b hb => h _ (by rw [pwFilter_map f xs]; apply mem_map_of_mem _ hb)
      rw [map, pwFilter_cons_of_pos h, pwFilter_cons_of_pos h', pwFilter_map f xs, map]
      -- 🎉 no goals
    else by
      have h' : ¬∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun hh =>
        h fun a ha => by
          rw [pwFilter_map f xs, mem_map] at ha
          rcases ha with ⟨b, hb₀, hb₁⟩
          subst a
          exact hh _ hb₀
      rw [map, pwFilter_cons_of_neg h, pwFilter_cons_of_neg h', pwFilter_map f xs]
      -- 🎉 no goals
#align list.pw_filter_map List.pwFilter_map

theorem pwFilter_sublist : ∀ l : List α, pwFilter R l <+ l
  | [] => nil_sublist _
  | x :: l => by
    by_cases h : ∀ y ∈ pwFilter R l, R x y
    -- ⊢ pwFilter R (x :: l) <+ x :: l
    · rw [pwFilter_cons_of_pos h]
      -- ⊢ x :: pwFilter R l <+ x :: l
      exact (pwFilter_sublist l).cons_cons _
      -- 🎉 no goals
    · rw [pwFilter_cons_of_neg h]
      -- ⊢ pwFilter R l <+ x :: l
      exact sublist_cons_of_sublist _ (pwFilter_sublist l)
      -- 🎉 no goals
#align list.pw_filter_sublist List.pwFilter_sublist

theorem pwFilter_subset (l : List α) : pwFilter R l ⊆ l :=
  (pwFilter_sublist _).subset
#align list.pw_filter_subset List.pwFilter_subset

theorem pairwise_pwFilter : ∀ l : List α, Pairwise R (pwFilter R l)
  | [] => Pairwise.nil
  | x :: l => by
    by_cases h : ∀ y ∈ pwFilter R l, R x y
    -- ⊢ Pairwise R (pwFilter R (x :: l))
    · rw [pwFilter_cons_of_pos h]
      -- ⊢ Pairwise R (x :: pwFilter R l)
      exact pairwise_cons.2 ⟨h, pairwise_pwFilter l⟩
      -- 🎉 no goals
    · rw [pwFilter_cons_of_neg h]
      -- ⊢ Pairwise R (pwFilter R l)
      exact pairwise_pwFilter l
      -- 🎉 no goals
#align list.pairwise_pw_filter List.pairwise_pwFilter

theorem pwFilter_eq_self {l : List α} : pwFilter R l = l ↔ Pairwise R l :=
  ⟨fun e => e ▸ pairwise_pwFilter l, fun p => by
    induction' l with x l IH; · rfl
    -- ⊢ pwFilter R [] = []
                                -- 🎉 no goals
    cases' pairwise_cons.1 p with al p
    -- ⊢ pwFilter R (x :: l) = x :: l
    rw [pwFilter_cons_of_pos (BAll.imp_left (pwFilter_subset l) al), IH p]⟩
    -- 🎉 no goals
#align list.pw_filter_eq_self List.pwFilter_eq_self

alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self
#align list.pairwise.pw_filter List.Pairwise.pwFilter

-- Porting note: commented out
-- attribute [protected] List.Pairwise.pwFilter

@[simp]
theorem pwFilter_idempotent : pwFilter R (pwFilter R l) = pwFilter R l :=
  (pairwise_pwFilter l).pwFilter
#align list.pw_filter_idempotent List.pwFilter_idempotent

theorem forall_mem_pwFilter (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z) (a : α) (l : List α) :
    (∀ b ∈ pwFilter R l, R a b) ↔ ∀ b ∈ l, R a b :=
  ⟨by
    induction' l with x l IH; · exact fun _ _ h => (not_mem_nil _ h).elim
    -- ⊢ (∀ (b : α), b ∈ pwFilter R [] → R a b) → ∀ (b : α), b ∈ [] → R a b
                                -- 🎉 no goals
    simp only [forall_mem_cons]
    -- ⊢ (∀ (b : α), b ∈ pwFilter R (x :: l) → R a b) → R a x ∧ ∀ (x : α), x ∈ l → R  …
    by_cases h : ∀ y ∈ pwFilter R l, R x y
    -- ⊢ (∀ (b : α), b ∈ pwFilter R (x :: l) → R a b) → R a x ∧ ∀ (x : α), x ∈ l → R  …
    · simp only [pwFilter_cons_of_pos h, forall_mem_cons, and_imp]
      -- ⊢ R a x → (∀ (x : α), x ∈ pwFilter R l → R a x) → R a x ∧ ∀ (x : α), x ∈ l → R …
      exact fun r H => ⟨r, IH H⟩
      -- 🎉 no goals
    · rw [pwFilter_cons_of_neg h]
      -- ⊢ (∀ (b : α), b ∈ pwFilter R l → R a b) → R a x ∧ ∀ (x : α), x ∈ l → R a x
      refine' fun H => ⟨_, IH H⟩
      -- ⊢ R a x
      cases' e : find? (fun y => ¬R x y) (pwFilter R l) with k
      -- ⊢ R a x
      · refine' h.elim (BAll.imp_right _ (find?_eq_none.1 e))
        -- ⊢ ∀ (x_1 : α), x_1 ∈ pwFilter R l → ¬(decide ¬R x x_1) = true → R x x_1
        exact fun y _ => by simp
        -- 🎉 no goals
      · have := find?_some e
        -- ⊢ R a x
        exact (neg_trans (H k (find?_mem e))).resolve_right (by simpa),
        -- 🎉 no goals
          BAll.imp_left (pwFilter_subset l)⟩
#align list.forall_mem_pw_filter List.forall_mem_pwFilter

end List
