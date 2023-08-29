/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Perm

#align_import data.list.sublists from "leanprover-community/mathlib"@"ccad6d5093bd2f5c6ca621fc74674cce51355af6"

/-! # sublists

`List.Sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
-/
/-
Porting note: various auxiliary definitions such as `sublists'_aux` were left out of the port
because they were only used to prove properties of `sublists`, and these proofs have changed.
-/
universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Nat

namespace List

/-! ### sublists -/

@[simp]
theorem sublists'_nil : sublists' (@nil α) = [[]] :=
  rfl
#align list.sublists'_nil List.sublists'_nil

@[simp]
theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] :=
  rfl
#align list.sublists'_singleton List.sublists'_singleton

#noalign list.map_sublists'_aux
#noalign list.sublists'_aux_append
#noalign list.sublists'_aux_eq_sublists'

--Porting note: Not the same as `sublists'_aux` from Lean3
/-- Auxiliary helper definition for `sublists'` -/
def sublists'Aux (a : α) (r₁ r₂ : List (List α)) : List (List α) :=
  r₁.foldl (init := r₂) fun r l => r ++ [a :: l]
#align list.sublists'_aux List.sublists'Aux

theorem sublists'Aux_eq_array_foldl (a : α) : ∀ (r₁ r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = ((r₁.toArray).foldl (init := r₂.toArray)
      (fun r l => r.push (a :: l))).toList := by
  intro r₁ r₂
  -- ⊢ sublists'Aux a r₁ r₂ = Array.toList (Array.foldl (fun r l => Array.push r (a …
  rw [sublists'Aux, Array.foldl_eq_foldl_data]
  -- ⊢ foldl (fun r l => r ++ [a :: l]) r₂ r₁ = Array.toList (foldl (fun r l => Arr …
  have := List.foldl_hom Array.toList (fun r l => r.push (a :: l))
    (fun r l => r ++ [a :: l]) r₁ r₂.toArray (by simp)
  simpa using this
  -- 🎉 no goals

theorem sublists'_eq_sublists'Aux (l : List α) :
    sublists' l = l.foldr (fun a r => sublists'Aux a r r) [[]] := by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  -- ⊢ Array.toList (foldr (fun a arr => Array.foldl (fun r l => Array.push r (a :: …
  rw [← List.foldr_hom Array.toList]
  · rfl
    -- 🎉 no goals
  · intros _ _; congr <;> simp
    -- ⊢ Array.toList (Array.foldl (fun r l => Array.push r (x✝ :: l)) (toArray (Arra …
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals

theorem sublists'Aux_eq_map (a : α) (r₁ : List (List α)) : ∀ (r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = r₂ ++ map (cons a) r₁ :=
  List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) <| fun r₁ l ih r₂ => by
                                    -- 🎉 no goals
    rw [map_append, map_singleton, ← append_assoc, ← ih, sublists'Aux, foldl_append, foldl]
    -- ⊢ foldl (fun r l => r ++ [a :: l]) (foldl (fun r l => r ++ [a :: l]) r₂ r₁ ++  …
    simp [sublists'Aux]
    -- 🎉 no goals

-- Porting note: simp can prove `sublists'_singleton`
@[simp 900]
theorem sublists'_cons (a : α) (l : List α) :
    sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]
  -- 🎉 no goals
#align list.sublists'_cons List.sublists'_cons

@[simp]
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t := by
  induction' t with a t IH generalizing s
  -- ⊢ s ∈ sublists' [] ↔ s <+ []
  · simp only [sublists'_nil, mem_singleton]
    -- ⊢ s = [] ↔ s <+ []
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
    -- 🎉 no goals
  simp only [sublists'_cons, mem_append, IH, mem_map]
  -- ⊢ (s <+ t ∨ ∃ a_1, a_1 <+ t ∧ a :: a_1 = s) ↔ s <+ a :: t
  constructor <;> intro h; rcases h with (h | ⟨s, h, rfl⟩)
  -- ⊢ (s <+ t ∨ ∃ a_1, a_1 <+ t ∧ a :: a_1 = s) → s <+ a :: t
                  -- ⊢ s <+ a :: t
                  -- ⊢ s <+ t ∨ ∃ a_1, a_1 <+ t ∧ a :: a_1 = s
  · exact sublist_cons_of_sublist _ h
    -- 🎉 no goals
  · exact h.cons_cons _
    -- 🎉 no goals
  · cases' h with _ _ _ h s _ _ h
    -- ⊢ s <+ t ∨ ∃ a_1, a_1 <+ t ∧ a :: a_1 = s
    · exact Or.inl h
      -- 🎉 no goals
    · exact Or.inr ⟨s, h, rfl⟩
      -- 🎉 no goals
#align list.mem_sublists' List.mem_sublists'

@[simp]
theorem length_sublists' : ∀ l : List α, length (sublists' l) = 2 ^ length l
  | [] => rfl
  | a :: l => by
    simp_arith only [sublists'_cons, length_append, length_sublists' l,
      length_map, length, Nat.pow_succ', mul_succ, mul_zero, zero_add]
#align list.length_sublists' List.length_sublists'

@[simp]
theorem sublists_nil : sublists (@nil α) = [[]] :=
  rfl
#align list.sublists_nil List.sublists_nil

@[simp]
theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] :=
  rfl
#align list.sublists_singleton List.sublists_singleton

--Porting note: Not the same as `sublists_aux` from Lean3
/-- Auxiliary helper function for `sublists` -/
def sublistsAux (a : α) (r : List (List α)) : List (List α) :=
  r.foldl (init := []) fun r l => r ++ [l, a :: l]
#align list.sublists_aux List.sublistsAux

theorem sublistsAux_eq_array_foldl :
    sublistsAux = fun (a : α) (r : List (List α)) =>
      (r.toArray.foldl (init := #[])
        fun r l => (r.push l).push (a :: l)).toList := by
  funext a r
  -- ⊢ sublistsAux a r = Array.toList (Array.foldl (fun r l => Array.push (Array.pu …
  simp only [sublistsAux, Array.foldl_eq_foldl_data, Array.mkEmpty]
  -- ⊢ foldl (fun r l => r ++ [l, a :: l]) [] r = Array.toList (foldl (fun r l => A …
  have := foldl_hom Array.toList (fun r l => (r.push l).push (a :: l))
    (fun (r : List (List α)) l => r ++ [l, a :: l]) r #[]
    (by simp)
  simpa using this
  -- 🎉 no goals

theorem sublistsAux_eq_bind :
    sublistsAux = fun (a : α) (r : List (List α)) => r.bind fun l => [l, a :: l] :=
  funext <| fun a => funext <| fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
        -- 🎉 no goals
    (fun r l ih => by
      rw [append_bind, ← ih, bind_singleton, sublistsAux, foldl_append]
      -- ⊢ foldl (fun r l => r ++ [l, a :: l]) (foldl (fun r l => r ++ [l, a :: l]) []  …
      simp [sublistsAux])
      -- 🎉 no goals

theorem sublists_eq_sublistsAux (l : List α) :
    sublists l = l.foldr sublistsAux [[]] := by
  simp only [sublists, sublistsAux_eq_array_foldl, Array.foldr_eq_foldr_data]
  -- ⊢ Array.toList (foldr (fun a arr => Array.foldl (fun r l => Array.push (Array. …
  rw [← foldr_hom Array.toList]
  · rfl
    -- 🎉 no goals
  · intros _ _; congr <;> simp
    -- ⊢ Array.toList (Array.foldl (fun r l => Array.push (Array.push r l) (x✝ :: l)) …
                -- ⊢ toArray (Array.toList y✝) = y✝
                          -- 🎉 no goals
                          -- 🎉 no goals

#noalign list.sublists_aux₁_eq_sublists_aux
#noalign list.sublists_aux_cons_eq_sublists_aux₁
#noalign list.sublists_aux_eq_foldr.aux
#noalign list.sublists_aux_eq_foldr
#noalign list.sublists_aux_cons_cons
#noalign list.sublists_aux₁_append
#noalign list.sublists_aux₁_concat
#noalign list.sublists_aux₁_bind
#noalign list.sublists_aux_cons_append

theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x)) := by
  simp only [sublists_eq_sublistsAux, foldr_append, sublistsAux_eq_bind]
  -- ⊢ foldr (fun a r => List.bind r fun l => [l, a :: l]) (foldr (fun a r => List. …
  induction l₁
  · case nil => simp
    -- 🎉 no goals
    -- 🎉 no goals
  · case cons a l₁ ih =>
      rw [foldr_cons, ih]
      simp [List.bind, join_join, Function.comp]
#align list.sublists_append List.sublists_append

--Portin note: New theorem
theorem sublists_cons (a : α) (l : List α) :
    sublists (a :: l) = sublists l >>= (fun x => [x, a :: x]) :=
  show sublists ([a] ++ l) = _ by
  rw [sublists_append]
  -- ⊢ (do
  simp only [sublists_singleton, map_cons, bind_eq_bind, nil_append, cons_append, map_nil]
  -- 🎉 no goals

@[simp]
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append, sublists_singleton, bind_eq_bind, cons_bind, cons_bind, nil_bind,
     map_id' append_nil, append_nil]
#align list.sublists_concat List.sublists_concat

theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction' l with hd tl ih <;> [rfl;
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      map_eq_map, bind_eq_bind, map_map, cons_bind, append_nil, nil_bind, (· ∘ ·)]]
#align list.sublists_reverse List.sublists_reverse

theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse, reverse_reverse]
  -- 🎉 no goals
#align list.sublists_eq_sublists' List.sublists_eq_sublists'

theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [sublists_eq_sublists', map_map, map_id' reverse_reverse, Function.comp]
  -- 🎉 no goals
#align list.sublists'_reverse List.sublists'_reverse

theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse, reverse_reverse]
  -- 🎉 no goals
#align list.sublists'_eq_sublists List.sublists'_eq_sublists

#noalign list.sublists_aux_ne_nil

@[simp]
theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s <+ t := by
  rw [← reverse_sublist, ← mem_sublists', sublists'_reverse,
    mem_map_of_injective reverse_injective]
#align list.mem_sublists List.mem_sublists

@[simp]
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]
  -- 🎉 no goals
#align list.length_sublists List.length_sublists

theorem map_ret_sublist_sublists (l : List α) : map List.ret l <+ sublists l := by
  induction' l using reverseRecOn with l a ih <;>
  -- ⊢ map List.ret [] <+ sublists []
  simp only [map, map_append, sublists_concat]
  -- ⊢ [] <+ sublists []
  -- ⊢ map List.ret l ++ [List.ret a] <+ sublists l ++ map (fun x => x ++ [a]) (sub …
  · simp only [sublists_nil, sublist_cons]
    -- 🎉 no goals
  exact ((append_sublist_append_left _).2 <|
              singleton_sublist.2 <| mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)
#align list.map_ret_sublist_sublists List.map_ret_sublist_sublists

/-! ### sublistsLen -/


/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
`f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublistsLenAux {α β : Type*} : ℕ → List α → (List α → β) → List β → List β
  | 0, _, f, r => f [] :: r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)
#align list.sublists_len_aux List.sublistsLenAux

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublistsLen {α : Type*} (n : ℕ) (l : List α) : List (List α) :=
  sublistsLenAux n l id []
#align list.sublists_len List.sublistsLen

theorem sublistsLenAux_append {α β γ : Type*} :
    ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => by unfold sublistsLenAux; simp
                           -- ⊢ (g ∘ f) [] :: (map g r ++ s) = map g (f [] :: r) ++ s
                                                  -- 🎉 no goals
  | n + 1, [], f, g, r, s => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublistsLenAux
    -- ⊢ sublistsLenAux (Nat.add n 0 + 1) l (g ∘ f) (sublistsLenAux (Nat.add n 0) l ( …
    simp only [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by rfl, sublistsLenAux_append,
      sublistsLenAux_append]
#align list.sublists_len_aux_append List.sublistsLenAux_append

theorem sublistsLenAux_eq {α β : Type*} (l : List α) (n) (f : List α → β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublistsLen, ← sublistsLenAux_append]; rfl
  -- ⊢ sublistsLenAux n l f r = sublistsLenAux n l (f ∘ id) (map f [] ++ r)
                                             -- 🎉 no goals
#align list.sublists_len_aux_eq List.sublistsLenAux_eq

theorem sublistsLenAux_zero {α : Type*} (l : List α) (f : List α → β) (r) :
    sublistsLenAux 0 l f r = f [] :: r := by cases l <;> rfl
                                             -- ⊢ sublistsLenAux 0 [] f r = f [] :: r
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
#align list.sublists_len_aux_zero List.sublistsLenAux_zero

@[simp]
theorem sublistsLen_zero {α : Type*} (l : List α) : sublistsLen 0 l = [[]] :=
  sublistsLenAux_zero _ _ _
#align list.sublists_len_zero List.sublistsLen_zero

@[simp]
theorem sublistsLen_succ_nil {α : Type*} (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl
#align list.sublists_len_succ_nil List.sublistsLen_succ_nil

@[simp]
theorem sublistsLen_succ_cons {α : Type*} (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublistsLen, sublistsLenAux, sublistsLenAux_eq, sublistsLenAux_eq, map_id,
      append_nil]; rfl
                   -- 🎉 no goals
#align list.sublists_len_succ_cons List.sublistsLen_succ_cons

@[simp]
theorem length_sublistsLen {α : Type*} :
    ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by simp
               -- 🎉 no goals
  | _ + 1, [] => by simp
                    -- 🎉 no goals
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, length_append, length_sublistsLen (n+1) l,
      length_map, length_sublistsLen n l, length_cons, Nat.choose_succ_succ, add_comm]
#align list.length_sublists_len List.length_sublistsLen

theorem sublistsLen_sublist_sublists' {α : Type*} :
    ∀ (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => by simp
               -- 🎉 no goals
  | _ + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, sublists'_cons]
    -- ⊢ sublistsLen (n + 1) l ++ map (cons a) (sublistsLen n l) <+ sublists' l ++ ma …
    exact (sublistsLen_sublist_sublists' _ _).append ((sublistsLen_sublist_sublists' _ _).map _)
    -- 🎉 no goals
#align list.sublists_len_sublist_sublists' List.sublistsLen_sublist_sublists'

theorem sublistsLen_sublist_of_sublist {α : Type*} (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ := by
  induction' n with n IHn generalizing l₁ l₂; · simp
  -- ⊢ sublistsLen zero l₁ <+ sublistsLen zero l₂
                                                -- 🎉 no goals
  induction' h with l₁ l₂ a _ IH l₁ l₂ a s IH; · rfl
                                                 -- 🎉 no goals
  · refine' IH.trans _
    -- ⊢ sublistsLen (succ n) l₂ <+ sublistsLen (succ n) (a :: l₂)
    rw [sublistsLen_succ_cons]
    -- ⊢ sublistsLen (succ n) l₂ <+ sublistsLen (n + 1) l₂ ++ map (cons a) (sublistsL …
    apply sublist_append_left
    -- 🎉 no goals
  · simp [sublistsLen_succ_cons]
    -- ⊢ sublistsLen (n + 1) l₁ ++ map (cons a) (sublistsLen n l₁) <+ sublistsLen (n  …
    exact IH.append ((IHn s).map _)
    -- 🎉 no goals
#align list.sublists_len_sublist_of_sublist List.sublistsLen_sublist_of_sublist

theorem length_of_sublistsLen {α : Type*} :
    ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n
  | 0, l, l', h => by simp_all
                      -- 🎉 no goals
  | n + 1, a :: l, l', h => by
    rw [sublistsLen_succ_cons, mem_append, mem_map] at h
    -- ⊢ length l' = n + 1
    rcases h with (h | ⟨l', h, rfl⟩)
    -- ⊢ length l' = n + 1
    · exact length_of_sublistsLen h
      -- 🎉 no goals
    · exact congr_arg (· + 1) (length_of_sublistsLen h)
      -- 🎉 no goals
#align list.length_of_sublists_len List.length_of_sublistsLen

theorem mem_sublistsLen_self {α : Type*} {l l' : List α} (h : l' <+ l) :
    l' ∈ sublistsLen (length l') l := by
  induction' h with l₁ l₂ a s IH l₁ l₂ a s IH
  · simp
    -- 🎉 no goals
  · cases' l₁ with b l₁
    -- ⊢ [] ∈ sublistsLen (length []) (a :: l₂)
    · simp
      -- 🎉 no goals
    · rw [length, sublistsLen_succ_cons]
      -- ⊢ b :: l₁ ∈ sublistsLen (length l₁ + 1) l₂ ++ map (cons a) (sublistsLen (lengt …
      exact mem_append_left _ IH
      -- 🎉 no goals
  · rw [length, sublistsLen_succ_cons]
    -- ⊢ a :: l₁ ∈ sublistsLen (length l₁ + 1) l₂ ++ map (cons a) (sublistsLen (lengt …
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)
    -- 🎉 no goals
#align list.mem_sublists_len_self List.mem_sublistsLen_self

@[simp]
theorem mem_sublistsLen {α : Type*} {n} {l l' : List α} :
    l' ∈ sublistsLen n l ↔ l' <+ l ∧ length l' = n :=
  ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩
#align list.mem_sublists_len List.mem_sublistsLen

theorem sublistsLen_of_length_lt {n} {l : List α} (h : l.length < n) : sublistsLen n l = [] :=
  eq_nil_iff_forall_not_mem.mpr fun _ =>
    mem_sublistsLen.not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_le (Sublist.length_le hs)
#align list.sublists_len_of_length_lt List.sublistsLen_of_length_lt

@[simp]
theorem sublistsLen_length : ∀ l : List α, sublistsLen l.length l = [l]
  | [] => rfl
  | a :: l => by
    simp only [length, sublistsLen_succ_cons, sublistsLen_length, map,
      sublistsLen_of_length_lt (lt_succ_self _), nil_append]
#align list.sublists_len_length List.sublistsLen_length

open Function

theorem Pairwise.sublists' {R} :
    ∀ {l : List α}, Pairwise R l → Pairwise (Lex (swap R)) (sublists' l)
  | _, Pairwise.nil => pairwise_singleton _ _
  | _, @Pairwise.cons _ _ a l H₁ H₂ => by
    simp only [sublists'_cons, pairwise_append, pairwise_map, mem_sublists', mem_map, exists_imp,
      and_imp]
    refine' ⟨H₂.sublists', H₂.sublists'.imp fun l₁ => Lex.cons l₁, _⟩
    -- ⊢ ∀ (a_1 : List α), a_1 <+ l → ∀ (b x : List α), x <+ l → a :: x = b → Lex (sw …
    rintro l₁ sl₁ x l₂ _ rfl
    -- ⊢ Lex (swap R) l₁ (a :: l₂)
    cases' l₁ with b l₁; · constructor
    -- ⊢ Lex (swap R) [] (a :: l₂)
                           -- 🎉 no goals
    exact Lex.rel (H₁ _ <| sl₁.subset <| mem_cons_self _ _)
    -- 🎉 no goals
#align list.pairwise.sublists' List.Pairwise.sublists'

theorem pairwise_sublists {R} {l : List α} (H : Pairwise R l) :
    Pairwise (fun l₁ l₂ => Lex R (reverse l₁) (reverse l₂)) (sublists l) := by
  have := (pairwise_reverse.2 H).sublists'
  -- ⊢ Pairwise (fun l₁ l₂ => Lex R (reverse l₁) (reverse l₂)) (sublists l)
  rwa [sublists'_reverse, pairwise_map] at this
  -- 🎉 no goals
#align list.pairwise_sublists List.pairwise_sublists

@[simp]
theorem nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l :=
  ⟨fun h => (h.sublist (map_ret_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp @fun l₁ l₂ h => by simpa using h.to_ne⟩
                                                 -- 🎉 no goals
#align list.nodup_sublists List.nodup_sublists

@[simp]
theorem nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l := by
  rw [sublists'_eq_sublists, nodup_map_iff reverse_injective, nodup_sublists, nodup_reverse]
  -- 🎉 no goals
#align list.nodup_sublists' List.nodup_sublists'

alias ⟨nodup.of_sublists, nodup.sublists⟩ := nodup_sublists
#align list.nodup.of_sublists List.nodup.of_sublists
#align list.nodup.sublists List.nodup.sublists

alias ⟨nodup.of_sublists', nodup.sublists'⟩ := nodup_sublists'
#align list.nodup.of_sublists' List.nodup.of_sublists'
#align list.nodup.sublists' List.nodup.sublists'

--Porting note: commented out
--attribute [protected] nodup.sublists nodup.sublists'

theorem nodup_sublistsLen (n : ℕ) {l : List α} (h : Nodup l) : (sublistsLen n l).Nodup := by
  have : Pairwise (· ≠ ·) l.sublists' := Pairwise.imp
    (fun h => Lex.to_ne (by convert h using 3; simp [swap, eq_comm])) h.sublists'
  exact this.sublist (sublistsLen_sublist_sublists' _ _)
  -- 🎉 no goals
#align list.nodup_sublists_len List.nodup_sublistsLen

--Porting note: new theorem
theorem sublists_map (f : α → β) : ∀ (l : List α),
    sublists (map f l) = map (map f) (sublists l)
  | [] => by simp
             -- 🎉 no goals
  | a::l => by
    rw [map_cons, sublists_cons, bind_eq_bind, sublists_map f l, sublists_cons,
      bind_eq_bind, map_eq_bind, map_eq_bind]
    induction sublists l <;> simp [*]
    -- ⊢ (List.bind (List.bind [] fun x => [map f x]) fun x => [x, f a :: x]) = List. …
                             -- 🎉 no goals
                             -- 🎉 no goals

--Porting note: new theorem
theorem sublists'_map (f : α → β) : ∀ (l : List α),
    sublists' (map f l) = map (map f) (sublists' l)
  | [] => by simp
             -- 🎉 no goals
  | a::l => by simp [map_cons, sublists'_cons, sublists'_map f l, Function.comp]
               -- 🎉 no goals

--Porting note: moved because it is now used to prove `sublists_cons_perm_append`
theorem sublists_perm_sublists' (l : List α) : sublists l ~ sublists' l := by
  rw [← finRange_map_get l, sublists_map, sublists'_map]
  -- ⊢ map (map (get l)) (sublists (finRange (length l))) ~ map (map (get l)) (subl …
  refine' Perm.map _ _
  -- ⊢ sublists (finRange (length l)) ~ sublists' (finRange (length l))
  exact (perm_ext (nodup_sublists.2 (nodup_finRange _)) (nodup_sublists'.2 (nodup_finRange _))).2
    (by simp)
#align list.sublists_perm_sublists' List.sublists_perm_sublists'

theorem sublists_cons_perm_append (a : α) (l : List α) :
    sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
  Perm.trans (sublists_perm_sublists' _) <| by
  rw [sublists'_cons];
  -- ⊢ sublists' l ++ map (cons a) (sublists' l) ~ sublists l ++ map (cons a) (subl …
  exact Perm.append (sublists_perm_sublists' _).symm (Perm.map _ (sublists_perm_sublists' _).symm)
  -- 🎉 no goals
#align list.sublists_cons_perm_append List.sublists_cons_perm_append

theorem revzip_sublists (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists → l₁ ++ l₂ ~ l := by
  rw [revzip]
  -- ⊢ ∀ (l₁ l₂ : List α), (l₁, l₂) ∈ zip (sublists l) (reverse (sublists l)) → l₁  …
  induction' l using List.reverseRecOn with l' a ih
  -- ⊢ ∀ (l₁ l₂ : List α), (l₁, l₂) ∈ zip (sublists []) (reverse (sublists [])) → l …
  · intro l₁ l₂ h
    -- ⊢ l₁ ++ l₂ ~ []
    simp at h
    -- ⊢ l₁ ++ l₂ ~ []
    simp [h]
    -- 🎉 no goals
  · intro l₁ l₂ h
    -- ⊢ l₁ ++ l₂ ~ l' ++ [a]
    rw [sublists_concat, reverse_append, zip_append, ← map_reverse, zip_map_right,
      zip_map_left] at * <;> [skip; simp]
    simp only [Prod.mk.inj_iff, mem_map, mem_append, Prod.map_mk, Prod.exists] at h
    -- ⊢ l₁ ++ l₂ ~ l' ++ [a]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    -- ⊢ id l₁ ++ (l₂' ++ [a]) ~ l' ++ [a]
    · rw [← append_assoc]
      -- ⊢ id l₁ ++ l₂' ++ [a] ~ l' ++ [a]
      exact (ih _ _ h).append_right _
      -- 🎉 no goals
    · rw [append_assoc]
      -- ⊢ l₁' ++ ([a] ++ id l₂) ~ l' ++ [a]
      apply (perm_append_comm.append_left _).trans
      -- ⊢ l₁' ++ (id l₂ ++ [a]) ~ l' ++ [a]
      rw [← append_assoc]
      -- ⊢ l₁' ++ id l₂ ++ [a] ~ l' ++ [a]
      exact (ih _ _ h).append_right _
      -- 🎉 no goals
#align list.revzip_sublists List.revzip_sublists

theorem revzip_sublists' (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists' → l₁ ++ l₂ ~ l := by
  rw [revzip]
  -- ⊢ ∀ (l₁ l₂ : List α), (l₁, l₂) ∈ zip (sublists' l) (reverse (sublists' l)) → l …
  induction' l with a l IH <;> intro l₁ l₂ h
  -- ⊢ ∀ (l₁ l₂ : List α), (l₁, l₂) ∈ zip (sublists' []) (reverse (sublists' [])) → …
                               -- ⊢ l₁ ++ l₂ ~ []
                               -- ⊢ l₁ ++ l₂ ~ a :: l
  · simp at h
    -- ⊢ l₁ ++ l₂ ~ []
    simp [h]
    -- 🎉 no goals
  · rw [sublists'_cons, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at *
      <;> [simp at h; simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    -- ⊢ l₁ ++ a :: l₂' ~ a :: l
    · exact perm_middle.trans ((IH _ _ h).cons _)
      -- 🎉 no goals
    · exact (IH _ _ h).cons _
      -- 🎉 no goals
#align list.revzip_sublists' List.revzip_sublists'

theorem range_bind_sublistsLen_perm {α : Type*} (l : List α) :
    ((List.range (l.length + 1)).bind fun n => sublistsLen n l) ~ sublists' l := by
  induction' l with h tl l_ih
  -- ⊢ (List.bind (range (length [] + 1)) fun n => sublistsLen n []) ~ sublists' []
  · simp [range_succ]
    -- 🎉 no goals
  · simp_rw [range_succ_eq_map, length, cons_bind, map_bind, sublistsLen_succ_cons, sublists'_cons,
      List.sublistsLen_zero, List.singleton_append]
    refine' ((bind_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans _
    -- ⊢ [] :: ((List.bind (range (length tl + 1)) fun a => sublistsLen (a + 1) tl) + …
    simp_rw [← List.bind_map, ← cons_append]
    -- ⊢ ([] :: List.bind (range (length tl + 1)) fun a => sublistsLen (a + 1) tl) ++ …
    rw [← List.singleton_append, ← List.sublistsLen_zero tl]
    -- ⊢ (sublistsLen 0 tl ++ List.bind (range (length tl + 1)) fun a => sublistsLen  …
    refine' Perm.append _ (l_ih.map _)
    -- ⊢ (sublistsLen 0 tl ++ List.bind (range (length tl + 1)) fun a => sublistsLen  …
    rw [List.range_succ, append_bind, bind_singleton,
      sublistsLen_of_length_lt (Nat.lt_succ_self _), append_nil, ←
      List.map_bind (fun n => sublistsLen n tl) Nat.succ, ←
      cons_bind 0 _ fun n => sublistsLen n tl, ← range_succ_eq_map]
    exact l_ih
    -- 🎉 no goals
#align list.range_bind_sublists_len_perm List.range_bind_sublistsLen_perm

end List
