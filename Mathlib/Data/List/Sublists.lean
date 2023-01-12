/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.sublists
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Perm

/-! # sublists

`List.Sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
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

-- Porting note: sublists'_aux disappeared. Check if it's really removed.
--theorem map_sublists'_aux (g : List β → List γ) (l : List α) (f r) :
--    map g (sublists'Aux l f r) = sublists'Aux l (g ∘ f) (map g r) := by
--  induction l generalizing f r <;> [rfl, simp only [*, sublists'_aux]]
--#align list.map_sublists'_aux List.map_sublists'_aux

--theorem sublists'_aux_append (r' : List (List β)) (l : List α) (f r) :
--    sublists'Aux l f (r ++ r') = sublists'Aux l f r ++ r' := by
--  induction l generalizing f r <;> [rfl, simp only [*, sublists'_aux]]
--#align list.sublists'_aux_append List.sublists'_aux_append

--theorem sublists'_aux_eq_sublists' (l f r) : @sublists'Aux α β l f r = map f (sublists' l) ++ r :=
--  by rw [sublists', map_sublists'_aux, ← sublists'_aux_append] <;> rfl
--#align list.sublists'_aux_eq_sublists' List.sublists'_aux_eq_sublists'

-- Porting note: Previous proof was:
-- rw [sublists', sublists'Aux] <;> simp only [sublists'Aux_eq_sublists', map_id, append_nil] <;>
--   rfl
--
-- This uses sublists'Aux, a removed definition.

--Porting note: Not the same as `sublists'_aux` from Lean3
def sublists'Aux (a : α) (r₁ r₂ : List (List α)) : List (List α) :=
  r₁.foldl (init := r₂) fun r l => r ++ [a :: l]

theorem sublists'Aux_eq_array_foldl (a : α) : ∀ (r₁ r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = ((r₁.toArray).foldl (init := r₂.toArray)
      (fun r l => r.push (a :: l))).toList := by
  intro r₁ r₂
  rw [sublists'Aux, Array.foldl_eq_foldl_data]
  have := List.foldl_hom Array.toList (fun r l => r.push (a :: l))
    (fun r l => r ++ [a :: l]) r₁ r₂.toArray (by simp)
  simpa using this

theorem sublists'_eq_sublists'Aux (l : List α) :
    sublists' l = l.foldr (fun a r => sublists'Aux a r r) [[]] := by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  dsimp only
  rw [← List.foldr_hom Array.toList]
  . rfl
  . intros _ _; congr <;> simp

theorem sublists'Aux_eq_map (a : α) (r₁ : List (List α)) : ∀ (r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = r₂ ++ map (cons a) r₁ :=
  List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) <| fun r₁ l ih r₂ => by
    rw [map_append, map_singleton, ← append_assoc, ← ih, sublists'Aux, foldl_append, foldl]
    simp [sublists'Aux]

@[simp]
theorem sublists'_cons (a : α) (l : List α) :
    sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]
#align list.sublists'_cons List.sublists'_cons

@[simp]
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t :=
  by
  induction' t with a t IH generalizing s
  · simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h; rcases h with (h | ⟨s, h, rfl⟩)
  · exact sublist_cons_of_sublist _ h
  · exact h.cons_cons _
  · cases' h with _ _ _ h s _ _ h
    · exact Or.inl h
    · exact Or.inr ⟨s, h, rfl⟩
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
def sublistsAux (a : α) (r : List (List α)) : List (List α) :=
  r.foldl (init := []) fun r l => r ++ [l, a :: l]

theorem sublistsAux_eq_array_foldl :
    sublistsAux = fun (a : α) (r : List (List α)) =>
      (r.toArray.foldl (init := #[])
        fun r l => (r.push l).push (a :: l)).toList := by
  funext a r
  simp only [sublistsAux, Array.foldl_eq_foldl_data, Array.mkEmpty]
  have := foldl_hom Array.toList (fun r l => (r.push l).push (a :: l))
    (fun (r : List (List α)) l => r ++ [l, a :: l]) r #[]
    (by simp)
  simpa using this

theorem sublistsAux_eq_bind :
    sublistsAux = fun (a : α) (r : List (List α)) => r.bind fun l => [l, a :: l] :=
  funext <| fun a => funext <| fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
    (fun r l ih => by
      rw [bind_append, ← ih, bind_singleton, sublistsAux, foldl_append]
      simp [sublistsAux])

theorem sublists_eq_sublistsAux (l : List α) :
    sublists l = l.foldr sublistsAux [[]] := by
  simp only [sublists, sublistsAux_eq_array_foldl, Array.foldr_eq_foldr_data]
  rw [← foldr_hom Array.toList]
  . rfl
  . intros _ _; congr <;> simp



-- Porting note: sublists'_aux disappeared. Check if it's really removed.
-- theorem sublists_aux₁_eq_sublists_aux :
--     ∀ (l) (f : List α → List β), sublistsAux₁ l f = sublistsAux l fun ys r => f ys ++ r
--   | [], f => rfl
--   | a :: l, f => by rw [sublists_aux₁, sublists_aux] <;> simp only [*, append_assoc]
-- #align list.sublists_aux₁_eq_sublists_aux List.sublists_aux₁_eq_sublists_aux

-- theorem sublists_aux_cons_eq_sublists_aux₁ (l : List α) :
--     sublistsAux l cons = sublistsAux₁ l fun x => [x] := by
--   rw [sublists_aux₁_eq_sublists_aux] <;> rfl
-- #align list.sublists_aux_cons_eq_sublists_aux₁ List.sublists_aux_cons_eq_sublists_aux₁

-- theorem SublistsAuxEqFoldr.aux {a : α} {l : List α}
--     (IH₁ : ∀ f : List α → List β → List β, sublistsAux l f = foldr f [] (sublistsAux l cons))
--     (IH₂ :
--       ∀ f : List α → List (List α) → List (List α),
--         sublistsAux l f = foldr f [] (sublistsAux l cons))
--     (f : List α → List β → List β) :
--     sublistsAux (a :: l) f = foldr f [] (sublistsAux (a :: l) cons) :=
--   by
--   simp only [sublists_aux, foldr_cons]; rw [IH₂, IH₁]; congr 1
--   induction' sublists_aux l cons with _ _ ih; · rfl
--   simp only [ih, foldr_cons]
-- #align list.sublists_aux_eq_foldr.aux List.SublistsAuxEqFoldr.aux

-- theorem sublists_aux_eq_foldr (l : List α) :
--     ∀ f : List α → List β → List β, sublistsAux l f = foldr f [] (sublistsAux l cons) :=
--   by
--   suffices
--     _ ∧
--       ∀ f : List α → List (List α) → List (List α),
--         sublistsAux l f = foldr f [] (sublistsAux l cons)
--     from this.1
--   induction' l with a l IH; · constructor <;> intro <;> rfl
--   exact ⟨sublists_aux_eq_foldr.aux IH.1 IH.2, sublists_aux_eq_foldr.aux IH.2 IH.2⟩
-- #align list.sublists_aux_eq_foldr List.sublists_aux_eq_foldr

-- theorem sublists_aux_cons_cons (l : List α) (a : α) :
--     sublistsAux (a :: l) cons =
--       [a] :: foldr (fun ys r => ys :: (a :: ys) :: r) [] (sublistsAux l cons) :=
--   by rw [← sublists_aux_eq_foldr] <;> rfl
-- #align list.sublists_aux_cons_cons List.sublists_aux_cons_cons

-- theorem sublistsAux₁_append :
--     ∀ (l₁ l₂ : List α) (f : List α → List β),
--       sublistsAux₁ (l₁ ++ l₂) f =
--         sublistsAux₁ l₁ f ++ sublistsAux₁ l₂ fun x => f x ++ sublistsAux₁ l₁ (f ∘ (· ++ x))
--   | [], l₂, f => by simp only [sublistsAux₁, nil_append, append_nil]
--   | a :: l₁, l₂, f => by
--     simp [sublistsAux₁, cons_append, sublistsAux₁_append l₁, append_assoc]; rfl
-- #align list.sublists_aux₁_append List.sublistsAux₁_append

-- theorem sublistsAux₁_concat (l : List α) (a : α) (f : List α → List β) :
--     sublistsAux₁ (l ++ [a]) f = sublistsAux₁ l f ++ f [a] ++ sublistsAux₁ l fun x => f (x ++ [a]) :=
--  by simp only [sublistsAux₁_append, sublistsAux₁, append_assoc, append_nil, Function.comp]
-- #align list.sublists_aux₁_concat List.sublistsAux₁_concat

-- theorem sublistsAux₁_bind :
--     ∀ (l : List α) (f : List α → List β) (g : β → List γ),
--       (sublistsAux₁ l f).bind g = sublistsAux₁ l fun x => (f x).bind g
--   | [], f, g => rfl
--   | a :: l, f, g => by simp only [sublistsAux₁, bind_append, sublistsAux₁_bind l]
-- #align list.sublists_aux₁_bind List.sublistsAux₁_bind

-- Porting note: sublists'_aux disappeared. Check if it's really removed.
-- theorem sublists_aux_cons_append (l₁ l₂ : List α) :
--     sublistsAux (l₁ ++ l₂) cons =
--       sublistsAux l₁ cons ++ do
--         let x ← sublistsAux l₂ cons
--         (· ++ x) <$> sublists l₁ :=
--   by
--   simp only [sublists, sublists_aux_cons_eq_sublists_aux₁, sublists_aux₁_append, bind_eq_bind,
--     sublists_aux₁_bind]
--   congr ; funext x; apply congr_arg _
--   rw [← bind_ret_eq_map, sublists_aux₁_bind]; exact (append_nil _).symm
-- #align list.sublists_aux_cons_append List.sublists_aux_cons_append

theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (. ++ x)) := by
  simp only [sublists_eq_sublistsAux, foldr_append, sublistsAux_eq_bind]
  induction l₁
  . case nil => simp
  . case cons a l₁ ih =>
      rw [foldr_cons, ih]
      simp [List.bind, join_join, Function.comp]
#align list.sublists_append List.sublists_append

@[simp]
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append, sublists_singleton, bind_eq_bind, cons_bind, cons_bind, nil_bind,
     map_id' append_nil, append_nil]
#align list.sublists_concat List.sublists_concat

theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction' l with hd tl ih <;> [rfl,
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      map_eq_map, bind_eq_bind, map_map, cons_bind, append_nil, nil_bind, (· ∘ ·)]]
#align list.sublists_reverse List.sublists_reverse

theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse, reverse_reverse]
#align list.sublists_eq_sublists' List.sublists_eq_sublists'

theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [sublists_eq_sublists', map_map, map_id' reverse_reverse, Function.comp]
#align list.sublists'_reverse List.sublists'_reverse

theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse, reverse_reverse]
#align list.sublists'_eq_sublists List.sublists'_eq_sublists

-- Porting note: sublists'_aux disappeared. Check if it's really removed.
-- theorem sublists_aux_ne_nil : ∀ l : List α, [] ∉ sublistsAux l cons
--   | [] => id
--   | a :: l => by
--     rw [sublists_aux_cons_cons]
--     refine' not_mem_cons_of_ne_of_not_mem (cons_ne_nil _ _).symm _
--     have := sublists_aux_ne_nil l; revert this
--     induction sublists_aux l cons <;> intro ; · rwa [foldr]
--     simp only [foldr, mem_cons_iff, false_or_iff, not_or]
--     exact ⟨ne_of_not_mem_cons this, ih (not_mem_of_not_mem_cons this)⟩
-- #align list.sublists_aux_ne_nil List.sublists_aux_ne_nil

@[simp]
theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s <+ t := by
  rw [← reverse_sublist, ← mem_sublists', sublists'_reverse,
    mem_map_of_injective reverse_injective]
#align list.mem_sublists List.mem_sublists

@[simp]
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]
#align list.length_sublists List.length_sublists

theorem map_ret_sublist_sublists (l : List α) : map List.ret l <+ sublists l := by
  induction' l using reverseRecOn with l a ih <;>
  simp only [map, map_append, sublists_concat]
  · simp only [sublists_nil, sublist_cons]
  exact ((append_sublist_append_left _).2 <|
              singleton_sublist.2 <| mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)
#align list.map_ret_sublist_sublists List.map_ret_sublist_sublists

/-! ### sublistsLen -/


/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
of `f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublistsLenAux {α β : Type _} : ℕ → List α → (List α → β) → List β → List β
  | 0, _, f, r => f [] :: r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)
#align list.sublists_len_aux List.sublistsLenAux

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublistsLen {α : Type _} (n : ℕ) (l : List α) : List (List α) :=
  sublistsLenAux n l id []
#align list.sublists_len List.sublistsLen

theorem sublistsLenAux_append {α β γ : Type _} :
    ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => by unfold sublistsLenAux; simp
  | n + 1, [], f, g, r, s => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublistsLenAux
    simp only [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by rfl, sublistsLenAux_append,
      sublistsLenAux_append]
#align list.sublists_len_aux_append List.sublistsLenAux_append

theorem sublistsLenAux_eq {α β : Type _} (l : List α) (n) (f : List α → β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublistsLen, ← sublistsLenAux_append]; rfl
#align list.sublists_len_aux_eq List.sublistsLenAux_eq

theorem sublistsLenAux_zero {α : Type _} (l : List α) (f : List α → β) (r) :
    sublistsLenAux 0 l f r = f [] :: r := by cases l <;> rfl
#align list.sublists_len_aux_zero List.sublistsLenAux_zero

@[simp]
theorem sublistsLen_zero {α : Type _} (l : List α) : sublistsLen 0 l = [[]] :=
  sublistsLenAux_zero _ _ _
#align list.sublists_len_zero List.sublistsLen_zero

@[simp]
theorem sublistsLen_succ_nil {α : Type _} (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl
#align list.sublists_len_succ_nil List.sublistsLen_succ_nil

@[simp]
theorem sublistsLen_succ_cons {α : Type _} (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublistsLen, sublistsLenAux, sublistsLenAux_eq, sublistsLenAux_eq, map_id,
      append_nil]; rfl
#align list.sublists_len_succ_cons List.sublistsLen_succ_cons

@[simp]
theorem length_sublistsLen {α : Type _} :
    ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by simp
  | _ + 1, [] => by simp
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, length_append, length_sublistsLen (n+1) l,
      length_map, length_sublistsLen n l, length_cons, Nat.choose_succ_succ, add_comm]
#align list.length_sublists_len List.length_sublistsLen

theorem sublistsLen_sublist_sublists' {α : Type _} :
    ∀ (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => by simp
  | _ + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, sublists'_cons]
    exact (sublistsLen_sublist_sublists' _ _).append ((sublistsLen_sublist_sublists' _ _).map _)
#align list.sublists_len_sublist_sublists' List.sublistsLen_sublist_sublists'

theorem sublistsLen_sublist_of_sublist {α : Type _} (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ :=
  by
  induction' n with n IHn generalizing l₁ l₂; · simp
  induction' h with l₁ l₂ a _ IH l₁ l₂ a s IH; · rfl
  · refine' IH.trans _
    rw [sublistsLen_succ_cons]
    apply sublist_append_left
  · simp [sublistsLen_succ_cons]
    exact IH.append ((IHn s).map _)
#align list.sublists_len_sublist_of_sublist List.sublistsLen_sublist_of_sublist

theorem length_of_sublistsLen {α : Type _} :
    ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n
  | 0, l, l', h => by simp_all
  | n + 1, a :: l, l', h => by
    rw [sublistsLen_succ_cons, mem_append, mem_map] at h
    rcases h with (h | ⟨l', h, rfl⟩)
    · exact length_of_sublistsLen h
    · exact congr_arg (· + 1) (length_of_sublistsLen h)
#align list.length_of_sublists_len List.length_of_sublistsLen

theorem mem_sublistsLen_self {α : Type _} {l l' : List α} (h : l' <+ l) :
    l' ∈ sublistsLen (length l') l :=
  by
  induction' h with l₁ l₂ a s IH l₁ l₂ a s IH
  · simp
  · cases' l₁ with b l₁
    · simp
    · rw [length, sublistsLen_succ_cons]
      exact mem_append_left _ IH
  · rw [length, sublistsLen_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)
#align list.mem_sublists_len_self List.mem_sublistsLen_self

@[simp]
theorem mem_sublistsLen {α : Type _} {n} {l l' : List α} :
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
    rintro l₁ sl₁ x l₂ _ rfl
    cases' l₁ with b l₁; · constructor
    exact Lex.rel (H₁ _ <| sl₁.subset <| mem_cons_self _ _)
#align list.pairwise.sublists' List.Pairwise.sublists'

theorem pairwise_sublists {R} {l : List α} (H : Pairwise R l) :
    Pairwise (fun l₁ l₂ => Lex R (reverse l₁) (reverse l₂)) (sublists l) :=
  by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this
#align list.pairwise_sublists List.pairwise_sublists

@[simp]
theorem nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l :=
  ⟨fun h => (h.sublist (map_ret_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp fun h => _⟩
#align list.nodup_sublists List.nodup_sublists

@[simp]
theorem nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l := by
  rw [sublists'_eq_sublists, nodup_map_iff reverse_injective, nodup_sublists, nodup_reverse]
#align list.nodup_sublists' List.nodup_sublists'

alias nodup_sublists ↔ nodup.of_sublists nodup.sublists
#align list.nodup.of_sublists List.nodup.of_sublists
#align list.nodup.sublists List.nodup.sublists

alias nodup_sublists' ↔ nodup.of_sublists' nodup.sublists'
#align list.nodup.of_sublists' List.nodup.of_sublists'
#align list.nodup.sublists' List.nodup.sublists'

attribute [protected] nodup.sublists nodup.sublists'

theorem nodup_sublistsLen (n : ℕ) {l : List α} (h : Nodup l) : (sublistsLen n l).Nodup :=
  h.sublists'.sublist <| sublistsLen_sublist_sublists' _ _
#align list.nodup_sublists_len List.nodup_sublistsLen

theorem sublists_cons_perm_append (a : α) (l : List α) :
    sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) := by
  simp only [sublists, sublistsAux_cons_cons, cons_append, perm_cons]
  refine' (perm.cons _ _).trans perm_middle.symm
  induction' sublists_aux l cons with b l IH <;> simp
  exact (IH.cons _).trans perm_middle.symm
#align list.sublists_cons_perm_append List.sublists_cons_perm_append

theorem sublists_perm_sublists' : ∀ l : List α, sublists l ~ sublists' l
  | [] => Perm.refl _
  | a :: l => by
    let IH := sublists_perm_sublists' l
    rw [sublists'_cons]; exact (sublists_cons_perm_append _ _).trans (IH.append (IH.map _))
#align list.sublists_perm_sublists' List.sublists_perm_sublists'

theorem revzip_sublists (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists → l₁ ++ l₂ ~ l := by
  rw [revzip]
  induction' l using List.reverseRecOn with l' a ih
  . intro l₁ l₂ h
    simp at h
    simp [h]
  . intro l₁ l₂ h
    rw [sublists_concat, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at
        * <;>
      [skip, · simp]
    simp only [Prod.mk.inj_iff, mem_map, mem_append, Prod.map_mk, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (ih _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (ih _ _ h).append_right _
#align list.revzip_sublists List.revzip_sublists


theorem revzip_sublists' (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists' → l₁ ++ l₂ ~ l := by
  rw [revzip]
  induction' l with a l IH <;> intro l₁ l₂ h
  · simp at h
    simp [h]
  · rw [sublists'_cons, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at
        * <;> [simp at h, simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _
#align list.revzip_sublists' List.revzip_sublists'

theorem range_bind_sublistsLen_perm {α : Type _} (l : List α) :
    ((List.range (l.length + 1)).bind fun n => sublistsLen n l) ~ sublists' l := by
  induction' l with h tl l_ih
  · simp [range_succ]
  · simp_rw [range_succ_eq_map, length, cons_bind, map_bind, sublistsLen_succ_cons, sublists'_cons,
      List.sublistsLen_zero, List.singleton_append]
    refine' ((bind_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans _
    simp_rw [← List.bind_map, ← cons_append]
    rw [← List.singleton_append, ← List.sublistsLen_zero tl]
    refine' Perm.append _ (l_ih.map _)
    rw [List.range_succ, append_bind, bind_singleton,
      sublistsLen_of_length_lt (Nat.lt_succ_self _), append_nil, ←
      List.map_bind (fun n => sublistsLen n tl) Nat.succ, ←
      cons_bind 0 _ fun n => sublistsLen n tl, ← range_succ_eq_map]
    exact l_ih
#align list.range_bind_sublists_len_perm List.range_bind_sublistsLen_perm

end List
