/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Induction

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

@[simp]
theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] :=
  rfl

/-- Auxiliary helper definition for `sublists'` -/
def sublists'Aux (a : α) (r₁ r₂ : List (List α)) : List (List α) :=
  r₁.foldl (init := r₂) fun r l => r ++ [a :: l]

theorem sublists'Aux_eq_array_foldl (a : α) : ∀ (r₁ r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = ((r₁.toArray).foldl (init := r₂.toArray)
      (fun r l => r.push (a :: l))).toList := by
  intro r₁ r₂
  rw [sublists'Aux, Array.foldl_toList]
  have := List.foldl_hom Array.toList (g₁ := fun r l => r.push (a :: l))
    (g₂ := fun r l => r ++ [a :: l]) (l := r₁) (init := r₂.toArray) (by simp)
  simpa using this

theorem sublists'_eq_sublists'Aux (l : List α) :
    sublists' l = l.foldr (fun a r => sublists'Aux a r r) [[]] := by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  rw [← List.foldr_hom Array.toList]
  · intros; congr

theorem sublists'Aux_eq_map (a : α) (r₁ : List (List α)) : ∀ (r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = r₂ ++ map (cons a) r₁ :=
  List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) fun r₁ l ih r₂ => by
    rw [map_append, map_singleton, ← append_assoc, ← ih, sublists'Aux, foldl_append, foldl]
    simp [sublists'Aux]

@[simp 900]
theorem sublists'_cons (a : α) (l : List α) :
    sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]

@[simp]
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t := by
  induction' t with a t IH generalizing s
  · simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h
  · rcases h with (h | ⟨s, h, rfl⟩)
    · exact sublist_cons_of_sublist _ h
    · exact h.cons_cons _
  · obtain - | ⟨-, h⟩ | ⟨-, h⟩ := h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, rfl⟩

@[simp]
theorem length_sublists' : ∀ l : List α, length (sublists' l) = 2 ^ length l
  | [] => rfl
  | a :: l => by
    simp +arith only [sublists'_cons, length_append, length_sublists' l,
      length_map, length, Nat.pow_succ']

@[simp]
theorem sublists_nil : sublists (@nil α) = [[]] :=
  rfl

@[simp]
theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] :=
  rfl

/-- Auxiliary helper function for `sublists` -/
def sublistsAux (a : α) (r : List (List α)) : List (List α) :=
  r.foldl (init := []) fun r l => r ++ [l, a :: l]

theorem sublistsAux_eq_array_foldl :
    sublistsAux = fun (a : α) (r : List (List α)) =>
      (r.toArray.foldl (init := #[])
        fun r l => (r.push l).push (a :: l)).toList := by
  funext a r
  simp only [sublistsAux]
  have := foldl_hom Array.toList (g₁ := fun r l => (r.push l).push (a :: l))
    (g₂ := fun r l => r ++ [l, a :: l]) (l := r) (init := #[]) (by simp)
  simpa using this

theorem sublistsAux_eq_flatMap :
    sublistsAux = fun (a : α) (r : List (List α)) => r.flatMap fun l => [l, a :: l] :=
  funext fun a => funext fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
    (fun r l ih => by
      rw [flatMap_append, ← ih, flatMap_singleton, sublistsAux, foldl_append]
      simp [sublistsAux])

@[csimp] theorem sublists_eq_sublistsFast : @sublists = @sublistsFast := by
  ext α l : 2
  trans l.foldr sublistsAux [[]]
  · rw [sublistsAux_eq_flatMap, sublists]
  · simp only [sublistsFast, sublistsAux_eq_array_foldl]
    rw [← foldr_hom Array.toList]
    · intros; congr

theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x)) := by
  simp only [sublists, foldr_append]
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [foldr_cons, ih]
    simp [List.flatMap, flatten_flatten, Function.comp_def]

theorem sublists_cons (a : α) (l : List α) :
    sublists (a :: l) = sublists l >>= (fun x => [x, a :: x]) :=
  show sublists ([a] ++ l) = _ by
  rw [sublists_append]
  simp only [sublists_singleton, map_cons, bind_eq_flatMap, nil_append, cons_append, map_nil]

@[simp]
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append, sublists_singleton, bind_eq_flatMap, flatMap_cons, flatMap_cons, flatMap_nil,
     map_id'' append_nil, append_nil]

theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction' l with hd tl ih <;> [rfl;
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      bind_eq_flatMap, map_map, flatMap_cons, append_nil, flatMap_nil,
      Function.comp_def]]

theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse, reverse_reverse]

theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [sublists_eq_sublists', map_map, map_id'' reverse_reverse, Function.comp_def]

theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse, reverse_reverse]

@[simp]
theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s <+ t := by
  rw [← reverse_sublist, ← mem_sublists', sublists'_reverse,
    mem_map_of_injective reverse_injective]

@[simp]
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]

theorem map_pure_sublist_sublists (l : List α) : map pure l <+ sublists l := by
  induction' l using reverseRecOn with l a ih <;> simp only [map, map_append, sublists_concat]
  · simp only [sublists_nil, sublist_cons_self]
  exact ((append_sublist_append_left _).2 <|
              singleton_sublist.2 <| mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)

/-! ### sublistsLen -/

/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
`f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublistsLenAux : ℕ → List α → (List α → β) → List β → List β
  | 0, _, f, r => f [] :: r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublistsLen (n : ℕ) (l : List α) : List (List α) :=
  sublistsLenAux n l id []

theorem sublistsLenAux_append :
    ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => by unfold sublistsLenAux; simp
  | _ + 1, [], _, _, _, _ => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublistsLenAux
    simp only [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by rfl,
      sublistsLenAux_append]

theorem sublistsLenAux_eq (l : List α) (n) (f : List α → β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublistsLen, ← sublistsLenAux_append]; rfl

theorem sublistsLenAux_zero (l : List α) (f : List α → β) (r) :
    sublistsLenAux 0 l f r = f [] :: r := by cases l <;> rfl

@[simp]
theorem sublistsLen_zero (l : List α) : sublistsLen 0 l = [[]] :=
  sublistsLenAux_zero _ _ _

@[simp]
theorem sublistsLen_succ_nil (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl

@[simp]
theorem sublistsLen_succ_cons (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublistsLen, sublistsLenAux, sublistsLenAux_eq, sublistsLenAux_eq, map_id,
      append_nil]; rfl

theorem sublistsLen_one (l : List α) : sublistsLen 1 l = l.reverse.map ([·]) :=
  l.rec (by rw [sublistsLen_succ_nil, reverse_nil, map_nil]) fun a s ih ↦ by
    rw [sublistsLen_succ_cons, ih, reverse_cons, map_append, sublistsLen_zero]; rfl

@[simp]
theorem length_sublistsLen :
    ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by simp
  | _ + 1, [] => by simp
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, length_append, length_sublistsLen (n + 1) l,
      length_map, length_sublistsLen n l, length_cons, Nat.choose_succ_succ, Nat.add_comm]

theorem sublistsLen_sublist_sublists' :
    ∀ (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => by simp
  | _ + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, sublists'_cons]
    exact (sublistsLen_sublist_sublists' _ _).append ((sublistsLen_sublist_sublists' _ _).map _)

theorem sublistsLen_sublist_of_sublist (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ := by
  induction' n with n IHn generalizing l₁ l₂; · simp
  induction h with
  | slnil => rfl
  | cons a _ IH =>
    refine IH.trans ?_
    rw [sublistsLen_succ_cons]
    apply sublist_append_left
  | cons₂ a s IH => simpa only [sublistsLen_succ_cons] using IH.append ((IHn s).map _)

theorem length_of_sublistsLen :
    ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n
  | 0, l, l', h => by simp_all
  | n + 1, a :: l, l', h => by
    rw [sublistsLen_succ_cons, mem_append, mem_map] at h
    rcases h with (h | ⟨l', h, rfl⟩)
    · exact length_of_sublistsLen h
    · exact congr_arg (· + 1) (length_of_sublistsLen h)

theorem mem_sublistsLen_self {l l' : List α} (h : l' <+ l) :
    l' ∈ sublistsLen (length l') l := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a s IH =>
    rcases l₁ with - | ⟨b, l₁⟩
    · simp
    · rw [length, sublistsLen_succ_cons]
      exact mem_append_left _ IH
  | cons₂ a s IH =>
    rw [length, sublistsLen_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)

@[simp]
theorem mem_sublistsLen {n} {l l' : List α} :
    l' ∈ sublistsLen n l ↔ l' <+ l ∧ length l' = n :=
  ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩

theorem sublistsLen_of_length_lt {n} {l : List α} (h : l.length < n) : sublistsLen n l = [] :=
  eq_nil_iff_forall_not_mem.mpr fun _ =>
    mem_sublistsLen.not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_ge (Sublist.length_le hs)

@[simp]
theorem sublistsLen_length : ∀ l : List α, sublistsLen l.length l = [l]
  | [] => rfl
  | a :: l => by
    simp only [length, sublistsLen_succ_cons, sublistsLen_length, map,
      sublistsLen_of_length_lt (lt_succ_self _), nil_append]

open Function

theorem Pairwise.sublists' {R} :
    ∀ {l : List α}, Pairwise R l → Pairwise (Lex (swap R)) (sublists' l)
  | _, Pairwise.nil => pairwise_singleton _ _
  | _, @Pairwise.cons _ _ a l H₁ H₂ => by
    simp only [sublists'_cons, pairwise_append, pairwise_map, mem_sublists', mem_map, exists_imp,
      and_imp]
    refine ⟨H₂.sublists', H₂.sublists'.imp fun l₁ => Lex.cons l₁, ?_⟩
    rintro l₁ sl₁ x l₂ _ rfl
    rcases l₁ with - | ⟨b, l₁⟩; · constructor
    exact Lex.rel (H₁ _ <| sl₁.subset mem_cons_self)

theorem pairwise_sublists {R} {l : List α} (H : Pairwise R l) :
    Pairwise (Lex R on reverse) (sublists l) := by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this

@[simp]
theorem nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l :=
  ⟨fun h => (h.sublist (map_pure_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp @fun l₁ l₂ h => by simpa using h.to_ne⟩

@[simp]
theorem nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l := by
  rw [sublists'_eq_sublists, nodup_map_iff reverse_injective, nodup_sublists, nodup_reverse]

protected alias ⟨Nodup.of_sublists, Nodup.sublists⟩ := nodup_sublists

protected alias ⟨Nodup.of_sublists', _⟩ := nodup_sublists'

theorem nodup_sublistsLen (n : ℕ) {l : List α} (h : Nodup l) : (sublistsLen n l).Nodup := by
  have : Pairwise (· ≠ ·) l.sublists' := Pairwise.imp
    (fun h => Lex.to_ne (by convert h using 3; simp [eq_comm])) h.sublists'
  exact this.sublist (sublistsLen_sublist_sublists' _ _)

theorem sublists_map (f : α → β) : ∀ (l : List α),
    sublists (map f l) = map (map f) (sublists l)
  | [] => by simp
  | a::l => by
    rw [map_cons, sublists_cons, bind_eq_flatMap, sublists_map f l, sublists_cons,
      bind_eq_flatMap, map_eq_flatMap, map_eq_flatMap]
    induction sublists l <;> simp [*]

theorem sublists'_map (f : α → β) : ∀ (l : List α),
    sublists' (map f l) = map (map f) (sublists' l)
  | [] => by simp
  | a::l => by simp [map_cons, sublists'_cons, sublists'_map f l, Function.comp]

theorem sublists_perm_sublists' (l : List α) : sublists l ~ sublists' l := by
  rw [← finRange_map_get l, sublists_map, sublists'_map]
  apply Perm.map
  apply (perm_ext_iff_of_nodup _ _).mpr
  · simp
  · exact nodup_sublists.mpr (nodup_finRange _)
  · exact (nodup_sublists'.mpr (nodup_finRange _))

theorem sublists_cons_perm_append (a : α) (l : List α) :
    sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
  Perm.trans (sublists_perm_sublists' _) <| by
  rw [sublists'_cons]
  exact Perm.append (sublists_perm_sublists' _).symm (Perm.map _ (sublists_perm_sublists' _).symm)

theorem revzip_sublists (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists → l₁ ++ l₂ ~ l := by
  rw [revzip]
  induction' l using List.reverseRecOn with l' a ih
  · intro l₁ l₂ h
    have : l₁ = [] ∧ l₂ = [] := by simpa using h
    simp [this]
  · intro l₁ l₂ h
    rw [sublists_concat, reverse_append, zip_append (by simp), ← map_reverse, zip_map_right,
      zip_map_left] at *
    simp only [Prod.mk_inj, mem_map, mem_append, Prod.map_apply, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (ih _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (ih _ _ h).append_right _

theorem revzip_sublists' (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists' → l₁ ++ l₂ ~ l := by
  rw [revzip]
  induction' l with a l IH <;> intro l₁ l₂ h
  · simp_all only [sublists'_nil, reverse_cons, reverse_nil, nil_append, zip_cons_cons,
      zip_nil_right, mem_singleton, Prod.mk.injEq, append_nil, Perm.refl]
  · rw [sublists'_cons, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at *
      <;> [simp only [mem_append, mem_map, Prod.map_apply, id_eq, Prod.mk.injEq, Prod.exists,
        exists_eq_right_right] at h; simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _

theorem range_bind_sublistsLen_perm (l : List α) :
    ((List.range (l.length + 1)).flatMap fun n => sublistsLen n l) ~ sublists' l := by
  induction' l with h tl l_ih
  · simp [range_succ]
  · simp_rw [range_succ_eq_map, length, flatMap_cons, flatMap_map, sublistsLen_succ_cons,
      sublists'_cons, List.sublistsLen_zero, List.singleton_append]
    refine ((flatMap_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans ?_
    simp_rw [← List.map_flatMap, ← cons_append]
    rw [← List.singleton_append, ← List.sublistsLen_zero tl]
    refine Perm.append ?_ (l_ih.map _)
    rw [List.range_succ, flatMap_append, flatMap_singleton,
      sublistsLen_of_length_lt (Nat.lt_succ_self _), append_nil,
      ← List.flatMap_map Nat.succ fun n => sublistsLen n tl,
      ← flatMap_cons (f := fun n => sublistsLen n tl), ← range_succ_eq_map]
    exact l_ih

end List
