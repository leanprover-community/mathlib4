/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Algebra.Order.Monoid.MinMax

#align_import data.list.zip from "leanprover-community/mathlib"@"134625f523e737f650a6ea7f0c82a6177e45e622"

/-!
# zip & unzip

This file provides results about `List.zipWith`, `List.zip` and `List.unzip` (definitions are in
core Lean).
`zipWith f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : List α` and `l₂ : List β`. It
applies, until one of the lists is exhausted. For example,
`zipWith f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zipWith` applied to `Prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/


universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type*}

@[simp]
theorem zipWith_cons_cons (f : α → β → γ) (a : α) (b : β) (l₁ : List α) (l₂ : List β) :
    zipWith f (a :: l₁) (b :: l₂) = f a b :: zipWith f l₁ l₂ := rfl
#align list.zip_with_cons_cons List.zipWith_cons_cons

@[simp]
theorem zip_cons_cons (a : α) (b : β) (l₁ : List α) (l₂ : List β) :
    zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ := rfl
#align list.zip_cons_cons List.zip_cons_cons

@[simp]
theorem zipWith_nil_left (f : α → β → γ) (l) : zipWith f [] l = [] := rfl
#align list.zip_with_nil_left List.zipWith_nil_left

theorem zipWith_nil_right (f : α → β → γ) (l) : zipWith f l [] = [] := by simp
                                                                          -- 🎉 no goals
#align list.zip_with_nil_right List.zipWith_nil_right

@[simp]
theorem zipWith_eq_nil_iff {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp
  -- ⊢ zipWith f [] l' = [] ↔ [] = [] ∨ l' = []
              -- ⊢ zipWith f [] [] = [] ↔ [] = [] ∨ [] = []
              -- ⊢ zipWith f (head✝ :: tail✝) [] = [] ↔ head✝ :: tail✝ = [] ∨ [] = []
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
#align list.zip_with_eq_nil_iff List.zipWith_eq_nil_iff

@[simp]
theorem zip_nil_left (l : List α) : zip ([] : List β) l = [] :=
  rfl
#align list.zip_nil_left List.zip_nil_left

@[simp]
theorem zip_nil_right (l : List α) : zip l ([] : List β) = [] :=
  zipWith_nil_right _ l
#align list.zip_nil_right List.zip_nil_right

@[simp]
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁
  | [], l₂ => (zip_nil_right _).symm
  | l₁, [] => by rw [zip_nil_right]; rfl
                 -- ⊢ map Prod.swap [] = zip [] l₁
                                     -- 🎉 no goals
  | a :: l₁, b :: l₂ => by
    simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk]
    -- 🎉 no goals
#align list.zip_swap List.zip_swap

#align list.length_zip_with List.length_zipWith

@[simp]
theorem length_zip :
    ∀ (l₁ : List α) (l₂ : List β), length (zip l₁ l₂) = min (length l₁) (length l₂) :=
  length_zipWith _
#align list.length_zip List.length_zip

theorem all₂_zipWith {f : α → β → γ} {p : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (_h : length l₁ = length l₂),
      All₂ p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂
  | [], [], _ => by simp
                    -- 🎉 no goals
  | a :: l₁, b :: l₂, h => by
    simp only [length_cons, succ_inj'] at h
    -- ⊢ All₂ p (zipWith f (a :: l₁) (b :: l₂)) ↔ Forall₂ (fun x y => p (f x y)) (a : …
    simp [all₂_zipWith h]
    -- 🎉 no goals
#align list.all₂_zip_with List.all₂_zipWith

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by
  rw [length_zipWith, lt_min_iff] at h
  -- ⊢ i < length l
  exact h.left
  -- 🎉 no goals
#align list.lt_length_left_of_zip_with List.lt_length_left_of_zipWith

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by
  rw [length_zipWith, lt_min_iff] at h
  -- ⊢ i < length l'
  exact h.right
  -- 🎉 no goals
#align list.lt_length_right_of_zip_with List.lt_length_right_of_zipWith

theorem lt_length_left_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l.length :=
  lt_length_left_of_zipWith h
#align list.lt_length_left_of_zip List.lt_length_left_of_zip

theorem lt_length_right_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l'.length :=
  lt_length_right_of_zipWith h
#align list.lt_length_right_of_zip List.lt_length_right_of_zip

theorem zip_append :
    ∀ {l₁ r₁ : List α} {l₂ r₂ : List β} (_h : length l₁ = length l₂),
      zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
  | [], r₁, l₂, r₂, h => by simp only [eq_nil_of_length_eq_zero h.symm]; rfl
                            -- ⊢ zip ([] ++ r₁) ([] ++ r₂) = zip [] [] ++ zip r₁ r₂
                                                                         -- 🎉 no goals
  | l₁, r₁, [], r₂, h => by simp only [eq_nil_of_length_eq_zero h]; rfl
                            -- ⊢ zip ([] ++ r₁) ([] ++ r₂) = zip [] [] ++ zip r₁ r₂
                                                                    -- 🎉 no goals
  | a :: l₁, r₁, b :: l₂, r₂, h => by
    simp only [cons_append, zip_cons_cons, zip_append (succ.inj h)]
    -- 🎉 no goals
#align list.zip_append List.zip_append

theorem zip_map (f : α → γ) (g : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g)
  | [], l₂ => rfl
  | l₁, [] => by simp only [map, zip_nil_right]
                 -- 🎉 no goals
  | a :: l₁, b :: l₂ => by
    simp only [map, zip_cons_cons, zip_map, Prod.map]; constructor
    -- ⊢ (f a, g b) :: map (fun x => (f x.fst, g x.snd)) (zip l₁ l₂) = (f a, g b) ::  …
                                                       -- 🎉 no goals
#align list.zip_map List.zip_map

theorem zip_map_left (f : α → γ) (l₁ : List α) (l₂ : List β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]
                                                              -- 🎉 no goals
#align list.zip_map_left List.zip_map_left

theorem zip_map_right (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]
                                                              -- 🎉 no goals
#align list.zip_map_right List.zip_map_right

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (as : List α) (bs : List β) :
    zipWith f (as.map g) (bs.map h) = zipWith (fun a b => f (g a) (h b)) as bs := by
  induction as generalizing bs
  -- ⊢ zipWith f (map g []) (map h bs) = zipWith (fun a b => f (g a) (h b)) [] bs
  · simp
    -- 🎉 no goals
  · cases bs <;> simp [*]
    -- ⊢ zipWith f (map g (head✝ :: tail✝)) (map h []) = zipWith (fun a b => f (g a)  …
                 -- 🎉 no goals
                 -- 🎉 no goals
#align list.zip_with_map List.zipWith_map

theorem zipWith_map_left (f : α → β → γ) (g : δ → α) (l : List δ) (l' : List β) :
    zipWith f (l.map g) l' = zipWith (f ∘ g) l l' := by
  convert zipWith_map f g id l l'
  -- ⊢ l' = map id l'
  exact Eq.symm (List.map_id _)
  -- 🎉 no goals
#align list.zip_with_map_left List.zipWith_map_left

theorem zipWith_map_right (f : α → β → γ) (l : List α) (g : δ → β) (l' : List δ) :
    zipWith f l (l'.map g) = zipWith (fun x => f x ∘ g) l l' := by
  convert List.zipWith_map f id g l l'
  -- ⊢ l = map id l
  exact Eq.symm (List.map_id _)
  -- 🎉 no goals
#align list.zip_with_map_right List.zipWith_map_right

theorem zip_map' (f : α → β) (g : α → γ) :
    ∀ l : List α, zip (l.map f) (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp only [map, zip_cons_cons, zip_map']
                 -- 🎉 no goals
#align list.zip_map' List.zip_map'

theorem map_zipWith {δ : Type*} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  induction' l with hd tl hl generalizing l'
  -- ⊢ map f (zipWith g [] l') = zipWith (fun x y => f (g x y)) [] l'
  · simp
    -- 🎉 no goals
  · cases l'
    -- ⊢ map f (zipWith g (hd :: tl) []) = zipWith (fun x y => f (g x y)) (hd :: tl) []
    · simp
      -- 🎉 no goals
    · simp [hl]
      -- 🎉 no goals
#align list.map_zip_with List.map_zipWith

theorem mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, h => by
    cases' h with _ _ _ h
    -- ⊢ a ∈ a :: l₁ ∧ b ∈ b :: l₂
    · simp
      -- 🎉 no goals
    · have := mem_zip h
      -- ⊢ a ∈ head✝¹ :: l₁ ∧ b ∈ head✝ :: l₂
      exact ⟨Mem.tail _ this.1, Mem.tail _ this.2⟩
      -- 🎉 no goals
#align list.mem_zip List.mem_zip

theorem map_fst_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length ≤ l₂.length → map Prod.fst (zip l₁ l₂) = l₁
  | [], bs, _ => rfl
  | _ :: as, _ :: bs, h => by
    simp [succ_le_succ_iff] at h
    -- ⊢ map Prod.fst (zip (head✝¹ :: as) (head✝ :: bs)) = head✝¹ :: as
    change _ :: map Prod.fst (zip as bs) = _ :: as
    -- ⊢ (head✝¹, head✝).fst :: map Prod.fst (zip as bs) = head✝¹ :: as
    rw [map_fst_zip as bs h]
    -- 🎉 no goals
  | a :: as, [], h => by simp at h
                         -- 🎉 no goals
#align list.map_fst_zip List.map_fst_zip

theorem map_snd_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₂.length ≤ l₁.length → map Prod.snd (zip l₁ l₂) = l₂
  | _, [], _ => by
    rw [zip_nil_right]
    -- ⊢ map Prod.snd [] = []
    rfl
    -- 🎉 no goals
  | [], b :: bs, h => by simp at h
                         -- 🎉 no goals
  | a :: as, b :: bs, h => by
    simp [succ_le_succ_iff] at h
    -- ⊢ map Prod.snd (zip (a :: as) (b :: bs)) = b :: bs
    change _ :: map Prod.snd (zip as bs) = _ :: bs
    -- ⊢ (a, b).snd :: map Prod.snd (zip as bs) = b :: bs
    rw [map_snd_zip as bs h]
    -- 🎉 no goals
#align list.map_snd_zip List.map_snd_zip

@[simp]
theorem unzip_nil : unzip (@nil (α × β)) = ([], []) := rfl
#align list.unzip_nil List.unzip_nil

@[simp]
theorem unzip_cons (a : α) (b : β) (l : List (α × β)) :
    unzip ((a, b) :: l) = (a :: (unzip l).1, b :: (unzip l).2) := rfl
#align list.unzip_cons List.unzip_cons

theorem unzip_eq_map : ∀ l : List (α × β), unzip l = (l.map Prod.fst, l.map Prod.snd)
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, map_cons, unzip_eq_map l]
                      -- 🎉 no goals
#align list.unzip_eq_map List.unzip_eq_map

theorem unzip_left (l : List (α × β)) : (unzip l).1 = l.map Prod.fst := by simp only [unzip_eq_map]
                                                                           -- 🎉 no goals
#align list.unzip_left List.unzip_left

theorem unzip_right (l : List (α × β)) : (unzip l).2 = l.map Prod.snd := by simp only [unzip_eq_map]
                                                                            -- 🎉 no goals
#align list.unzip_right List.unzip_right

theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap := by
  simp only [unzip_eq_map, map_map]
  -- ⊢ (map (Prod.fst ∘ Prod.swap) l, map (Prod.snd ∘ Prod.swap) l) = Prod.swap (ma …
  rfl
  -- 🎉 no goals
#align list.unzip_swap List.unzip_swap

theorem zip_unzip : ∀ l : List (α × β), zip (unzip l).1 (unzip l).2 = l
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, zip_cons_cons, zip_unzip l]
                      -- 🎉 no goals
#align list.zip_unzip List.zip_unzip

theorem unzip_zip_left :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ ≤ length l₂ → (unzip (zip l₁ l₂)).1 = l₁
  | [], l₂, _ => rfl
  | l₁, [], h => by rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)]; rfl
                    -- ⊢ (unzip (zip [] [])).fst = []
                                                                              -- 🎉 no goals
  | a :: l₁, b :: l₂, h => by
    simp only [zip_cons_cons, unzip_cons, unzip_zip_left (le_of_succ_le_succ h)]
    -- 🎉 no goals
#align list.unzip_zip_left List.unzip_zip_left

theorem unzip_zip_right {l₁ : List α} {l₂ : List β} (h : length l₂ ≤ length l₁) :
    (unzip (zip l₁ l₂)).2 = l₂ := by rw [← zip_swap, unzip_swap]; exact unzip_zip_left h
                                     -- ⊢ (Prod.swap (unzip (zip l₂ l₁))).snd = l₂
                                                                  -- 🎉 no goals
#align list.unzip_zip_right List.unzip_zip_right

theorem unzip_zip {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  rw [← Prod.mk.eta (p := unzip (zip l₁ l₂)),
    unzip_zip_left (le_of_eq h), unzip_zip_right (ge_of_eq h)]
#align list.unzip_zip List.unzip_zip

theorem zip_of_prod {l : List α} {l' : List β} {lp : List (α × β)} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_left, ← unzip_right, zip_unzip, zip_unzip]
  -- 🎉 no goals
#align list.zip_of_prod List.zip_of_prod

theorem map_prod_left_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  -- ⊢ zip (map (fun x => x) l) (map (fun x => f x) l) = zip l (map f l)
  congr
  -- ⊢ map (fun x => x) l = l
  exact map_id _
  -- 🎉 no goals
#align list.map_prod_left_eq_zip List.map_prod_left_eq_zip

theorem map_prod_right_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  -- ⊢ zip (map (fun x => f x) l) (map (fun x => x) l) = zip (map f l) l
  congr
  -- ⊢ map (fun x => x) l = l
  exact map_id _
  -- 🎉 no goals
#align list.map_prod_right_eq_zip List.map_prod_right_eq_zip

theorem zipWith_comm (f : α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith f la lb = zipWith (fun b a => f a b) lb la
  | [], _ => (List.zipWith_nil_right _ _).symm
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg _ (zipWith_comm f as bs)
#align list.zip_with_comm List.zipWith_comm

@[congr]
theorem zipWith_congr (f g : α → β → γ) (la : List α) (lb : List β)
    (h : List.Forall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb := by
  induction' h with a b as bs hfg _ ih
  -- ⊢ zipWith f [] [] = zipWith g [] []
  · rfl
    -- 🎉 no goals
  · exact congr_arg₂ _ hfg ih
    -- 🎉 no goals
#align list.zip_with_congr List.zipWith_congr

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  -- ⊢ zipWith (fun b a => f a b) l' l = zipWith f l' l
  simp only [comm]
  -- 🎉 no goals
#align list.zip_with_comm_of_comm List.zipWith_comm_of_comm

@[simp]
theorem zipWith_same (f : α → α → δ) : ∀ l : List α, zipWith f l l = l.map fun a => f a a
  | [] => rfl
  | _ :: xs => congr_arg _ (zipWith_same f xs)
#align list.zip_with_same List.zipWith_same

theorem zipWith_zipWith_left (f : δ → γ → ε) (g : α → β → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_left f g as bs cs
#align list.zip_with_zip_with_left List.zipWith_zipWith_left

theorem zipWith_zipWith_right (f : α → δ → ε) (g : β → γ → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_right f g as bs cs
#align list.zip_with_zip_with_right List.zipWith_zipWith_right

@[simp]
theorem zipWith3_same_left (f : α → α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_left f as bs
#align list.zip_with3_same_left List.zipWith3_same_left

@[simp]
theorem zipWith3_same_mid (f : α → β → α → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_mid f as bs
#align list.zip_with3_same_mid List.zipWith3_same_mid

@[simp]
theorem zipWith3_same_right (f : α → β → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_right f as bs
#align list.zip_with3_same_right List.zipWith3_same_right

instance (f : α → α → β) [IsSymmOp α β f] : IsSymmOp (List α) (List β) (zipWith f) :=
  ⟨zipWith_comm_of_comm f IsSymmOp.symm_op⟩

@[simp]
theorem length_revzip (l : List α) : length (revzip l) = length l := by
  simp only [revzip, length_zip, length_reverse, min_self]
  -- 🎉 no goals
#align list.length_revzip List.length_revzip

@[simp]
theorem unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse) :=
  unzip_zip (length_reverse l).symm
#align list.unzip_revzip List.unzip_revzip

@[simp]
theorem revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l := by
  rw [← unzip_left, unzip_revzip]
  -- 🎉 no goals
#align list.revzip_map_fst List.revzip_map_fst

@[simp]
theorem revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse := by
  rw [← unzip_right, unzip_revzip]
  -- 🎉 no goals
#align list.revzip_map_snd List.revzip_map_snd

theorem reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse := by
  rw [← zip_unzip (revzip l).reverse]
  -- ⊢ zip (unzip (reverse (revzip l))).fst (unzip (reverse (revzip l))).snd = revz …
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]
  -- 🎉 no goals
#align list.reverse_revzip List.reverse_revzip

theorem revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse := by simp [revzip]
                                                                                     -- 🎉 no goals
#align list.revzip_swap List.revzip_swap

theorem get?_zip_with (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = ((l₁.get? i).map f).bind fun g => (l₂.get? i).map g := by
  induction' l₁ with head tail generalizing l₂ i
  -- ⊢ get? (zipWith f [] l₂) i = Option.bind (Option.map f (get? [] i)) fun g => O …
  · rw [zipWith] <;> simp
    -- ⊢ get? [] i = Option.bind (Option.map f (get? [] i)) fun g => Option.map g (ge …
                     -- 🎉 no goals
                     -- 🎉 no goals
  · cases l₂
    -- ⊢ get? (zipWith f (head :: tail) []) i = Option.bind (Option.map f (get? (head …
    simp only [zipWith, Seq.seq, Functor.map, get?, Option.map_none']
    -- ⊢ none = Option.bind (Option.map f (get? (head :: tail) i)) fun g => none
    · cases (head :: tail).get? i <;> rfl
      -- ⊢ none = Option.bind (Option.map f none) fun g => none
                                      -- 🎉 no goals
                                      -- 🎉 no goals
    · cases i <;> simp only [Option.map_some', get?, Option.some_bind', *]
      -- ⊢ get? (zipWith f (head :: tail) (head✝ :: tail✝)) zero = Option.bind (Option. …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.nth_zip_with List.get?_zip_with

theorem get?_zip_with_eq_some {α β γ} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = some z ↔
      ∃ x y, l₁.get? i = some x ∧ l₂.get? i = some y ∧ f x y = z := by
  induction l₁ generalizing l₂ i
  -- ⊢ get? (zipWith f [] l₂) i = some z ↔ ∃ x y, get? [] i = some x ∧ get? l₂ i =  …
  · simp [zipWith]
    -- 🎉 no goals
  · cases l₂ <;> simp only [zipWith, get?, exists_false, and_false_iff, false_and_iff]
    -- ⊢ get? (zipWith f (head✝ :: tail✝) []) i = some z ↔ ∃ x y, get? (head✝ :: tail …
                 -- 🎉 no goals
                 -- ⊢ get? (f head✝¹ head✝ :: zipWith f tail✝¹ tail✝) i = some z ↔ ∃ x y, get? (he …
    cases i <;> simp [*]
    -- ⊢ get? (f head✝¹ head✝ :: zipWith f tail✝¹ tail✝) zero = some z ↔ ∃ x y, get?  …
                -- 🎉 no goals
                -- 🎉 no goals
#align list.nth_zip_with_eq_some List.get?_zip_with_eq_some

theorem get?_zip_eq_some (l₁ : List α) (l₂ : List β) (z : α × β) (i : ℕ) :
    (zip l₁ l₂).get? i = some z ↔ l₁.get? i = some z.1 ∧ l₂.get? i = some z.2 := by
  cases z
  -- ⊢ get? (zip l₁ l₂) i = some (fst✝, snd✝) ↔ get? l₁ i = some (fst✝, snd✝).fst ∧ …
  rw [zip, get?_zip_with_eq_some]; constructor
  -- ⊢ (∃ x y, get? l₁ i = some x ∧ get? l₂ i = some y ∧ (x, y) = (fst✝, snd✝)) ↔ g …
                                   -- ⊢ (∃ x y, get? l₁ i = some x ∧ get? l₂ i = some y ∧ (x, y) = (fst✝, snd✝)) → g …
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    -- ⊢ get? l₁ i = some (fst✝, snd✝).fst ∧ get? l₂ i = some (fst✝, snd✝).snd
    simpa [h₀, h₁] using h₂
    -- 🎉 no goals
  · rintro ⟨h₀, h₁⟩
    -- ⊢ ∃ x y, get? l₁ i = some x ∧ get? l₂ i = some y ∧ (x, y) = (fst✝, snd✝)
    exact ⟨_, _, h₀, h₁, rfl⟩
    -- 🎉 no goals
#align list.nth_zip_eq_some List.get?_zip_eq_some

@[simp]
theorem get_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : Fin (zipWith f l l').length} :
    (zipWith f l l').get i =
      f (l.get ⟨i, lt_length_left_of_zipWith i.isLt⟩)
        (l'.get ⟨i, lt_length_right_of_zipWith i.isLt⟩) := by
  rw [← Option.some_inj, ← get?_eq_get, get?_zip_with_eq_some]
  -- ⊢ ∃ x y, get? l ↑i = some x ∧ get? l' ↑i = some y ∧ f x y = f (get l { val :=  …
  exact
    ⟨l.get ⟨i, lt_length_left_of_zipWith i.isLt⟩, l'.get ⟨i, lt_length_right_of_zipWith i.isLt⟩,
      by rw [get?_eq_get], by rw [get?_eq_get]; exact ⟨rfl, rfl⟩⟩

@[simp]
theorem nthLe_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : ℕ}
    {h : i < (zipWith f l l').length} :
    (zipWith f l l').nthLe i h =
      f (l.nthLe i (lt_length_left_of_zipWith h)) (l'.nthLe i (lt_length_right_of_zipWith h)) :=
  get_zipWith (i := ⟨i, h⟩)
#align list.nth_le_zip_with List.nthLe_zipWith

@[simp]
theorem get_zip {l : List α} {l' : List β} {i : Fin (zip l l').length} :
    (zip l l').get i =
      (l.get ⟨i, lt_length_left_of_zip i.isLt⟩, l'.get ⟨i, lt_length_right_of_zip i.isLt⟩) :=
  get_zipWith

@[simp]
theorem nthLe_zip {l : List α} {l' : List β} {i : ℕ} {h : i < (zip l l').length} :
    (zip l l').nthLe i h =
      (l.nthLe i (lt_length_left_of_zip h), l'.nthLe i (lt_length_right_of_zip h)) :=
  nthLe_zipWith
#align list.nth_le_zip List.nthLe_zip

theorem mem_zip_inits_tails {l : List α} {init tail : List α} :
    (init, tail) ∈ zip l.inits l.tails ↔ init ++ tail = l := by
  induction' l with hd tl ih generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  -- ⊢ (init, tail) ∈ zip (inits []) (tails []) ↔ init ++ tail = []
                                                        -- ⊢ (init, tail) ∈ ([], []) :: zip [] [] ↔ init ++ tail = []
                                                        -- ⊢ (init, tail) ∈ ([], hd :: tl) :: zip (map (fun t => hd :: t) (inits tl)) (ta …
  · simp
    -- 🎉 no goals
  · constructor <;> rw [mem_cons, zip_map_left, mem_map, Prod.exists]
    -- ⊢ (init, tail) ∈ ([], hd :: tl) :: zip (map (fun t => hd :: t) (inits tl)) (ta …
                    -- ⊢ ((init, tail) = ([], hd :: tl) ∨ ∃ a b, (a, b) ∈ zip (inits tl) (tails tl) ∧ …
                    -- ⊢ init ++ tail = hd :: tl → (init, tail) = ([], hd :: tl) ∨ ∃ a b, (a, b) ∈ zi …
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      -- ⊢ [] ++ hd :: tl = hd :: tl
      · simp
        -- 🎉 no goals
      · simp [ih.mp h]
        -- 🎉 no goals
    · cases' init with hd' tl'
      -- ⊢ [] ++ tail = hd :: tl → ([], tail) = ([], hd :: tl) ∨ ∃ a b, (a, b) ∈ zip (i …
      · rintro rfl
        -- ⊢ ([], hd :: tl) = ([], hd :: tl) ∨ ∃ a b, (a, b) ∈ zip (inits tl) (tails tl)  …
        simp
        -- 🎉 no goals
      · intro h
        -- ⊢ (hd' :: tl', tail) = ([], hd :: tl) ∨ ∃ a b, (a, b) ∈ zip (inits tl) (tails  …
        right
        -- ⊢ ∃ a b, (a, b) ∈ zip (inits tl) (tails tl) ∧ Prod.map (fun t => hd :: t) id ( …
        use tl', tail
        -- ⊢ (tl', tail) ∈ zip (inits tl) (tails tl) ∧ Prod.map (fun t => hd :: t) id (tl …
        simp_all
        -- 🎉 no goals
#align list.mem_zip_inits_tails List.mem_zip_inits_tails

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : List α) (l' : List β) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' := by
  rw [zip]
  -- ⊢ map (Function.uncurry f) (zipWith Prod.mk l l') = zipWith f l l'
  induction' l with hd tl hl generalizing l'
  -- ⊢ map (Function.uncurry f) (zipWith Prod.mk [] l') = zipWith f [] l'
  · simp
    -- 🎉 no goals
  · cases' l' with hd' tl'
    -- ⊢ map (Function.uncurry f) (zipWith Prod.mk (hd :: tl) []) = zipWith f (hd ::  …
    · simp
      -- 🎉 no goals
    · simp [hl]
      -- 🎉 no goals
#align list.map_uncurry_zip_eq_zip_with List.map_uncurry_zip_eq_zipWith

@[simp]
theorem sum_zipWith_distrib_left {γ : Type*} [Semiring γ] (f : α → β → γ) (n : γ) (l : List α)
    (l' : List β) : (l.zipWith (fun x y => n * f x y) l').sum = n * (l.zipWith f l').sum := by
  induction' l with hd tl hl generalizing f n l'
  -- ⊢ sum (zipWith (fun x y => n * f x y) [] l') = n * sum (zipWith f [] l')
  · simp
    -- 🎉 no goals
  · cases' l' with hd' tl'
    -- ⊢ sum (zipWith (fun x y => n * f x y) (hd :: tl) []) = n * sum (zipWith f (hd  …
    · simp
      -- 🎉 no goals
    · simp [hl, mul_add]
      -- 🎉 no goals
#align list.sum_zip_with_distrib_left List.sum_zipWith_distrib_left

section Distrib

/-! ### Operations that can be applied before or after a `zip_with` -/


variable (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)

theorem zipWith_distrib_take : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  induction' l with hd tl hl generalizing l' n
  -- ⊢ take n (zipWith f [] l') = zipWith f (take n []) (take n l')
  · simp
    -- 🎉 no goals
  · cases l'
    -- ⊢ take n (zipWith f (hd :: tl) []) = zipWith f (take n (hd :: tl)) (take n [])
    · simp
      -- 🎉 no goals
    · cases n
      -- ⊢ take zero (zipWith f (hd :: tl) (head✝ :: tail✝)) = zipWith f (take zero (hd …
      · simp
        -- 🎉 no goals
      · simp [hl]
        -- 🎉 no goals
#align list.zip_with_distrib_take List.zipWith_distrib_take

theorem zipWith_distrib_drop : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) := by
  induction' l with hd tl hl generalizing l' n
  -- ⊢ drop n (zipWith f [] l') = zipWith f (drop n []) (drop n l')
  · simp
    -- 🎉 no goals
  · cases l'
    -- ⊢ drop n (zipWith f (hd :: tl) []) = zipWith f (drop n (hd :: tl)) (drop n [])
    · simp
      -- 🎉 no goals
    · cases n
      -- ⊢ drop zero (zipWith f (hd :: tl) (head✝ :: tail✝)) = zipWith f (drop zero (hd …
      · simp
        -- 🎉 no goals
      · simp [hl]
        -- 🎉 no goals
#align list.zip_with_distrib_drop List.zipWith_distrib_drop

theorem zipWith_distrib_tail : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  simp_rw [← drop_one, zipWith_distrib_drop]
  -- 🎉 no goals
#align list.zip_with_distrib_tail List.zipWith_distrib_tail

theorem zipWith_append (f : α → β → γ) (l la : List α) (l' lb : List β)
    (h : l.length = l'.length) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  induction' l with hd tl hl generalizing l'
  -- ⊢ zipWith f ([] ++ la) (l' ++ lb) = zipWith f [] l' ++ zipWith f la lb
  · have : l' = [] := eq_nil_of_length_eq_zero (by simpa using h.symm)
    -- ⊢ zipWith f ([] ++ la) (l' ++ lb) = zipWith f [] l' ++ zipWith f la lb
    simp [this]
    -- 🎉 no goals
  · cases l'
    -- ⊢ zipWith f (hd :: tl ++ la) ([] ++ lb) = zipWith f (hd :: tl) [] ++ zipWith f …
    · simp at h
      -- 🎉 no goals
    · simp only [add_left_inj, length] at h
      -- ⊢ zipWith f (hd :: tl ++ la) (head✝ :: tail✝ ++ lb) = zipWith f (hd :: tl) (he …
      simp [hl _ h]
      -- 🎉 no goals
#align list.zip_with_append List.zipWith_append

theorem zipWith_distrib_reverse (h : l.length = l'.length) :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse := by
  induction' l with hd tl hl generalizing l'
  -- ⊢ reverse (zipWith f [] l') = zipWith f (reverse []) (reverse l')
  · simp
    -- 🎉 no goals
  · cases' l' with hd' tl'
    -- ⊢ reverse (zipWith f (hd :: tl) []) = zipWith f (reverse (hd :: tl)) (reverse  …
    · simp
      -- 🎉 no goals
    · simp only [add_left_inj, length] at h
      -- ⊢ reverse (zipWith f (hd :: tl) (hd' :: tl')) = zipWith f (reverse (hd :: tl)) …
      have : tl.reverse.length = tl'.reverse.length := by simp [h]
      -- ⊢ reverse (zipWith f (hd :: tl) (hd' :: tl')) = zipWith f (reverse (hd :: tl)) …
      simp [hl _ h, zipWith_append _ _ _ _ _ this]
      -- 🎉 no goals
#align list.zip_with_distrib_reverse List.zipWith_distrib_reverse

end Distrib

section CommMonoid

variable [CommMonoid α]

@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    ∀ L L' : List α,
      L.prod * L'.prod =
        (zipWith (· * ·) L L').prod * (L.drop L'.length).prod * (L'.drop L.length).prod
  | [], ys => by simp [Nat.zero_le]
                 -- 🎉 no goals
  | xs, [] => by simp [Nat.zero_le]
                 -- 🎉 no goals
  | x :: xs, y :: ys => by
    simp only [drop, length, zipWith_cons_cons, prod_cons]
    -- ⊢ x * prod xs * (y * prod ys) = x * y * prod (zipWith (fun x x_1 => x * x_1) x …
    conv =>
      lhs; rw [mul_assoc]; right; rw [mul_comm, mul_assoc]; right
      rw [mul_comm, prod_mul_prod_eq_prod_zipWith_mul_prod_drop xs ys]
    simp only [add_eq, add_zero]
    -- ⊢ x * (y * (prod (zipWith (fun x x_1 => x * x_1) xs ys) * prod (drop (length y …
    ac_rfl
    -- 🎉 no goals
#align list.prod_mul_prod_eq_prod_zip_with_mul_prod_drop List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop
#align list.sum_add_sum_eq_sum_zip_with_add_sum_drop List.sum_add_sum_eq_sum_zipWith_add_sum_drop

@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith_of_length_eq (L L' : List α) (h : L.length = L'.length) :
    L.prod * L'.prod = (zipWith (· * ·) L L').prod := by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop L L').trans
  -- ⊢ prod (zipWith (fun x x_1 => x * x_1) L L') * prod (drop (length L') L) * pro …
  rw [← h, drop_length, h, drop_length, prod_nil, mul_one, mul_one]
  -- 🎉 no goals
#align list.prod_mul_prod_eq_prod_zip_with_of_length_eq List.prod_mul_prod_eq_prod_zipWith_of_length_eq
#align list.sum_add_sum_eq_sum_zip_with_of_length_eq List.sum_add_sum_eq_sum_zipWith_of_length_eq

end CommMonoid

end List
