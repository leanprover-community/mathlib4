/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range

#align_import data.list.indexes from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Lemmas about List.*Idx functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx` and `List.foldrIdx`.
-/


universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapIdx

-- Porting note: Add back old definition because it's easier for writing proofs.

/-- Lean3 `map_with_index` helper function -/
protected def oldMapIdxCore (f : ℕ → α → β) : ℕ → List α → List β
  | _, []      => []
  | k, a :: as => f k a :: List.oldMapIdxCore f (k + 1) as

/-- Given a function `f : ℕ → α → β` and `as : List α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
protected def oldMapIdx (f : ℕ → α → β) (as : List α) : List β :=
  List.oldMapIdxCore f 0 as

@[simp]
theorem mapIdx_nil {α β} (f : ℕ → α → β) : mapIdx f [] = [] :=
  rfl
#align list.map_with_index_nil List.mapIdx_nil

-- Porting note: new theorem.
protected theorem oldMapIdxCore_eq (l : List α) (f : ℕ → α → β) (n : ℕ) :
    l.oldMapIdxCore f n = l.oldMapIdx fun i a ↦ f (i + n) a := by
  induction' l with hd tl hl generalizing f n
  -- ⊢ List.oldMapIdxCore f n [] = List.oldMapIdx (fun i a => f (i + n) a) []
  · rfl
    -- 🎉 no goals
  · rw [List.oldMapIdx]
    -- ⊢ List.oldMapIdxCore f n (hd :: tl) = List.oldMapIdxCore (fun i a => f (i + n) …
    simp only [List.oldMapIdxCore, hl, add_left_comm, add_comm, add_zero, zero_add]
    -- 🎉 no goals
#noalign list.map_with_index_core_eq

-- Porting note: convert new definition to old definition.
--   A few new theorems are added to achieve this
--   1. Prove that `oldMapIdxCore f (l ++ [e]) = oldMapIdxCore f l ++ [f l.length e]`
--   2. Prove that `oldMapIdx f (l ++ [e]) = oldMapIdx f l ++ [f l.length e]`
--   3. Prove list induction using `∀ l e, p [] → (p l → p (l ++ [e])) → p l`
-- Porting note: new theorem.
theorem list_reverse_induction (p : List α → Prop) (base : p [])
    (ind : ∀ (l : List α) (e : α), p l → p (l ++ [e])) : (∀ (l : List α), p l) := by
  let q := fun l ↦ p (reverse l)
  -- ⊢ ∀ (l : List α), p l
  have pq : ∀ l, p (reverse l) → q l := by simp only [reverse_reverse]; intro; exact id
  -- ⊢ ∀ (l : List α), p l
  have qp : ∀ l, q (reverse l) → p l := by simp only [reverse_reverse]; intro; exact id
  -- ⊢ ∀ (l : List α), p l
  intro l
  -- ⊢ p l
  apply qp
  -- ⊢ q (reverse l)
  generalize (reverse l) = l
  -- ⊢ q l
  induction' l with head tail ih
  -- ⊢ q []
  · apply pq; simp only [reverse_nil, base]
    -- ⊢ p (reverse [])
              -- 🎉 no goals
  · apply pq; simp only [reverse_cons]; apply ind; apply qp; rw [reverse_reverse]; exact ih
    -- ⊢ p (reverse (head :: tail))
              -- ⊢ p (reverse tail ++ [head])
                                        -- ⊢ p (reverse tail)
                                                   -- ⊢ q (reverse (reverse tail))
                                                             -- ⊢ q tail
                                                                                   -- 🎉 no goals

-- Porting note: new theorem.
protected theorem oldMapIdxCore_append : ∀ (f : ℕ → α → β) (n : ℕ) (l₁ l₂ : List α),
    List.oldMapIdxCore f n (l₁ ++ l₂) =
    List.oldMapIdxCore f n l₁ ++ List.oldMapIdxCore f (n + l₁.length) l₂ := by
  intros f n l₁ l₂
  -- ⊢ List.oldMapIdxCore f n (l₁ ++ l₂) = List.oldMapIdxCore f n l₁ ++ List.oldMap …
  generalize e : (l₁ ++ l₂).length = len
  -- ⊢ List.oldMapIdxCore f n (l₁ ++ l₂) = List.oldMapIdxCore f n l₁ ++ List.oldMap …
  revert n l₁ l₂
  -- ⊢ ∀ (n : ℕ) (l₁ l₂ : List α), length (l₁ ++ l₂) = len → List.oldMapIdxCore f n …
  induction' len with len ih <;> intros n l₁ l₂ h
  -- ⊢ ∀ (n : ℕ) (l₁ l₂ : List α), length (l₁ ++ l₂) = Nat.zero → List.oldMapIdxCor …
                                 -- ⊢ List.oldMapIdxCore f n (l₁ ++ l₂) = List.oldMapIdxCore f n l₁ ++ List.oldMap …
                                 -- ⊢ List.oldMapIdxCore f n (l₁ ++ l₂) = List.oldMapIdxCore f n l₁ ++ List.oldMap …
  · have l₁_nil : l₁ = [] := by cases l₁; rfl; contradiction
    -- ⊢ List.oldMapIdxCore f n (l₁ ++ l₂) = List.oldMapIdxCore f n l₁ ++ List.oldMap …
    have l₂_nil : l₂ = [] := by cases l₂; rfl; rw [List.length_append] at h; contradiction
    -- ⊢ List.oldMapIdxCore f n (l₁ ++ l₂) = List.oldMapIdxCore f n l₁ ++ List.oldMap …
    simp only [l₁_nil, l₂_nil]; rfl
    -- ⊢ List.oldMapIdxCore f n ([] ++ []) = List.oldMapIdxCore f n [] ++ List.oldMap …
                                -- 🎉 no goals
  · cases' l₁ with head tail
    -- ⊢ List.oldMapIdxCore f n ([] ++ l₂) = List.oldMapIdxCore f n [] ++ List.oldMap …
    · rfl
      -- 🎉 no goals
    · simp only [List.oldMapIdxCore, List.append_eq, length_cons, cons_append,cons.injEq, true_and]
      -- ⊢ List.oldMapIdxCore f (n + 1) (tail ++ l₂) = List.oldMapIdxCore f (n + 1) tai …
      suffices : n + Nat.succ (length tail) = n + 1 + tail.length
      -- ⊢ List.oldMapIdxCore f (n + 1) (tail ++ l₂) = List.oldMapIdxCore f (n + 1) tai …
      { rw [this]
        apply ih (n + 1) _ _ _
        simp only [cons_append, length_cons, length_append, Nat.succ.injEq] at h
        simp only [length_append, h] }
      { rw [Nat.add_assoc]; simp only [Nat.add_comm] }
      -- 🎉 no goals

-- Porting note: new theorem.
protected theorem oldMapIdx_append : ∀ (f : ℕ → α → β) (l : List α) (e : α),
    List.oldMapIdx f (l ++ [e]) = List.oldMapIdx f l ++ [f l.length e] := by
  intros f l e
  -- ⊢ List.oldMapIdx f (l ++ [e]) = List.oldMapIdx f l ++ [f (length l) e]
  unfold List.oldMapIdx
  -- ⊢ List.oldMapIdxCore f 0 (l ++ [e]) = List.oldMapIdxCore f 0 l ++ [f (length l …
  rw [List.oldMapIdxCore_append f 0 l [e]]
  -- ⊢ List.oldMapIdxCore f 0 l ++ List.oldMapIdxCore f (0 + length l) [e] = List.o …
  simp only [zero_add, append_cancel_left_eq]; rfl
  -- ⊢ List.oldMapIdxCore f (length l) [e] = [f (length l) e]
                                               -- 🎉 no goals

-- Porting note: new theorem.
theorem mapIdxGo_append : ∀ (f : ℕ → α → β) (l₁ l₂ : List α) (arr : Array β),
    mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (List.toArray (mapIdx.go f l₁ arr)) := by
  intros f l₁ l₂ arr
  -- ⊢ mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f l₁ arr))
  generalize e : (l₁ ++ l₂).length = len
  -- ⊢ mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f l₁ arr))
  revert l₁ l₂ arr
  -- ⊢ ∀ (l₁ l₂ : List α) (arr : Array β), length (l₁ ++ l₂) = len → mapIdx.go f (l …
  induction' len with len ih <;> intros l₁ l₂ arr h
  -- ⊢ ∀ (l₁ l₂ : List α) (arr : Array β), length (l₁ ++ l₂) = Nat.zero → mapIdx.go …
                                 -- ⊢ mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f l₁ arr))
                                 -- ⊢ mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f l₁ arr))
  · have l₁_nil : l₁ = [] := by cases l₁; rfl; contradiction
    -- ⊢ mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f l₁ arr))
    have l₂_nil : l₂ = [] := by cases l₂; rfl; rw [List.length_append] at h; contradiction
    -- ⊢ mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f l₁ arr))
    rw [l₁_nil, l₂_nil]; simp only [mapIdx.go, Array.toList_eq, Array.toArray_data]
    -- ⊢ mapIdx.go f ([] ++ []) arr = mapIdx.go f [] (toArray (mapIdx.go f [] arr))
                         -- 🎉 no goals
  · cases' l₁ with head tail <;> simp only [mapIdx.go]
    -- ⊢ mapIdx.go f ([] ++ l₂) arr = mapIdx.go f l₂ (toArray (mapIdx.go f [] arr))
                                 -- ⊢ mapIdx.go f ([] ++ l₂) arr = mapIdx.go f l₂ (toArray (Array.toList arr))
                                 -- ⊢ mapIdx.go f (List.append tail l₂) (Array.push arr (f (Array.size arr) head)) …
    · simp only [nil_append, Array.toList_eq, Array.toArray_data]
      -- 🎉 no goals
    · simp only [List.append_eq]
      -- ⊢ mapIdx.go f (tail ++ l₂) (Array.push arr (f (Array.size arr) head)) = mapIdx …
      rw [ih]
      -- ⊢ length (tail ++ l₂) = len
      · simp only [cons_append, length_cons, length_append, Nat.succ.injEq] at h
        -- ⊢ length (tail ++ l₂) = len
        simp only [length_append, h]
        -- 🎉 no goals

-- Porting note: new theorem.
theorem mapIdxGo_length : ∀ (f : ℕ → α → β) (l : List α) (arr : Array β),
    length (mapIdx.go f l arr) = length l + arr.size := by
  intro f l
  -- ⊢ ∀ (arr : Array β), length (mapIdx.go f l arr) = length l + Array.size arr
  induction' l with head tail ih
  -- ⊢ ∀ (arr : Array β), length (mapIdx.go f [] arr) = length [] + Array.size arr
  · intro; simp only [mapIdx.go, Array.toList_eq, length_nil, zero_add]
    -- ⊢ length (mapIdx.go f [] arr✝) = length [] + Array.size arr✝
           -- 🎉 no goals
  · intro; simp only [mapIdx.go]; rw [ih]; simp only [Array.size_push, length_cons];
    -- ⊢ length (mapIdx.go f (head :: tail) arr✝) = length (head :: tail) + Array.siz …
           -- ⊢ length (mapIdx.go f tail (Array.push arr✝ (f (Array.size arr✝) head))) = len …
                                  -- ⊢ length tail + Array.size (Array.push arr✝ (f (Array.size arr✝) head)) = leng …
                                           -- ⊢ length tail + (Array.size arr✝ + 1) = Nat.succ (length tail) + Array.size arr✝
    simp only [Nat.add_succ, add_zero, Nat.add_comm]
    -- 🎉 no goals

-- Porting note: new theorem.
theorem mapIdx_append_one : ∀ (f : ℕ → α → β) (l : List α) (e : α),
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] := by
  intros f l e
  -- ⊢ mapIdx f (l ++ [e]) = mapIdx f l ++ [f (length l) e]
  unfold mapIdx
  -- ⊢ mapIdx.go f (l ++ [e]) #[] = mapIdx.go f l #[] ++ [f (length l) e]
  rw [mapIdxGo_append f l [e]]
  -- ⊢ mapIdx.go f [e] (toArray (mapIdx.go f l #[])) = mapIdx.go f l #[] ++ [f (len …
  simp only [mapIdx.go, Array.size_toArray, mapIdxGo_length, length_nil, add_zero, Array.toList_eq,
    Array.push_data, Array.data_toArray]

-- Porting note: new theorem.
protected theorem new_def_eq_old_def :
    ∀ (f : ℕ → α → β) (l : List α), l.mapIdx f = List.oldMapIdx f l := by
  intro f
  -- ⊢ ∀ (l : List α), mapIdx f l = List.oldMapIdx f l
  apply list_reverse_induction
  -- ⊢ mapIdx f [] = List.oldMapIdx f []
  · rfl
    -- 🎉 no goals
  · intro l e h
    -- ⊢ mapIdx f (l ++ [e]) = List.oldMapIdx f (l ++ [e])
    rw [List.oldMapIdx_append, mapIdx_append_one, h]
    -- 🎉 no goals

@[local simp]
theorem map_enumFrom_eq_zipWith : ∀ (l : List α) (n : ℕ) (f : ℕ → α → β),
    map (uncurry f) (enumFrom n l) = zipWith (fun i ↦ f (i + n)) (range (length l)) l := by
  intro l
  -- ⊢ ∀ (n : ℕ) (f : ℕ → α → β), map (uncurry f) (enumFrom n l) = zipWith (fun i = …
  generalize e : l.length = len
  -- ⊢ ∀ (n : ℕ) (f : ℕ → α → β), map (uncurry f) (enumFrom n l) = zipWith (fun i = …
  revert l
  -- ⊢ ∀ (l : List α), length l = len → ∀ (n : ℕ) (f : ℕ → α → β), map (uncurry f)  …
  induction' len with len ih <;> intros l e n f
  -- ⊢ ∀ (l : List α), length l = Nat.zero → ∀ (n : ℕ) (f : ℕ → α → β), map (uncurr …
                                 -- ⊢ map (uncurry f) (enumFrom n l) = zipWith (fun i => f (i + n)) (range Nat.zer …
                                 -- ⊢ map (uncurry f) (enumFrom n l) = zipWith (fun i => f (i + n)) (range (Nat.su …
  · have : l = [] := by cases l; rfl; contradiction
    -- ⊢ map (uncurry f) (enumFrom n l) = zipWith (fun i => f (i + n)) (range Nat.zer …
    rw [this]; rfl
    -- ⊢ map (uncurry f) (enumFrom n []) = zipWith (fun i => f (i + n)) (range Nat.ze …
               -- 🎉 no goals
  · cases' l with head tail
    -- ⊢ map (uncurry f) (enumFrom n []) = zipWith (fun i => f (i + n)) (range (Nat.s …
    · contradiction
      -- 🎉 no goals
    · simp only [map, uncurry_apply_pair, range_succ_eq_map, zipWith, zero_add, zipWith_map_left]
      -- ⊢ f n head :: map (uncurry f) (enumFrom (n + 1) tail) = f n head :: zipWith (( …
      rw [ih]
      -- ⊢ f n head :: zipWith (fun i => f (i + (n + 1))) (range len) tail = f n head : …
      suffices : (fun i ↦ f (i + (n + 1))) = ((fun i ↦ f (i + n)) ∘ Nat.succ)
      rw [this]
      -- ⊢ (fun i => f (i + (n + 1))) = (fun i => f (i + n)) ∘ Nat.succ
      funext n' a
      -- ⊢ f (n' + (n + 1)) a = ((fun i => f (i + n)) ∘ Nat.succ) n' a
      simp only [comp, Nat.add_assoc, Nat.add_comm, Nat.add_succ]
      -- ⊢ length tail = len
      simp only [length_cons, Nat.succ.injEq] at e; exact e
      -- ⊢ length tail = len
                                                    -- 🎉 no goals

theorem mapIdx_eq_enum_map (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = l.enum.map (Function.uncurry f) := by
  rw [List.new_def_eq_old_def]
  -- ⊢ List.oldMapIdx f l = map (uncurry f) (enum l)
  induction' l with hd tl hl generalizing f
  -- ⊢ List.oldMapIdx f [] = map (uncurry f) (enum [])
  · rfl
    -- 🎉 no goals
  · rw [List.oldMapIdx, List.oldMapIdxCore, List.oldMapIdxCore_eq, hl]
    -- ⊢ f 0 hd :: map (uncurry fun i a => f (i + (0 + 1)) a) (enum tl) = map (uncurr …
    simp [enum_eq_zip_range, map_uncurry_zip_eq_zipWith]
    -- 🎉 no goals
#align list.map_with_index_eq_enum_map List.mapIdx_eq_enum_map

@[simp]
theorem mapIdx_cons {α β} (l : List α) (f : ℕ → α → β) (a : α) :
    mapIdx f (a :: l) = f 0 a :: mapIdx (fun i ↦ f (i + 1)) l := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zipWith,
    range_succ_eq_map, zipWith_map_left]
#align list.map_with_index_cons List.mapIdx_cons

theorem mapIdx_append {α} (K L : List α) (f : ℕ → α → β) :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i a ↦ f (i + K.length) a := by
  induction' K with a J IH generalizing f
  -- ⊢ mapIdx f ([] ++ L) = mapIdx f [] ++ mapIdx (fun i a => f (i + length []) a) L
  · rfl
    -- 🎉 no goals
  · simp [IH fun i ↦ f (i + 1), add_assoc]
    -- 🎉 no goals
#align list.map_with_index_append List.mapIdx_append

@[simp]
theorem length_mapIdx {α β} (l : List α) (f : ℕ → α → β) : (l.mapIdx f).length = l.length := by
  induction' l with hd tl IH generalizing f
  -- ⊢ length (mapIdx f []) = length []
  · rfl
    -- 🎉 no goals
  · simp [IH]
    -- 🎉 no goals
#align list.length_map_with_index List.length_mapIdx

@[simp, deprecated]
theorem nthLe_mapIdx {α β} (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapIdx f).length := h.trans_le (l.length_mapIdx f).ge) :
    (l.mapIdx f).nthLe i h' = f i (l.nthLe i h) := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range]
  -- 🎉 no goals
#align list.nth_le_map_with_index List.nthLe_mapIdx

-- Porting note: Changed the type to use `List.get` instead of deprecated `List.nthLe`.
theorem mapIdx_eq_ofFn {α β} (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length ↦ f (i : ℕ) (l.get i) := by
  induction' l with hd tl IH generalizing f
  -- ⊢ mapIdx f [] = ofFn fun i => f (↑i) (get [] i)
  · rfl
    -- 🎉 no goals
  · simp [IH]
    -- 🎉 no goals
#align list.map_with_index_eq_of_fn List.mapIdx_eq_ofFn

end MapIdx

section FoldrIdx

-- Porting note: Changed argument order of `foldrIdxSpec` to align better with `foldrIdx`.
/-- Specification of `foldrIdx`. -/
def foldrIdxSpec (f : ℕ → α → β → β) (b : β) (as : List α) (start : ℕ) : β :=
  foldr (uncurry f) b <| enumFrom start as
#align list.foldr_with_index_aux_spec List.foldrIdxSpecₓ

theorem foldrIdxSpec_cons (f : ℕ → α → β → β) (b a as start) :
    foldrIdxSpec f b (a :: as) start = f start a (foldrIdxSpec f b as (start + 1)) :=
  rfl
#align list.foldr_with_index_aux_spec_cons List.foldrIdxSpec_consₓ

theorem foldrIdx_eq_foldrIdxSpec (f : ℕ → α → β → β) (b as start) :
    foldrIdx f b as start = foldrIdxSpec f b as start := by
  induction as generalizing start
  -- ⊢ foldrIdx f b [] start = foldrIdxSpec f b [] start
  · rfl
    -- 🎉 no goals
  · simp only [foldrIdx, foldrIdxSpec_cons, *]
    -- 🎉 no goals
#align list.foldr_with_index_aux_eq_foldr_with_index_aux_spec List.foldrIdx_eq_foldrIdxSpecₓ

theorem foldrIdx_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrIdx f b as = foldr (uncurry f) b (enum as) := by
  simp only [foldrIdx, foldrIdxSpec, foldrIdx_eq_foldrIdxSpec, enum]
  -- 🎉 no goals
#align list.foldr_with_index_eq_foldr_enum List.foldrIdx_eq_foldr_enum

end FoldrIdx

theorem indexesValues_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filter (p ∘ Prod.snd) (enum as) := by
  simp [indexesValues, foldrIdx_eq_foldr_enum, uncurry, filter_eq_foldr]
  -- 🎉 no goals
#align list.indexes_values_eq_filter_enum List.indexesValues_eq_filter_enum

theorem findIdxs_eq_map_indexesValues (p : α → Prop) [DecidablePred p] (as : List α) :
    findIdxs p as = map Prod.fst (indexesValues p as) := by
  simp only [indexesValues_eq_filter_enum, map_filter_eq_foldr, findIdxs, uncurry,
    foldrIdx_eq_foldr_enum, decide_eq_true_eq, comp_apply, Bool.cond_decide]
#align list.find_indexes_eq_map_indexes_values List.findIdxs_eq_map_indexesValues

section FoldlIdx

-- Porting note: Changed argument order of `foldlIdxSpec` to align better with `foldlIdx`.
/-- Specification of `foldlIdx`. -/
def foldlIdxSpec (f : ℕ → α → β → α) (a : α) (bs : List β) (start : ℕ) : α :=
  foldl (fun a p ↦ f p.fst a p.snd) a <| enumFrom start bs
#align list.foldl_with_index_aux_spec List.foldlIdxSpecₓ

theorem foldlIdxSpec_cons (f : ℕ → α → β → α) (a b bs start) :
    foldlIdxSpec f a (b :: bs) start = foldlIdxSpec f (f start a b) bs (start + 1) :=
  rfl
#align list.foldl_with_index_aux_spec_cons List.foldlIdxSpec_consₓ

theorem foldlIdx_eq_foldlIdxSpec (f : ℕ → α → β → α) (a bs start) :
    foldlIdx f a bs start = foldlIdxSpec f a bs start := by
  induction bs generalizing start a
  -- ⊢ foldlIdx f a [] start = foldlIdxSpec f a [] start
  · rfl
    -- 🎉 no goals
  · simp [foldlIdxSpec, *]
    -- 🎉 no goals
#align list.foldl_with_index_aux_eq_foldl_with_index_aux_spec List.foldlIdx_eq_foldlIdxSpecₓ

theorem foldlIdx_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlIdx f a bs = foldl (fun a p ↦ f p.fst a p.snd) a (enum bs) := by
  simp only [foldlIdx, foldlIdxSpec, foldlIdx_eq_foldlIdxSpec, enum]
  -- 🎉 no goals
#align list.foldl_with_index_eq_foldl_enum List.foldlIdx_eq_foldl_enum

end FoldlIdx

section FoldIdxM

-- Porting note: `foldrM_eq_foldr` now depends on `[LawfulMonad m]`
variable {m : Type u → Type v} [Monad m]

theorem foldrIdxM_eq_foldrM_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) [LawfulMonad m] :
    foldrIdxM f b as = foldrM (uncurry f) b (enum as) := by
  simp only [foldrIdxM, foldrM_eq_foldr, foldrIdx_eq_foldr_enum, uncurry]
  -- 🎉 no goals
#align list.mfoldr_with_index_eq_mfoldr_enum List.foldrIdxM_eq_foldrM_enum

theorem foldlIdxM_eq_foldlM_enum [LawfulMonad m] {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    foldlIdxM f b as = List.foldlM (fun b p ↦ f p.fst b p.snd) b (enum as) := by
  rw [foldlIdxM, foldlM_eq_foldl, foldlIdx_eq_foldl_enum]
  -- 🎉 no goals
#align list.mfoldl_with_index_eq_mfoldl_enum List.foldlIdxM_eq_foldlM_enum

end FoldIdxM

section MapIdxM

-- Porting note: `[Applicative m]` replaced by `[Monad m] [LawfulMonad m]`
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Specification of `mapIdxMAux`. -/
def mapIdxMAuxSpec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverse (uncurry f) <| enumFrom start as
#align list.mmap_with_index_aux_spec List.mapIdxMAuxSpec

-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.
theorem mapIdxMAuxSpec_cons {α β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mapIdxMAuxSpec f start (a :: as) = cons <$> f start a <*> mapIdxMAuxSpec f (start + 1) as :=
  rfl
#align list.mmap_with_index_aux_spec_cons List.mapIdxMAuxSpec_cons

theorem mapIdxMGo_eq_mapIdxMAuxSpec {α β} (f : ℕ → α → m β) (arr : Array β) (as : List α) :
    mapIdxM.go f as arr = (arr.toList ++ ·) <$> mapIdxMAuxSpec f arr.size as := by
  generalize e : as.length = len
  -- ⊢ mapIdxM.go f as arr = (fun x => Array.toList arr ++ x) <$> mapIdxMAuxSpec f  …
  revert as arr
  -- ⊢ ∀ (arr : Array β) (as : List α), length as = len → mapIdxM.go f as arr = (fu …
  induction' len with len ih <;> intro arr as h
  -- ⊢ ∀ (arr : Array β) (as : List α), length as = Nat.zero → mapIdxM.go f as arr  …
                                 -- ⊢ mapIdxM.go f as arr = (fun x => Array.toList arr ++ x) <$> mapIdxMAuxSpec f  …
                                 -- ⊢ mapIdxM.go f as arr = (fun x => Array.toList arr ++ x) <$> mapIdxMAuxSpec f  …
  · have : as = [] := by cases as; rfl; contradiction
    -- ⊢ mapIdxM.go f as arr = (fun x => Array.toList arr ++ x) <$> mapIdxMAuxSpec f  …
    simp only [this, mapIdxM.go, mapIdxMAuxSpec, List.traverse, map_pure, append_nil]
    -- 🎉 no goals
  · match as with
    | nil => contradiction
    | cons head tail =>
      simp only [length_cons, Nat.succ.injEq] at h
      simp only [mapIdxM.go, mapIdxMAuxSpec_cons, map_eq_pure_bind, seq_eq_bind_map,
        LawfulMonad.bind_assoc, pure_bind]
      congr
      conv => { lhs; intro x; rw [ih _ _ h]; }
      funext x
      simp only [Array.toList_eq, Array.push_data, append_assoc, singleton_append, Array.size_push,
        map_eq_pure_bind]
#align list.mmap_with_index_aux_eq_mmap_with_index_aux_spec List.mapIdxMGo_eq_mapIdxMAuxSpec

theorem mapIdxM_eq_mmap_enum {α β} (f : ℕ → α → m β) (as : List α) :
    as.mapIdxM f = List.traverse (uncurry f) (enum as) := by
  simp only [mapIdxM, mapIdxMGo_eq_mapIdxMAuxSpec, Array.toList_eq, Array.data_toArray,
    nil_append, mapIdxMAuxSpec, Array.size_toArray, length_nil, id_map', enum]
#align list.mmap_with_index_eq_mmap_enum List.mapIdxM_eq_mmap_enum

end MapIdxM

section MapIdxM'

-- Porting note: `[Applicative m] [LawfulApplicative m]` replaced by [Monad m] [LawfulMonad m]
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

theorem mapIdxMAux'_eq_mapIdxMGo {α} (f : ℕ → α → m PUnit) (as : List α) (arr : Array PUnit) :
    mapIdxMAux' f arr.size as = mapIdxM.go f as arr *> pure PUnit.unit := by
  revert arr
  -- ⊢ ∀ (arr : Array PUnit), mapIdxMAux' f (Array.size arr) as = SeqRight.seqRight …
  induction' as with head tail ih <;> intro arr
  -- ⊢ ∀ (arr : Array PUnit), mapIdxMAux' f (Array.size arr) [] = SeqRight.seqRight …
                                      -- ⊢ mapIdxMAux' f (Array.size arr) [] = SeqRight.seqRight (mapIdxM.go f [] arr)  …
                                      -- ⊢ mapIdxMAux' f (Array.size arr) (head :: tail) = SeqRight.seqRight (mapIdxM.g …
  · simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
    -- 🎉 no goals
  · simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go, seq_pure]
    generalize (f (Array.size arr) head) = head
    -- ⊢ (do
    let arr_1 := arr.push ⟨⟩
    -- ⊢ (do
    have : arr_1.size = arr.size + 1 := Array.size_push arr ⟨⟩
    -- ⊢ (do
    rw [← this, ih arr_1]
    -- ⊢ (do
    simp only [seqRight_eq, map_eq_pure_bind, seq_pure, LawfulMonad.bind_assoc, pure_bind]
    -- 🎉 no goals
#align list.mmap_with_index'_aux_eq_mmap_with_index_aux List.mapIdxMAux'_eq_mapIdxMGo

theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM as f *> pure PUnit.unit :=
  mapIdxMAux'_eq_mapIdxMGo f as #[]
#align list.mmap_with_index'_eq_mmap_with_index List.mapIdxM'_eq_mapIdxM

end MapIdxM'

end List
