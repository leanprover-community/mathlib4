/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg

! This file was ported from Lean 3 source module data.list.indexes
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range

/-!
# Lemmas about List.*_with_index functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx`
and `List.foldrIdx`.
-/


universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapWithIndex

-- Porting note: Add back old definition because it's easier for writing proofs.

/-- Lean3 map_with_index helper function -/
def map_with_index_core (f : ℕ → α → β) : ℕ → List α → List β
  | _, []      => []
  | k, (a::as) => f k a::(map_with_index_core f (k+1) as)

/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def map_with_index (f : ℕ → α → β) (as : List α) : List β :=
  map_with_index_core f 0 as

@[simp]
theorem mapIdx_nil {α β} (f : ℕ → α → β) : mapIdx f [] = [] :=
  rfl
#align list.map_with_index_nil List.mapIdx_nil

theorem mapIdx_core_eq (l : List α) (f : ℕ → α → β) (n : ℕ) :
    l.map_with_index_core f n = l.map_with_index fun i a => f (i + n) a := by
  induction' l with hd tl hl generalizing f n
  · rfl
  · rw [map_with_index]
    simp [map_with_index_core, hl, add_left_comm, add_assoc, add_comm]
#align list.map_with_index_core_eq List.mapIdx_core_eq

-- Porting note: convert new definition to old definition.
--   A few new theorem are added to archive this
--   1. Prove that map_with_index_core f (l++[e]) = map_with_index_core l ++ [f l.length e]
--   2. Prove that mapIdx f (l ++ [e])            = mapIdx l              ++ [f l.length e]
--   3. Prove list induction using ∀ l e, p [] → (p l → p (l ++ [e])) → p l
-- Porting note: new theorem.
theorem list_reverse_induction (p : List α → Prop) :
  (p []) → (∀ (l : List α) (e : α), p l → p (l ++ [e])) → (∀ (l : List α), p l) := by
  let q := λ l ↦ p (reverse l)
  have pq : ∀ l, p (reverse l) → q l := by simp only [reverse_reverse]; intro; exact id
  have qp : ∀ l, q (reverse l) → p l := by simp only [reverse_reverse]; intro; exact id
  intros base ind l
  apply qp
  generalize (reverse l) = l
  induction' l with head tail ih
  · apply pq; simp only [reverse_nil, base]
  · apply pq; simp only [reverse_cons]; apply ind; apply qp; rw [reverse_reverse]; exact ih

-- Porting note: new theorem.
theorem length_eq_0_iff_nil : ∀ {α : Type} (l : List α), length l = 0 ↔ l = [] := by
  intros α l
  cases l
  simp only [length_nil]
  simp only [length_cons]

-- Porting note: new theorem.
theorem nil_append_nil : ∀ {α : Type} (l₁ l₂ : List α), l₁ ++ l₂ = [] ↔ l₁ = [] ∧ l₂ = [] := by
  simp only [append_eq_nil, forall_const]

-- Porting note: new theorem.
theorem map_with_index_core_append : ∀ (f : ℕ → α → β) (n : ℕ) (l₁ l₂ : List α),
  map_with_index_core f n (l₁ ++ l₂) =
  map_with_index_core f n l₁ ++ map_with_index_core f (n + l₁.length) l₂ := by
  intros f n l₁ l₂
  generalize e : (l₁++l₂).length = len
  revert n l₁ l₂
  induction' len with len ih <;> intros n l₁ l₂ h
  · have l₁_nil : l₁ = [] := by cases l₁; rfl; contradiction
    have l₂_nil : l₂ = [] := by cases l₂; rfl; rw [List.length_append] at h; contradiction
    simp only [l₁_nil, l₂_nil]; rfl
  · cases' l₁ with head tail
    · trivial -- · simp [map_with_index_core]; rw [(ih (n+1) tail l₂ _)]; simp
    · simp only [map_with_index_core, List.append_eq, length_cons, cons_append,cons.injEq, true_and]
      suffices : n + Nat.succ (length tail) = n + 1 + tail.length
      { rw [this]
        apply ih (n+1) _ _ _
        simp at h; simp [h] }
      { rw [Nat.add_assoc]; simp only [Nat.add_comm] }

-- Porting note: new theorem.
theorem map_with_index_append : ∀ (f : ℕ → α → β) (l : List α) (e : α),
  map_with_index f (l ++ [e]) = map_with_index f l ++ [f l.length e] := by
  intros f l e
  unfold map_with_index
  rw [(map_with_index_core_append f 0 l [e])]
  simp; rfl

-- Porting note: new theorem.
theorem mapIdx_go_append : ∀ (f : ℕ → α → β) (l₁ l₂ : List α) (arr : Array β),
  mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (List.toArray (mapIdx.go f l₁ arr)) := by
  intros f l₁ l₂ arr
  generalize e : (l₁++l₂).length = len
  revert l₁ l₂ arr
  induction' len with len ih <;> intros l₁ l₂ arr h
  · have l₁_nil : l₁ = [] := by cases l₁; rfl; contradiction
    have l₂_nil : l₂ = [] := by cases l₂; rfl; rw [List.length_append] at h; contradiction
    rw [l₁_nil, l₂_nil]; simp only [mapIdx.go, Array.toList_eq, Array.toArray_data]
  · cases' l₁ with head tail <;> simp only [mapIdx.go]
    · simp only [nil_append, Array.toList_eq, Array.toArray_data]
    · simp only [List.append_eq]
      rw [ih]
      · simp only [cons_append, length_cons, length_append, Nat.succ.injEq] at h
        simp only [length_append, h]

-- Porting note: new theorem.
theorem mapIdx.go_length : ∀ (f : ℕ → α → β) (l : List α) (arr : Array β),
  length (mapIdx.go f l arr) = length l + arr.size := by
  intro f l
  induction' l with head tail ih
  · intros; simp only [go, Array.toList_eq, length_nil, zero_add]
  · intro arr; simp only [go]; rw [ih]; simp only [Array.size_push, length_cons];
    simp only [Nat.add_succ, add_zero, Nat.add_comm]

-- Porting note: new theorem.
theorem mapIdx_length : ∀ (f : ℕ → α → β) (l : List α), length (mapIdx f l) = length l := by
  intros; simp only [mapIdx]; rw [mapIdx.go_length]; rfl

-- Porting note: new theorem.
theorem mapIdx_append : ∀ (f : ℕ → α → β) (l : List α) (e : α),
  mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] := by
  intros f l e
  unfold mapIdx
  rw [(mapIdx_go_append f l [e])]
  simp only [mapIdx.go, Array.size_toArray, mapIdx.go_length, length_nil, add_zero, Array.toList_eq,
             Array.push_data, Array.data_toArray]

-- Porting note: new theorem.
theorem new_def_eq_old_def: ∀ (f : ℕ → α → β) (l : List α), l.mapIdx f = map_with_index f l := by
  intro f
  apply list_reverse_induction
  · rfl
  · intro l e h
    rw [map_with_index_append, mapIdx_append, h]

theorem mapIdx_eq_enum_map (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = l.enum.map (Function.uncurry f) := by
  induction' l with hd tl hl generalizing f
  · simp only [mapIdx_nil, map]
  · rw [mapIdx, mapIdx.go, map_with_index_core_eq, hl]
    simp [enum_eq_zip_range, range_succ_eq_map, zip_with_map_left, map_uncurry_zip_eq_zip_with]
#align list.map_with_index_eq_enum_map List.mapIdx_eq_enum_map

@[simp]
theorem mapIdx_cons {α β} (l : List α) (f : ℕ → α → β) (a : α) :
    mapIdx f (a :: l) = f 0 a :: mapIdx (fun i => f (i + 1)) l := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zipWith,
    range_succ_eq_map, zipWith_map_left]
#align list.map_with_index_cons List.mapIdx_cons

theorem mapIdx_append {α} (K L : List α) (f : ℕ → α → β) :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i a => f (i + K.length) a := by
  induction' K with a J IH generalizing f
  · rfl
  · simp [IH fun i => f (i + 1), add_assoc]
#align list.map_with_index_append List.mapIdx_append

@[simp]
theorem length_mapIdx {α β} (l : List α) (f : ℕ → α → β) : (l.mapIdx f).length = l.length := by
  induction' l with hd tl IH generalizing f
  · rfl
  · simp [IH]
#align list.length_map_with_index List.length_mapIdx

@[simp, deprecated]
theorem nthLe_mapIdx {α β} (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapIdx f).length := h.trans_le (l.length_mapIdx f).ge) :
    (l.mapIdx f).nthLe i h' = f i (l.nthLe i h) := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range]
#align list.nth_le_map_with_index List.nthLe_mapIdx

-- Porting note: Changed the type to use `List.get` instead of deprecated `List.nthLe`.
theorem mapIdx_eq_ofFn {α β} (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length => f (i : ℕ) (l.get i) := by
  induction' l with hd tl IH generalizing f
  · rfl
  · simp [IH]
#align list.map_with_index_eq_of_fn List.mapIdx_eq_ofFn

end MapWithIndex

section FoldrWithIndex

-- Porting note: Changed argument order of `foldrIdxSpec` to align better with `foldrIdx`.
/-- Specification of `foldr_with_index_aux`. -/
def foldrIdxSpec (f : ℕ → α → β → β) (b : β) (as : List α) (start : ℕ) : β :=
  foldr (uncurry f) b <| enumFrom start as
#align list.foldr_with_index_aux_spec List.foldrIdxSpecₓ

theorem foldrIdxSpec_cons (f : ℕ → α → β → β) (b a as start) :
    foldrIdxSpec f b (a :: as) start =
      f start a (foldrIdxSpec f b as (start + 1)) :=
  rfl
#align list.foldr_with_index_aux_spec_cons List.foldrIdxSpec_consₓ

theorem foldrIdx_eq_foldrIdxSpec (f : ℕ → α → β → β) (start b as) :
    foldrIdx f b as start = foldrIdxSpec f b as start := by
  induction as generalizing start
  · rfl
  · simp only [foldrIdx, foldrIdxSpec_cons, *]
#align list.foldr_with_index_aux_eq_foldr_with_index_aux_spec List.foldrIdx_eq_foldrIdxSpecₓ

theorem foldrIdx_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrIdx f b as = foldr (uncurry f) b (enum as) := by
  simp only [foldrIdx, foldrIdxSpec, foldrIdx_eq_foldrIdxSpec, enum]
#align list.foldr_with_index_eq_foldr_enum List.foldrIdx_eq_foldr_enum

end FoldrWithIndex

theorem indexesValues_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filter (p ∘ Prod.snd) (enum as) := by
  simp [indexesValues, foldrIdx_eq_foldr_enum, uncurry, filter_eq_foldr]
#align list.indexes_values_eq_filter_enum List.indexesValues_eq_filter_enum

theorem findIdxs_eq_map_indexesValues (p : α → Prop) [DecidablePred p] (as : List α) :
    findIdxs p as = map Prod.fst (indexesValues p as) := by
  simp only [indexesValues_eq_filter_enum, map_filter_eq_foldr, findIdxs,
    foldrIdx_eq_foldr_enum, uncurry]
#align list.find_indexes_eq_map_indexes_values List.findIdxs_eq_map_indexesValues

section FoldlWithIndex

-- Porting note: Changed argument order of `foldlIdxSpec` to align better with `foldlIdx`.
/-- Specification of `foldl_with_index_aux`. -/
def foldlIdxSpec (f : ℕ → α → β → α) (a : α) (bs : List β) (start : ℕ) : α :=
  foldl (fun a (p : ℕ × β) => f p.fst a p.snd) a <| enumFrom start bs
#align list.foldl_with_index_aux_spec List.foldlIdxSpecₓ

#noalign list.foldl_with_index_aux_spec_cons

theorem foldlIdx_eq_foldlIdxSpec (f : ℕ → α → β → α) (a bs start) :
    foldlIdx f a bs start = foldlIdxSpec f a bs start := by
  induction bs generalizing start a
  · rfl
  · simp [foldlIdxSpec, *]
#align list.foldl_with_index_aux_eq_foldl_with_index_aux_spec List.foldlIdx_eq_foldlIdxSpecₓ

theorem foldlIdx_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlIdx f a bs = foldl (fun a (p : ℕ × β) => f p.fst a p.snd) a (enum bs) := by
  simp only [foldlIdx, foldlIdxSpec, foldlIdx_eq_foldlIdxSpec, enum]
#align list.foldl_with_index_eq_foldl_enum List.foldlIdx_eq_foldl_enum

end FoldlWithIndex

section MfoldWithIndex

variable {m : Type u → Type v} [Monad m]

theorem foldrIdxM_eq_foldrM_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) :
    foldrIdxM f b as = foldrM (uncurry f) b (enum as) := by
  simp only [foldrIdxM, foldrM_eq_foldr, foldrIdx_eq_foldr_enum, uncurry]
#align list.mfoldr_with_index_eq_mfoldr_enum List.foldrIdxM_eq_foldrM_enum

theorem foldlIdxM_eq_foldlM_enum [LawfulMonad m] {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    foldlIdxM f b as = foldlM (fun b (p : ℕ × α) => f p.fst b p.snd) b (enum as) := by
  rw [foldlIdxM, foldlM_eq_foldl, foldlIdx_eq_foldl_enum]
#align list.mfoldl_with_index_eq_mfoldl_enum List.foldlIdxM_eq_foldlM_enum

end MfoldWithIndex

section MmapWithIndex

variable {m : Type u → Type v} [Applicative m]

/-- Specification of `mmap_with_index_aux`. -/
def mmapWithIndexAuxSpec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverse (uncurry f) <| enumFrom start as
#align list.mmap_with_index_aux_spec List.mmapWithIndexAuxSpec

-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.
theorem mmapWithIndexAuxSpec_cons {α β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mmapWithIndexAuxSpec f start (a :: as) =
      List.cons <$> f start a <*> mmapWithIndexAuxSpec f (start + 1) as :=
  rfl
#align list.mmap_with_index_aux_spec_cons List.mmapWithIndexAuxSpec_cons

theorem mmapWithIndexAux_eq_mmapWithIndexAuxSpec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) :
    mmapWithIndexAux f start as = mmapWithIndexAuxSpec f start as := by
  induction as generalizing start
  · rfl
  · simp [mmap_with_index_aux, mmap_with_index_aux_spec_cons, *]
#align list.mmap_with_index_aux_eq_mmap_with_index_aux_spec List.mmapWithIndexAux_eq_mmapWithIndexAuxSpec

theorem mapIdxM_eq_mmap_enum {α β} (f : ℕ → α → m β) (as : List α) :
    mapIdxM f as = List.traverse (uncurry f) (enum as) := by
  simp only [mmap_with_index, mmap_with_index_aux_spec,
    mmap_with_index_aux_eq_mmap_with_index_aux_spec, enum]
#align list.mmap_with_index_eq_mmap_enum List.mapIdxM_eq_mmap_enum

end MmapWithIndex

section MmapWithIndex'

variable {m : Type u → Type v} [Applicative m] [LawfulApplicative m]

theorem mapIdxMAux'_eq_mmapWithIndexAux {α} (f : ℕ → α → m PUnit) (start : ℕ) (as : List α) :
    mapIdxMAux' f start as = mmapWithIndexAux f start as *> pure PUnit.unit := by
  induction as generalizing start <;>
    simp [mmap_with_index'_aux, mmap_with_index_aux, *, seq_right_eq, const, -comp_const,
      functor_norm]
#align list.mmap_with_index'_aux_eq_mmap_with_index_aux List.mapIdxMAux'_eq_mmapWithIndexAux

theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM f as *> pure PUnit.unit := by
  apply mmap_with_index'_aux_eq_mmap_with_index_aux
#align list.mmap_with_index'_eq_mmap_with_index List.mapIdxM'_eq_mapIdxM

end MmapWithIndex'

end List
