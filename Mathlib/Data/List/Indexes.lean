/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg

! This file was ported from Lean 3 source module data.list.indexes
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.OfFn
import Mathbin.Data.List.Range

/-!
# Lemmas about list.*_with_index functions.

Some specification lemmas for `list.map_with_index`, `list.mmap_with_index`, `list.foldl_with_index`
and `list.foldr_with_index`.
-/


universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapWithIndex

@[simp]
theorem mapIdx_nil {α β} (f : ℕ → α → β) : mapIdx f [] = [] :=
  rfl
#align list.map_with_index_nil List.mapIdx_nil

theorem mapIdx_core_eq (l : List α) (f : ℕ → α → β) (n : ℕ) :
    l.MapWithIndexCore f n = l.mapWithIndex fun i a => f (i + n) a :=
  by
  induction' l with hd tl hl generalizing f n
  · simpa
  · rw [map_with_index]
    simp [map_with_index_core, hl, add_left_comm, add_assoc, add_comm]
#align list.map_with_index_core_eq List.mapIdx_core_eq

theorem mapIdx_eq_enum_map (l : List α) (f : ℕ → α → β) :
    l.mapWithIndex f = l.enum.map (Function.uncurry f) :=
  by
  induction' l with hd tl hl generalizing f
  · simp [List.enum_eq_zip_range]
  · rw [map_with_index, map_with_index_core, map_with_index_core_eq, hl]
    simp [enum_eq_zip_range, range_succ_eq_map, zip_with_map_left, map_uncurry_zip_eq_zip_with]
#align list.map_with_index_eq_enum_map List.mapIdx_eq_enum_map

@[simp]
theorem mapIdx_cons {α β} (l : List α) (f : ℕ → α → β) (a : α) :
    mapIdx f (a :: l) = f 0 a :: mapIdx (fun i => f (i + 1)) l := by
  simp [map_with_index_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zip_with,
    range_succ_eq_map, zip_with_map_left]
#align list.map_with_index_cons List.mapIdx_cons

theorem mapIdx_append {α} (K L : List α) (f : ℕ → α → β) :
    (K ++ L).mapWithIndex f = K.mapWithIndex f ++ L.mapWithIndex fun i a => f (i + K.length) a :=
  by
  induction' K with a J IH generalizing f
  · simp
  · simp [IH fun i => f (i + 1), add_assoc]
#align list.map_with_index_append List.mapIdx_append

@[simp]
theorem length_mapIdx {α β} (l : List α) (f : ℕ → α → β) : (l.mapWithIndex f).length = l.length :=
  by
  induction' l with hd tl IH generalizing f
  · simp
  · simp [IH]
#align list.length_map_with_index List.length_mapIdx

@[simp]
theorem nthLe_mapIdx {α β} (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapWithIndex f).length := h.trans_le (l.length_map_with_index f).ge) :
    (l.mapWithIndex f).nthLe i h' = f i (l.nthLe i h) := by
  simp [map_with_index_eq_enum_map, enum_eq_zip_range]
#align list.nth_le_map_with_index List.nthLe_mapIdx

theorem mapIdx_eq_ofFn {α β} (l : List α) (f : ℕ → α → β) :
    l.mapWithIndex f = ofFn fun i : Fin l.length => f (i : ℕ) (l.nthLe i i.is_lt) :=
  by
  induction' l with hd tl IH generalizing f
  · simp
  · simpa [IH]
#align list.map_with_index_eq_of_fn List.mapIdx_eq_ofFn

end MapWithIndex

section FoldrWithIndex

/-- Specification of `foldr_with_index_aux`. -/
def foldrWithIndexAuxSpec (f : ℕ → α → β → β) (start : ℕ) (b : β) (as : List α) : β :=
  foldr (uncurry f) b <| enumFrom start as
#align list.foldr_with_index_aux_spec List.foldrWithIndexAuxSpec

theorem foldrWithIndexAuxSpec_cons (f : ℕ → α → β → β) (start b a as) :
    foldrWithIndexAuxSpec f start b (a :: as) =
      f start a (foldrWithIndexAuxSpec f (start + 1) b as) :=
  rfl
#align list.foldr_with_index_aux_spec_cons List.foldrWithIndexAuxSpec_cons

theorem foldrWithIndexAux_eq_foldrWithIndexAuxSpec (f : ℕ → α → β → β) (start b as) :
    foldrWithIndexAux f start b as = foldrWithIndexAuxSpec f start b as :=
  by
  induction as generalizing start
  · rfl
  · simp only [foldr_with_index_aux, foldr_with_index_aux_spec_cons, *]
#align list.foldr_with_index_aux_eq_foldr_with_index_aux_spec List.foldrWithIndexAux_eq_foldrWithIndexAuxSpec

theorem foldrIdx_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrIdx f b as = foldr (uncurry f) b (enum as) := by
  simp only [foldr_with_index, foldr_with_index_aux_spec,
    foldr_with_index_aux_eq_foldr_with_index_aux_spec, enum]
#align list.foldr_with_index_eq_foldr_enum List.foldrIdx_eq_foldr_enum

end FoldrWithIndex

theorem indexesValues_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filter (p ∘ Prod.snd) (enum as) := by
  simp [indexes_values, foldr_with_index_eq_foldr_enum, uncurry, filter_eq_foldr]
#align list.indexes_values_eq_filter_enum List.indexesValues_eq_filterₓ_enum

theorem findIdxs_eq_map_indexesValues (p : α → Prop) [DecidablePred p] (as : List α) :
    findIdxs p as = map Prod.fst (indexesValues p as) := by
  simp only [indexes_values_eq_filter_enum, map_filter_eq_foldr, find_indexes,
    foldr_with_index_eq_foldr_enum, uncurry]
#align list.find_indexes_eq_map_indexes_values List.findIdxs_eq_map_indexesValues

section FoldlWithIndex

/-- Specification of `foldl_with_index_aux`. -/
def foldlWithIndexAuxSpec (f : ℕ → α → β → α) (start : ℕ) (a : α) (bs : List β) : α :=
  foldl (fun a (p : ℕ × β) => f p.fst a p.snd) a <| enumFrom start bs
#align list.foldl_with_index_aux_spec List.foldlWithIndexAuxSpec

theorem foldlWithIndexAuxSpec_cons (f : ℕ → α → β → α) (start a b bs) :
    foldlWithIndexAuxSpec f start a (b :: bs) =
      foldlWithIndexAuxSpec f (start + 1) (f start a b) bs :=
  rfl
#align list.foldl_with_index_aux_spec_cons List.foldlWithIndexAuxSpec_cons

theorem foldlWithIndexAux_eq_foldlWithIndexAuxSpec (f : ℕ → α → β → α) (start a bs) :
    foldlWithIndexAux f start a bs = foldlWithIndexAuxSpec f start a bs :=
  by
  induction bs generalizing start a
  · rfl
  · simp [foldl_with_index_aux, foldl_with_index_aux_spec_cons, *]
#align list.foldl_with_index_aux_eq_foldl_with_index_aux_spec List.foldlWithIndexAux_eq_foldlWithIndexAuxSpec

theorem foldlIdx_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlIdx f a bs = foldl (fun a (p : ℕ × β) => f p.fst a p.snd) a (enum bs) := by
  simp only [foldl_with_index, foldl_with_index_aux_spec,
    foldl_with_index_aux_eq_foldl_with_index_aux_spec, enum]
#align list.foldl_with_index_eq_foldl_enum List.foldlIdx_eq_foldl_enum

end FoldlWithIndex

section MfoldWithIndex

variable {m : Type u → Type v} [Monad m]

theorem foldrIdxM_eq_foldrM_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) :
    foldrIdxM f b as = foldrM (uncurry f) b (enum as) := by
  simp only [mfoldr_with_index, mfoldr_eq_foldr, foldr_with_index_eq_foldr_enum, uncurry]
#align list.mfoldr_with_index_eq_mfoldr_enum List.foldrIdxM_eq_foldrM_enum

theorem foldlIdxM_eq_foldlM_enum [LawfulMonad m] {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    foldlIdxM f b as = foldlM (fun b (p : ℕ × α) => f p.fst b p.snd) b (enum as) := by
  rw [mfoldl_with_index, mfoldl_eq_foldl, foldl_with_index_eq_foldl_enum]
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
    mmapWithIndexAux f start as = mmapWithIndexAuxSpec f start as :=
  by
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

