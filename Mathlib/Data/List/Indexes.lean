/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathlib.Data.List.Induction

/-!
# Lemmas about List.*Idx functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx` and `List.foldrIdx`.

As of 2025-01-29, these are not used anywhere in Mathlib. Moreover, with
`List.enum` and `List.enumFrom` being replaced by `List.zipIdx`
in Lean's `nightly-2025-01-29` release, they now use deprecated functions and theorems.
Rather than updating this unused material, we are deprecating it.
Anyone wanting to restore this material is welcome to do so, but will need to update uses of
`List.enum` and `List.enumFrom` to use `List.zipIdx` instead.
However, note that this material will later be implemented in the Lean standard library.
-/

assert_not_exists MonoidWithZero

universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapIdx

@[deprecated reverseRecOn (since := "2025-01-28")]
theorem list_reverse_induction (p : List α → Prop) (base : p [])
    (ind : ∀ (l : List α) (e : α), p l → p (l ++ [e])) : (∀ (l : List α), p l) :=
  fun l => l.reverseRecOn base ind

theorem mapIdx_append_one : ∀ {f : ℕ → α → β} {l : List α} {e : α},
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] :=
  mapIdx_concat

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29"), local simp]
theorem map_enumFrom_eq_zipWith : ∀ (l : List α) (n : ℕ) (f : ℕ → α → β),
    map (uncurry f) (enumFrom n l) = zipWith (fun i ↦ f (i + n)) (range (length l)) l := by
  intro l
  generalize e : l.length = len
  revert l
  induction' len with len ih <;> intros l e n f
  · have : l = [] := by
      cases l
      · rfl
      · contradiction
    rw [this]; rfl
  · rcases l with - | ⟨head, tail⟩
    · contradiction
    · simp only [enumFrom_cons, map_cons, range_succ_eq_map, zipWith_cons_cons,
        Nat.zero_add, zipWith_map_left, true_and]
      rw [ih]
      · suffices (fun i ↦ f (i + (n + 1))) = ((fun i ↦ f (i + n)) ∘ Nat.succ) by
          rw [this]
          rfl
        funext n' a
        simp only [comp, Nat.add_assoc, Nat.add_comm, Nat.add_succ]
      simp only [length_cons, Nat.succ.injEq] at e; exact e

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem get_mapIdx (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapIdx f).length := h.trans_le length_mapIdx.ge) :
    (l.mapIdx f).get ⟨i, h'⟩ = f i (l.get ⟨i, h⟩) := by
  simp [mapIdx_eq_zipIdx_map, enum_eq_zip_range]

theorem mapIdx_eq_ofFn (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length ↦ f (i : ℕ) (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

end MapIdx

section FoldrIdx

-- Porting note: Changed argument order of `foldrIdxSpec` to align better with `foldrIdx`.
set_option linter.deprecated false in
/-- Specification of `foldrIdx`. -/
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
def foldrIdxSpec (f : ℕ → α → β → β) (b : β) (as : List α) (start : ℕ) : β :=
  foldr (uncurry f) b <| enumFrom start as

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldrIdxSpec_cons (f : ℕ → α → β → β) (b a as start) :
    foldrIdxSpec f b (a :: as) start = f start a (foldrIdxSpec f b as (start + 1)) :=
  rfl

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldrIdx_eq_foldrIdxSpec (f : ℕ → α → β → β) (b as start) :
    foldrIdx f b as start = foldrIdxSpec f b as start := by
  induction as generalizing start
  · rfl
  · simp only [foldrIdx, foldrIdxSpec_cons, *]

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldrIdx_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrIdx f b as = foldr (uncurry f) b (enum as) := by
  simp only [foldrIdx, foldrIdxSpec, foldrIdx_eq_foldrIdxSpec, enum]

end FoldrIdx

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem indexesValues_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filter (p ∘ Prod.snd) (enum as) := by
  simp +unfoldPartialApp [indexesValues, foldrIdx_eq_foldr_enum, uncurry,
    filter_eq_foldr, cond_eq_if]

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem findIdxs_eq_map_indexesValues (p : α → Prop) [DecidablePred p] (as : List α) :
    findIdxs p as = map Prod.fst (indexesValues p as) := by
  simp +unfoldPartialApp only [indexesValues_eq_filter_enum,
    map_filter_eq_foldr, findIdxs, uncurry, foldrIdx_eq_foldr_enum, decide_eq_true_eq, comp_apply,
    Bool.cond_decide]

section FoldlIdx

-- Porting note: Changed argument order of `foldlIdxSpec` to align better with `foldlIdx`.
set_option linter.deprecated false in
/-- Specification of `foldlIdx`. -/
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
def foldlIdxSpec (f : ℕ → α → β → α) (a : α) (bs : List β) (start : ℕ) : α :=
  foldl (fun a p ↦ f p.fst a p.snd) a <| enumFrom start bs

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldlIdxSpec_cons (f : ℕ → α → β → α) (a b bs start) :
    foldlIdxSpec f a (b :: bs) start = foldlIdxSpec f (f start a b) bs (start + 1) :=
  rfl

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldlIdx_eq_foldlIdxSpec (f : ℕ → α → β → α) (a bs start) :
    foldlIdx f a bs start = foldlIdxSpec f a bs start := by
  induction bs generalizing start a
  · rfl
  · simp [foldlIdxSpec, *]

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldlIdx_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlIdx f a bs = foldl (fun a p ↦ f p.fst a p.snd) a (enum bs) := by
  simp only [foldlIdx, foldlIdxSpec, foldlIdx_eq_foldlIdxSpec, enum]

end FoldlIdx

section FoldIdxM

-- Porting note: `foldrM_eq_foldr` now depends on `[LawfulMonad m]`
variable {m : Type u → Type v} [Monad m]

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldrIdxM_eq_foldrM_enum {β} (f : ℕ → α → β → m β) (b : β) (as : List α) [LawfulMonad m] :
    foldrIdxM f b as = foldrM (uncurry f) b (enum as) := by
  simp +unfoldPartialApp only [foldrIdxM, foldrM_eq_foldr,
    foldrIdx_eq_foldr_enum, uncurry]

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem foldlIdxM_eq_foldlM_enum [LawfulMonad m] {β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    foldlIdxM f b as = List.foldlM (fun b p ↦ f p.fst b p.snd) b (enum as) := by
  rw [foldlIdxM, foldlM_eq_foldl, foldlIdx_eq_foldl_enum]

end FoldIdxM

section MapIdxM

-- Porting note: `[Applicative m]` replaced by `[Monad m] [LawfulMonad m]`
variable {m : Type u → Type v} [Monad m]

set_option linter.deprecated false in
/-- Specification of `mapIdxMAux`. -/
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
def mapIdxMAuxSpec {β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverse (uncurry f) <| enumFrom start as

-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.
set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem mapIdxMAuxSpec_cons {β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mapIdxMAuxSpec f start (a :: as) = cons <$> f start a <*> mapIdxMAuxSpec f (start + 1) as :=
  rfl

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem mapIdxMGo_eq_mapIdxMAuxSpec
    [LawfulMonad m] {β} (f : ℕ → α → m β) (arr : Array β) (as : List α) :
    mapIdxM.go f as arr = (arr.toList ++ ·) <$> mapIdxMAuxSpec f arr.size as := by
  generalize e : as.length = len
  revert as arr
  induction' len with len ih <;> intro arr as h
  · have : as = [] := by
      cases as
      · rfl
      · contradiction
    simp only [this, mapIdxM.go, mapIdxMAuxSpec, enumFrom_nil, List.traverse, map_pure, append_nil]
  · match as with
    | nil => contradiction
    | cons head tail =>
      simp only [length_cons, Nat.succ.injEq] at h
      simp only [mapIdxM.go, mapIdxMAuxSpec_cons, map_eq_pure_bind, seq_eq_bind_map,
        LawfulMonad.bind_assoc, pure_bind]
      congr
      conv => { lhs; intro x; rw [ih _ _ h]; }
      funext x
      simp only [Array.toList_push, append_assoc, singleton_append, Array.size_push,
        map_eq_pure_bind]

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-01-29")]
theorem mapIdxM_eq_mmap_enum [LawfulMonad m] {β} (f : ℕ → α → m β) (as : List α) :
    as.mapIdxM f = List.traverse (uncurry f) (enum as) := by
  simp only [mapIdxM, mapIdxMGo_eq_mapIdxMAuxSpec, Array.toList_toArray,
    nil_append, mapIdxMAuxSpec, Array.size_toArray, length_nil, id_map', enum]

end MapIdxM

section MapIdxM'

-- Porting note: `[Applicative m] [LawfulApplicative m]` replaced by [Monad m] [LawfulMonad m]
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

theorem mapIdxMAux'_eq_mapIdxMGo {α} (f : ℕ → α → m PUnit) (as : List α) (arr : Array PUnit) :
    mapIdxMAux' f arr.size as = mapIdxM.go f as arr *> pure PUnit.unit := by
  revert arr
  induction' as with head tail ih <;> intro arr
  · simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
  · simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go, seq_pure]
    generalize (f (Array.size arr) head) = head
    have : (arr.push ⟨⟩).size = arr.size + 1 := Array.size_push _
    rw [← this, ih]
    simp only [seqRight_eq, map_eq_pure_bind, seq_pure, LawfulMonad.bind_assoc, pure_bind]

theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM f as *> pure PUnit.unit :=
  mapIdxMAux'_eq_mapIdxMGo f as #[]

end MapIdxM'

end List
