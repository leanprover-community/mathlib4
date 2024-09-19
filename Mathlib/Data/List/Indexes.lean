/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Zip

/-!
# Lemmas about List.*Idx functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx` and `List.foldrIdx`.
-/

assert_not_exists MonoidWithZero

universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapIdx

@[simp]
theorem mapIdx_nil {α β} (f : ℕ → α → β) : mapIdx f [] = [] :=
  rfl


theorem list_reverse_induction (p : List α → Prop) (base : p [])
    (ind : ∀ (l : List α) (e : α), p l → p (l ++ [e])) : (∀ (l : List α), p l) := by
  let q := fun l ↦ p (reverse l)
  have pq : ∀ l, p (reverse l) → q l := by simp only [q, reverse_reverse]; intro; exact id
  have qp : ∀ l, q (reverse l) → p l := by simp only [q, reverse_reverse]; intro; exact id
  intro l
  apply qp
  generalize (reverse l) = l
  induction' l with head tail ih
  · apply pq; simp only [reverse_nil, base]
  · apply pq; simp only [reverse_cons]; apply ind; apply qp; rw [reverse_reverse]; exact ih

theorem mapIdxGo_append : ∀ (f : ℕ → α → β) (l₁ l₂ : List α) (arr : Array β),
    mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (List.toArray (mapIdx.go f l₁ arr)) := by
  intros f l₁ l₂ arr
  generalize e : (l₁ ++ l₂).length = len
  revert l₁ l₂ arr
  induction' len with len ih <;> intros l₁ l₂ arr h
  · have l₁_nil : l₁ = [] := by
      cases l₁
      · rfl
      · contradiction
    have l₂_nil : l₂ = [] := by
      cases l₂
      · rfl
      · rw [List.length_append] at h; contradiction
    rw [l₁_nil, l₂_nil]; simp only [mapIdx.go, Array.toList_eq, Array.toArray_data]
  · cases' l₁ with head tail <;> simp only [mapIdx.go]
    · simp only [nil_append, Array.toList_eq, Array.toArray_data]
    · simp only [List.append_eq]
      rw [ih]
      · simp only [cons_append, length_cons, length_append, Nat.succ.injEq] at h
        simp only [length_append, h]

theorem mapIdxGo_length : ∀ (f : ℕ → α → β) (l : List α) (arr : Array β),
    length (mapIdx.go f l arr) = length l + arr.size := by
  intro f l
  induction' l with head tail ih
  · intro; simp only [mapIdx.go, Array.toList_eq, length_nil, Nat.zero_add]
  · intro; simp only [mapIdx.go]; rw [ih]; simp only [Array.size_push, length_cons]
    simp only [Nat.add_succ, Fin.add_zero, Nat.add_comm]

theorem mapIdx_append_one : ∀ (f : ℕ → α → β) (l : List α) (e : α),
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] := by
  intros f l e
  unfold mapIdx
  rw [mapIdxGo_append f l [e]]
  simp only [mapIdx.go, Array.size_toArray, mapIdxGo_length, length_nil, Nat.add_zero,
    Array.toList_eq, Array.push_data, Array.data_toArray]

@[local simp]
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
  · cases' l with head tail
    · contradiction
    · simp only [map, uncurry_apply_pair, range_succ_eq_map, zipWith, Nat.zero_add,
        zipWith_map_left]
      rw [ih]
      · suffices (fun i ↦ f (i + (n + 1))) = ((fun i ↦ f (i + n)) ∘ Nat.succ) by
          rw [this]
          rfl
        funext n' a
        simp only [comp, Nat.add_assoc, Nat.add_comm, Nat.add_succ]
      simp only [length_cons, Nat.succ.injEq] at e; exact e

theorem length_mapIdx_go (f : ℕ → α → β) : ∀ (l : List α) (arr : Array β),
    (mapIdx.go f l arr).length = l.length + arr.size
  | [], _ => by simp [mapIdx.go]
  | a :: l, _ => by
    simp only [mapIdx.go, length_cons]
    rw [length_mapIdx_go]
    simp
    omega

@[simp] theorem length_mapIdx (l : List α) (f : ℕ → α → β) : (l.mapIdx f).length = l.length := by
  simp [mapIdx, length_mapIdx_go]

theorem getElem?_mapIdx_go (f : ℕ → α → β) : ∀ (l : List α) (arr : Array β) (i : ℕ),
    (mapIdx.go f l arr)[i]? =
      if h : i < arr.size then some arr[i] else Option.map (f i) l[i - arr.size]?
  | [], arr, i => by
    simp [mapIdx.go, getElem?_eq, Array.getElem_eq_data_getElem]
  | a :: l, arr, i => by
    rw [mapIdx.go, getElem?_mapIdx_go]
    simp only [Array.size_push]
    split <;> split
    · simp only [Option.some.injEq]
      rw [Array.getElem_eq_data_getElem]
      simp only [Array.push_data]
      rw [getElem_append_left, Array.getElem_eq_data_getElem]
    · have : i = arr.size := by omega
      simp_all
    · omega
    · have : i - arr.size = i - (arr.size + 1) + 1 := by omega
      simp_all

@[simp] theorem getElem?_mapIdx (l : List α) (f : ℕ → α → β) (i : ℕ) :
    (l.mapIdx f)[i]? = Option.map (f i) l[i]? := by
  simp [mapIdx, getElem?_mapIdx_go]

theorem mapIdx_eq_enum_map (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = l.enum.map (Function.uncurry f) := by
  ext1 i
  simp only [getElem?_mapIdx, Option.map, getElem?_map, getElem?_enum]
  split <;> simp

@[simp]
theorem mapIdx_cons (l : List α) (f : ℕ → α → β) (a : α) :
    mapIdx f (a :: l) = f 0 a :: mapIdx (fun i ↦ f (i + 1)) l := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zipWith,
    range_succ_eq_map, zipWith_map_left]

theorem mapIdx_append (K L : List α) (f : ℕ → α → β) :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i a ↦ f (i + K.length) a := by
  induction' K with a J IH generalizing f
  · rfl
  · simp [IH fun i ↦ f (i + 1), Nat.add_assoc]

@[simp]
theorem mapIdx_eq_nil {f : ℕ → α → β} {l : List α} : List.mapIdx f l = [] ↔ l = [] := by
  rw [List.mapIdx_eq_enum_map, List.map_eq_nil, List.enum_eq_nil]

theorem get_mapIdx (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapIdx f).length := h.trans_le (l.length_mapIdx f).ge) :
    (l.mapIdx f).get ⟨i, h'⟩ = f i (l.get ⟨i, h⟩) := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range]

@[deprecated (since := "2024-08-19")] alias nthLe_mapIdx := get_mapIdx

theorem mapIdx_eq_ofFn (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length ↦ f (i : ℕ) (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

section deprecated

/-- Lean3 `map_with_index` helper function -/
@[deprecated (since := "2024-08-15")]
protected def oldMapIdxCore (f : ℕ → α → β) : ℕ → List α → List β
  | _, []      => []
  | k, a :: as => f k a :: List.oldMapIdxCore f (k + 1) as

set_option linter.deprecated false in
/-- Given a function `f : ℕ → α → β` and `as : List α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
@[deprecated (since := "2024-08-15")]
protected def oldMapIdx (f : ℕ → α → β) (as : List α) : List β :=
  List.oldMapIdxCore f 0 as

set_option linter.deprecated false in
@[deprecated (since := "2024-08-15")]
protected theorem oldMapIdxCore_eq (l : List α) (f : ℕ → α → β) (n : ℕ) :
    l.oldMapIdxCore f n = l.oldMapIdx fun i a ↦ f (i + n) a := by
  induction' l with hd tl hl generalizing f n
  · rfl
  · rw [List.oldMapIdx]
    simp only [List.oldMapIdxCore, hl, Nat.add_left_comm, Nat.add_comm, Nat.add_zero]

set_option linter.deprecated false in
@[deprecated (since := "2024-08-15")]
protected theorem oldMapIdxCore_append : ∀ (f : ℕ → α → β) (n : ℕ) (l₁ l₂ : List α),
    List.oldMapIdxCore f n (l₁ ++ l₂) =
    List.oldMapIdxCore f n l₁ ++ List.oldMapIdxCore f (n + l₁.length) l₂ := by
  intros f n l₁ l₂
  generalize e : (l₁ ++ l₂).length = len
  revert n l₁ l₂
  induction' len with len ih <;> intros n l₁ l₂ h
  · have l₁_nil : l₁ = [] := by
      cases l₁
      · rfl
      · contradiction
    have l₂_nil : l₂ = [] := by
      cases l₂
      · rfl
      · rw [List.length_append] at h; contradiction
    simp only [l₁_nil, l₂_nil]; rfl
  · cases' l₁ with head tail
    · rfl
    · simp only [List.oldMapIdxCore, List.append_eq, length_cons, cons_append,cons.injEq, true_and]
      suffices n + Nat.succ (length tail) = n + 1 + tail.length by
        rw [this]
        apply ih (n + 1) _ _ _
        simp only [cons_append, length_cons, length_append, Nat.succ.injEq] at h
        simp only [length_append, h]
      rw [Nat.add_assoc]; simp only [Nat.add_comm]

set_option linter.deprecated false in
@[deprecated (since := "2024-08-15")]
protected theorem oldMapIdx_append : ∀ (f : ℕ → α → β) (l : List α) (e : α),
    List.oldMapIdx f (l ++ [e]) = List.oldMapIdx f l ++ [f l.length e] := by
  intros f l e
  unfold List.oldMapIdx
  rw [List.oldMapIdxCore_append f 0 l [e]]
  simp only [Nat.zero_add]; rfl

set_option linter.deprecated false in
@[deprecated (since := "2024-08-15")]
protected theorem new_def_eq_old_def :
    ∀ (f : ℕ → α → β) (l : List α), l.mapIdx f = List.oldMapIdx f l := by
  intro f
  apply list_reverse_induction
  · rfl
  · intro l e h
    rw [List.oldMapIdx_append, mapIdx_append_one, h]

end deprecated

end MapIdx

section FoldrIdx

-- Porting note: Changed argument order of `foldrIdxSpec` to align better with `foldrIdx`.
/-- Specification of `foldrIdx`. -/
def foldrIdxSpec (f : ℕ → α → β → β) (b : β) (as : List α) (start : ℕ) : β :=
  foldr (uncurry f) b <| enumFrom start as

theorem foldrIdxSpec_cons (f : ℕ → α → β → β) (b a as start) :
    foldrIdxSpec f b (a :: as) start = f start a (foldrIdxSpec f b as (start + 1)) :=
  rfl

theorem foldrIdx_eq_foldrIdxSpec (f : ℕ → α → β → β) (b as start) :
    foldrIdx f b as start = foldrIdxSpec f b as start := by
  induction as generalizing start
  · rfl
  · simp only [foldrIdx, foldrIdxSpec_cons, *]

theorem foldrIdx_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrIdx f b as = foldr (uncurry f) b (enum as) := by
  simp only [foldrIdx, foldrIdxSpec, foldrIdx_eq_foldrIdxSpec, enum]

end FoldrIdx

theorem indexesValues_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filter (p ∘ Prod.snd) (enum as) := by
  simp (config := { unfoldPartialApp := true }) [indexesValues, foldrIdx_eq_foldr_enum, uncurry,
    filter_eq_foldr, cond_eq_if]

theorem findIdxs_eq_map_indexesValues (p : α → Prop) [DecidablePred p] (as : List α) :
    findIdxs p as = map Prod.fst (indexesValues p as) := by
  simp (config := { unfoldPartialApp := true }) only [indexesValues_eq_filter_enum,
    map_filter_eq_foldr, findIdxs, uncurry, foldrIdx_eq_foldr_enum, decide_eq_true_eq, comp_apply,
    Bool.cond_decide]

section FoldlIdx

-- Porting note: Changed argument order of `foldlIdxSpec` to align better with `foldlIdx`.
/-- Specification of `foldlIdx`. -/
def foldlIdxSpec (f : ℕ → α → β → α) (a : α) (bs : List β) (start : ℕ) : α :=
  foldl (fun a p ↦ f p.fst a p.snd) a <| enumFrom start bs

theorem foldlIdxSpec_cons (f : ℕ → α → β → α) (a b bs start) :
    foldlIdxSpec f a (b :: bs) start = foldlIdxSpec f (f start a b) bs (start + 1) :=
  rfl

theorem foldlIdx_eq_foldlIdxSpec (f : ℕ → α → β → α) (a bs start) :
    foldlIdx f a bs start = foldlIdxSpec f a bs start := by
  induction bs generalizing start a
  · rfl
  · simp [foldlIdxSpec, *]

theorem foldlIdx_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlIdx f a bs = foldl (fun a p ↦ f p.fst a p.snd) a (enum bs) := by
  simp only [foldlIdx, foldlIdxSpec, foldlIdx_eq_foldlIdxSpec, enum]

end FoldlIdx

section FoldIdxM

-- Porting note: `foldrM_eq_foldr` now depends on `[LawfulMonad m]`
variable {m : Type u → Type v} [Monad m]

theorem foldrIdxM_eq_foldrM_enum {β} (f : ℕ → α → β → m β) (b : β) (as : List α) [LawfulMonad m] :
    foldrIdxM f b as = foldrM (uncurry f) b (enum as) := by
  simp (config := { unfoldPartialApp := true }) only [foldrIdxM, foldrM_eq_foldr,
    foldrIdx_eq_foldr_enum, uncurry]

theorem foldlIdxM_eq_foldlM_enum [LawfulMonad m] {β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    foldlIdxM f b as = List.foldlM (fun b p ↦ f p.fst b p.snd) b (enum as) := by
  rw [foldlIdxM, foldlM_eq_foldl, foldlIdx_eq_foldl_enum]

end FoldIdxM

section MapIdxM

-- Porting note: `[Applicative m]` replaced by `[Monad m] [LawfulMonad m]`
variable {m : Type u → Type v} [Monad m]

/-- Specification of `mapIdxMAux`. -/
def mapIdxMAuxSpec {β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverse (uncurry f) <| enumFrom start as

-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.
theorem mapIdxMAuxSpec_cons {β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mapIdxMAuxSpec f start (a :: as) = cons <$> f start a <*> mapIdxMAuxSpec f (start + 1) as :=
  rfl

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
    simp only [this, mapIdxM.go, mapIdxMAuxSpec, List.traverse, map_pure, append_nil]
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

theorem mapIdxM_eq_mmap_enum [LawfulMonad m] {β} (f : ℕ → α → m β) (as : List α) :
    as.mapIdxM f = List.traverse (uncurry f) (enum as) := by
  simp only [mapIdxM, mapIdxMGo_eq_mapIdxMAuxSpec, Array.toList_eq, Array.data_toArray,
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
    let arr_1 := arr.push ⟨⟩
    have : arr_1.size = arr.size + 1 := Array.size_push arr ⟨⟩
    rw [← this, ih arr_1]
    simp only [seqRight_eq, map_eq_pure_bind, seq_pure, LawfulMonad.bind_assoc, pure_bind]

theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM as f *> pure PUnit.unit :=
  mapIdxMAux'_eq_mapIdxMGo f as #[]

end MapIdxM'

end List
