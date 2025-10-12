/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.List.Nodup
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.TakeWhile

/-!
# Sorting algorithms on lists

In this file we define the sorting algorithm `List.insertionSort r` and prove
that we have `(l.insertionSort r l).Pairwise r` under suitable conditions on `r`.

We then define `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT` to be
aliases for `List.Pairwise` when the relation derives from a preorder.
-/

open List.Perm

universe u v

namespace List

/-!
### The predicate `List.Sorted` (now deprecated).
-/

section Sorted

variable {α : Type u} {r : α → α → Prop} {a : α} {l : List α}

/-- `Sorted r l` is the same as `List.Pairwise r l` and has been deprecated -/
@[deprecated (since := "2025-10-11")]
alias Sorted := Pairwise

@[deprecated (since := "2025-10-11")]
alias decidableSorted := List.instDecidablePairwise

@[deprecated Pairwise.nil (since := "2025-10-11")]
theorem sorted_nil : Pairwise r [] := Pairwise.nil

@[deprecated (since := "2025-10-11")]
alias Sorted.of_cons := Pairwise.of_cons

@[deprecated (since := "2025-10-11")]
alias Sorted.tail := Pairwise.tail

@[deprecated (since := "2025-10-11")]
alias rel_of_sorted_cons := rel_of_pairwise_cons

@[deprecated (since := "2025-10-11")]
alias Sorted.cons := Pairwise.cons_cons_of_trans

@[deprecated (since := "2025-10-11")]
alias sorted_cons_cons := pairwise_cons_cons_iff_of_trans

@[deprecated (since := "2025-10-11")]
alias sorted_cons := pairwise_cons

@[deprecated (since := "2025-10-11")]
alias Sorted.nodup := Pairwise.nodup

@[deprecated (since := "2025-10-11")]
alias Sorted.filter := Pairwise.filter

@[deprecated (since := "2025-10-11")]
alias sorted_singleton := pairwise_singleton

@[deprecated  (since := "2025-10-11")]
alias Sorted.head!_le := Pairwise.head!_le

@[deprecated  (since := "2025-10-11")]
alias Sorted.le_head! := Pairwise.head!_le

@[deprecated (since := "2025-10-11")]
alias sorted_replicate := pairwise_replicate_of_refl

@[deprecated (since := "2025-10-11")]
alias Sorted.rel_get_of_lt := Pairwise.rel_get_of_lt

@[deprecated (since := "2025-10-11")]
alias Sorted.rel_get_of_le := Pairwise.rel_get_of_le

@[deprecated (since := "2025-10-11")]
alias Sorted.rel_of_mem_take_of_mem_drop := Pairwise.rel_of_mem_take_of_mem_drop

@[deprecated (since := "2025-10-11")]
alias Sorted.decide := Pairwise.decide

@[deprecated Pairwise.filterMap (since := "2025-10-11")]
lemma Sorted.filterMap {α β : Type*} {p : α → Option β} {l : List α}
    {r : α → α → Prop} {r' : β → β → Prop} (hl : l.Pairwise r)
    (hp : ∀ (a b : α) (c d : β), p a = some c → p b = some d → r a b → r' c d) :
    (l.filterMap p).Pairwise r' := by
  exact Pairwise.filterMap _ (fun _ _ hr _ hp₁ _ hp₂ => hp _ _ _ _ hp₁ hp₂ hr) hl

end Sorted

section sort

variable {α β : Type v} (r : α → α → Prop) (s : β → β → Prop)

variable [DecidableRel r] [DecidableRel s]

local infixl:50 " ≼ " => r
local infixl:50 " ≼ " => s

/-! ### Insertion sort -/

section InsertionSort

/-- `orderedInsert a l` inserts `a` into `l` at such that
  `orderedInsert a l` is sorted if `l` is. -/
@[simp]
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

theorem orderedInsert_of_le {a b : α} (l : List α) (h : a ≼ b) :
    orderedInsert r a (b :: l) = a :: b :: l :=
  dif_pos h

/-- `insertionSort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp]
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert r b (insertionSort l)

-- A quick check that insertionSort is stable:
example :
    insertionSort (fun m n => m / 10 ≤ n / 10) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] =
      [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567] := rfl

@[simp]
theorem orderedInsert_nil (a : α) : [].orderedInsert r a = [a] :=
  rfl

theorem orderedInsert_length : ∀ (L : List α) (a : α), (L.orderedInsert r a).length = L.length + 1
  | [], _ => rfl
  | hd :: tl, a => by
    dsimp [orderedInsert]
    split_ifs <;> simp [orderedInsert_length tl]

/-- An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`. -/
theorem orderedInsert_eq_take_drop (a : α) :
    ∀ l : List α,
      l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b
  | [] => rfl
  | b :: l => by
    dsimp only [orderedInsert]
    split_ifs with h <;> simp [takeWhile, dropWhile, *, orderedInsert_eq_take_drop a l]

theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _

@[simp]
theorem mem_orderedInsert {a b : α} {l : List α} :
    a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l :=
  match l with
  | [] => by simp [orderedInsert]
  | x :: xs => by
    rw [orderedInsert]
    split_ifs
    · simp
    · rw [mem_cons, mem_cons, mem_orderedInsert, or_left_comm]

theorem map_orderedInsert (f : α → β) (l : List α) (x : α)
    (hl₁ : ∀ a ∈ l, a ≼ x ↔ f a ≼ f x) (hl₂ : ∀ a ∈ l, x ≼ a ↔ f x ≼ f a) :
    (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.forall_mem_cons] at hl₁ hl₂
    simp only [List.map, List.orderedInsert, ← hl₂.1]
    split_ifs
    · rw [List.map, List.map]
    · rw [List.map, ih (fun _ ha => hl₁.2 _ ha) (fun _ ha => hl₂.2 _ ha)]

section Correctness

theorem perm_orderedInsert (a) : ∀ l : List α, orderedInsert r a l ~ a :: l
  | [] => Perm.refl _
  | b :: l => by
    by_cases h : a ≼ b
    · simp [orderedInsert, h]
    · simpa [orderedInsert, h] using ((perm_orderedInsert a l).cons _).trans (Perm.swap _ _ _)

theorem orderedInsert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if b = a then 1 else 0 := by
  rw [(L.perm_orderedInsert r b).count_eq, count_cons]
  simp

theorem perm_insertionSort : ∀ l : List α, insertionSort r l ~ l
  | [] => Perm.nil
  | b :: l => by
    simpa [insertionSort] using (perm_orderedInsert _ _ _).trans ((perm_insertionSort l).cons b)

@[simp]
theorem mem_insertionSort {l : List α} {x : α} : x ∈ l.insertionSort r ↔ x ∈ l :=
  (perm_insertionSort r l).mem_iff

@[simp]
theorem length_insertionSort (l : List α) : (insertionSort r l).length = l.length :=
  (perm_insertionSort r _).length_eq

theorem insertionSort_cons {a : α} {l : List α} (h : ∀ b ∈ l, r a b) :
    insertionSort r (a :: l) = a :: insertionSort r l := by
  rw [insertionSort]
  cases hi : insertionSort r l with
  | nil => rfl
  | cons b m =>
    rw [orderedInsert_of_le]
    apply h b <| (mem_insertionSort r).1 _
    rw [hi]
    exact mem_cons_self

theorem map_insertionSort (f : α → β) (l : List α) (hl : ∀ a ∈ l, ∀ b ∈ l, a ≼ b ↔ f a ≼ f b) :
    (l.insertionSort r).map f = (l.map f).insertionSort s := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp_rw [List.forall_mem_cons, forall_and] at hl
    simp_rw [List.map, List.insertionSort]
    rw [List.map_orderedInsert _ s, ih hl.2.2]
    · simpa only [mem_insertionSort] using hl.2.1
    · simpa only [mem_insertionSort] using hl.1.2

variable {r}

/-- If `l` is already `List.Pairwise` with respect to `r`, then `insertionSort` does not change
it. -/
theorem Pairwise.insertionSort_eq : ∀ {l : List α}, Pairwise r l → insertionSort r l = l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [insertionSort, Pairwise.insertionSort_eq, orderedInsert, if_pos]
    exacts [rel_of_pairwise_cons h mem_cons_self, h.tail]

/-- For a reflexive relation, insert then erasing is the identity. -/
theorem erase_orderedInsert [DecidableEq α] [IsRefl α r] (x : α) (xs : List α) :
    (xs.orderedInsert r x).erase x = xs := by
  rw [orderedInsert_eq_take_drop, erase_append_right, List.erase_cons_head,
    takeWhile_append_dropWhile]
  intro h
  replace h := mem_takeWhile_imp h
  simp [refl x] at h

/-- Inserting then erasing an element that is absent is the identity. -/
theorem erase_orderedInsert_of_notMem [DecidableEq α]
    {x : α} {xs : List α} (hx : x ∉ xs) :
    (xs.orderedInsert r x).erase x = xs := by
  rw [orderedInsert_eq_take_drop, erase_append_right, List.erase_cons_head,
    takeWhile_append_dropWhile]
  exact mt ((takeWhile_prefix _).sublist.subset ·) hx

@[deprecated (since := "2025-05-23")]
alias erase_orderedInsert_of_not_mem := erase_orderedInsert_of_notMem

/-- For an antisymmetric relation, erasing then inserting is the identity. -/
theorem orderedInsert_erase [DecidableEq α] [IsAntisymm α r] (x : α) (xs : List α) (hx : x ∈ xs)
    (hxs : Pairwise r xs) :
    (xs.erase x).orderedInsert r x = xs := by
  induction xs generalizing x with
  | nil => cases hx
  | cons y ys ih =>
    rw [pairwise_cons] at hxs
    obtain rfl | hxy := Decidable.eq_or_ne x y
    · rw [erase_cons_head]
      cases ys with
      | nil => rfl
      | cons z zs =>
        rw [orderedInsert, if_pos (hxs.1 _ (.head zs))]
    · rw [mem_cons] at hx
      replace hx := hx.resolve_left hxy
      rw [erase_cons_tail (not_beq_of_ne hxy.symm), orderedInsert, ih _ hx hxs.2, if_neg]
      refine mt (fun hrxy => ?_) hxy
      exact antisymm hrxy (hxs.1 _ hx)

theorem sublist_orderedInsert (x : α) (xs : List α) : xs <+ xs.orderedInsert r x := by
  rw [orderedInsert_eq_take_drop]
  refine Sublist.trans ?_ (.append_left (.cons _ (.refl _)) _)
  rw [takeWhile_append_dropWhile]

theorem cons_sublist_orderedInsert {l c : List α} {a : α} (hl : c <+ l) (ha : ∀ a' ∈ c, a ≼ a') :
    a :: c <+ orderedInsert r a l := by
  induction l with
  | nil         => simp_all only [sublist_nil, orderedInsert, Sublist.refl]
  | cons _ _ ih =>
    unfold orderedInsert
    split_ifs with hr
    · exact .cons₂ _ hl
    · cases hl with
      | cons _ h => exact .cons _ <| ih h
      | cons₂    => exact absurd (ha _ <| mem_cons_self ..) hr

theorem Sublist.orderedInsert_sublist [IsTrans α r] {as bs} (x) (hs : as <+ bs)
    (hb : bs.Pairwise r) : orderedInsert r x as <+ orderedInsert r x bs := by
  cases as with
  | nil => simp
  | cons a as =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      unfold orderedInsert
      cases hs <;> split_ifs with hr
      · exact .cons₂ _ <| .cons _ ‹a :: as <+ bs›
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs›  hb.of_cons
        simp only [hr, orderedInsert, ite_true] at ih
        exact .trans ih <| .cons _ (.refl _)
      · have hba := pairwise_cons.mp hb |>.left _ (mem_of_cons_sublist ‹a :: as <+ bs›)
        exact absurd (trans_of _ ‹r x b› hba) hr
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        rw [orderedInsert, if_neg hr] at ih
        exact .cons _ ih
      · simp_all only [pairwise_cons, cons_sublist_cons]
      · exact .cons₂ _ <| orderedInsert_sublist x ‹as <+ bs› hb.of_cons

section TotalAndTransitive

variable [IsTotal α r] [IsTrans α r]

theorem Pairwise.orderedInsert (a : α) : ∀ l, Pairwise r l → Pairwise r (orderedInsert r a l)
  | [], _ => pairwise_singleton _ a
  | b :: l, h => by
    by_cases h' : a ≼ b
    · simpa [orderedInsert, h', h] using fun b' bm => _root_.trans h' (rel_of_pairwise_cons h bm)
    · suffices ∀ b' : α, b' ∈ List.orderedInsert r a l → r b b' by
        simpa [orderedInsert, h', h.of_cons.orderedInsert a l]
      intro b' bm
      rcases (mem_orderedInsert r).mp bm with be | bm
      · subst b'
        exact (total_of r _ _).resolve_left h'
      · exact rel_of_pairwise_cons h bm

variable (r)

/-- The list `List.insertionSort r l` is `List.Pairwise` with respect to `r`. -/
theorem pairwise_insertionSort : ∀ l, Pairwise r (insertionSort r l)
  | [] => Pairwise.nil
  | a :: l => (pairwise_insertionSort l).orderedInsert a _

@[deprecated (since := "2025-10-11")]
alias sorted_insertionSort := pairwise_insertionSort

end TotalAndTransitive

/--
If `c` is a sorted sublist of `l`, then `c` is still a sublist of `insertionSort r l`.
-/
theorem sublist_insertionSort {l c : List α} (hr : c.Pairwise r) (hc : c <+ l) :
    c <+ insertionSort r l := by
  induction l generalizing c with
  | nil         => simp_all only [sublist_nil, insertionSort, Sublist.refl]
  | cons _ _ ih =>
    cases hc with
    | cons  _ h => exact ih hr h |>.trans (sublist_orderedInsert ..)
    | cons₂ _ h =>
      obtain ⟨hr, hp⟩ := pairwise_cons.mp hr
      exact cons_sublist_orderedInsert (ih hp h) hr

/--
Another statement of stability of insertion sort.
If a pair `[a, b]` is a sublist of `l` and `r a b`,
then `[a, b]` is still a sublist of `insertionSort r l`.
-/
theorem pair_sublist_insertionSort {a b : α} {l : List α} (hab : r a b) (h : [a, b] <+ l) :
    [a, b] <+ insertionSort r l :=
  sublist_insertionSort (pairwise_pair.mpr hab) h

variable [IsAntisymm α r] [IsTotal α r] [IsTrans α r]

/--
A version of `insertionSort_stable` which only assumes `c <+~ l` (instead of `c <+ l`), but
additionally requires `IsAntisymm α r`, `IsTotal α r` and `IsTrans α r`.
-/
theorem sublist_insertionSort' {l c : List α} (hs : c.Pairwise r) (hc : c <+~ l) :
    c <+ insertionSort r l := by
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil         => simp_all only [sublist_nil, insertionSort, nil_perm]
  | cons a _ ih =>
    cases hd with
    | cons  _ h => exact ih hs _ hc h |>.trans (sublist_orderedInsert ..)
    | cons₂ _ h =>
      specialize ih (hs.erase _) _ (erase_cons_head a ‹List _› ▸ hc.erase a) h
      have hm := hc.mem_iff.mp <| mem_cons_self ..
      have he := orderedInsert_erase _ _ hm hs
      exact he ▸ Sublist.orderedInsert_sublist _ ih (pairwise_insertionSort ..)

/--
Another statement of stability of insertion sort.
If a pair `[a, b]` is a sublist of a permutation of `l` and `a ≼ b`,
then `[a, b]` is still a sublist of `insertionSort r l`.
-/
theorem pair_sublist_insertionSort' {a b : α} {l : List α} (hab : a ≼ b) (h : [a, b] <+~ l) :
    [a, b] <+ insertionSort r l :=
  sublist_insertionSort' (pairwise_pair.mpr hab) h

end Correctness

end InsertionSort

/-! ### Merge sort

We provide some wrapper functions around the theorems for `mergeSort` provided in Lean,
which rather than using explicit hypotheses for transitivity and totality,
use Mathlib order typeclasses instead.
-/

example :
    mergeSort [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] (fun m n => m / 10 ≤ n / 10) =
      [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567] := by simp [mergeSort]

section MergeSort

section Correctness

section IsAntisymm

variable {r : α → α → Prop} [IsAntisymm α r]

/-- Variant of `Perm.eq_of_sorted` using relation typeclasses. -/
theorem Perm.eq_of_pairwise {l₁ l₂ : List α} (hp : l₁ ~ l₂)
    (hs₁ : Pairwise r l₁) (hs₂ : Pairwise r l₂) : l₁ = l₂ :=
  hp.eq_of_sorted (fun _ _ _ _ => antisymm) hs₁ hs₂

@[deprecated (since := "2025-10-11")]
alias eq_of_perm_of_sorted := Perm.eq_of_pairwise

theorem Pairwise.eq_of_mem_iff [IsIrrefl α r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  ((perm_ext_iff_of_nodup h₁.nodup h₂.nodup).2 h).eq_of_pairwise h₁ h₂

@[deprecated (since := "2025-10-11")]
alias Sorted.eq_of_mem_iff := Pairwise.eq_of_mem_iff

theorem sublist_of_subperm_of_pairwise {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
    (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := hp
  rwa [← h.eq_of_pairwise (hs₂.sublist h') hs₁]

@[deprecated (since := "2025-10-11")]
alias sublist_of_subperm_of_sorted := sublist_of_subperm_of_pairwise

end IsAntisymm

section TotalAndTransitive

variable {r} [IsTotal α r] [IsTrans α r]

theorem Pairwise.merge {l l' : List α} (h : Pairwise r l) (h' : Pairwise r l') :
    Pairwise r (merge l l' (r · ·)) := by
  simpa using sorted_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using IsTotal.total a b)
    l l' (by simpa using h) (by simpa using h')

variable (r)

/-- Variant of `sorted_mergeSort` using relation typeclasses. -/
theorem pairwise_mergeSort (l : List α) : Pairwise r (mergeSort l (r · ·)) := by
  simpa using sorted_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

variable [IsAntisymm α r]

theorem mergeSort_eq_self {l : List α} : Pairwise r l → mergeSort l (r · ·) = l :=
  (mergeSort_perm _ _).eq_of_pairwise (pairwise_mergeSort _ l)

theorem mergeSort_eq_insertionSort (l : List α) :
    mergeSort l (r · ·) = insertionSort r l :=
  ((mergeSort_perm l _).trans (perm_insertionSort r l).symm).eq_of_pairwise
    (pairwise_mergeSort r l) (pairwise_insertionSort r l)

end TotalAndTransitive

end Correctness

end MergeSort

end sort

section Sorted

variable {α : Type u} {a b : α} {l : List α}

/-!
### The predicates `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`
-/

section Preorder

variable [Preorder α]

/-- `SortedLE l` means that the list is monotonic. -/
@[irreducible] def SortedLE (l : List α) := Monotone l.get
/-- `SortedGE l` means that the list is antitonic. -/
@[irreducible] def SortedGE (l : List α) := Antitone l.get
/-- `SortedLT l` means that the list is strictly monotonic. -/
@[irreducible] def SortedLT (l : List α) := StrictMono l.get
/-- `SortedGT l` means that the list is strictly antitonic. -/
@[irreducible] def SortedGT (l : List α) := StrictAnti l.get

unseal SortedLE in theorem sortedLE_iff_monotone : l.SortedLE ↔ Monotone l.get := Iff.rfl
alias ⟨SortedLE.get_mono, _⟩ := sortedLE_iff_monotone
unseal SortedGE in theorem sortedGE_iff_antitone : l.SortedGE ↔ Antitone l.get := Iff.rfl
alias ⟨SortedGE.get_anti, _⟩ := sortedGE_iff_antitone
unseal SortedLT in theorem sortedLT_iff_strictMono : l.SortedLT ↔ StrictMono l.get := Iff.rfl
alias ⟨SortedLT.get_strictMono, _⟩ := sortedLT_iff_strictMono
unseal SortedGT in theorem sortedGT_iff_strictAnti : l.SortedGT ↔ StrictAnti l.get := Iff.rfl
alias ⟨SortedGT.get_strictAnti, _⟩ := sortedGT_iff_strictAnti

theorem sortedLE_iff_get : l.SortedLE ↔ ∀ (i j : Fin l.length), i < j → l.get i ≤ l.get j :=
  sortedLE_iff_monotone.trans monotone_iff_forall_lt
theorem sortedGE_iff_get : l.SortedGE ↔ ∀ (i j : Fin l.length), i < j → l.get j ≤ l.get i :=
  sortedGE_iff_antitone.trans antitone_iff_forall_lt
theorem sortedLT_iff_get : l.SortedLT ↔ ∀ (i j : Fin l.length), i < j → l.get i < l.get j :=
  sortedLT_iff_strictMono
theorem sortedGT_iff_get : l.SortedGT ↔ ∀ (i j : Fin l.length), i < j → l.get j < l.get i :=
  sortedGT_iff_strictAnti

@[grind] theorem sortedLE_iff_getElem : l.SortedLE ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[i] ≤ l[j] := by
  simp_rw [sortedLE_iff_get, Fin.forall_iff]; grind
@[grind] theorem sortedGE_iff_getElem : l.SortedGE ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[j] ≤ l[i] := by
  simp_rw [sortedGE_iff_get, Fin.forall_iff]; grind
@[grind] theorem sortedLT_iff_getElem : l.SortedLT ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[i] < l[j] := by
  simp_rw [sortedLT_iff_get, Fin.forall_iff]; grind
@[grind] theorem sortedGT_iff_getElem : l.SortedGT ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[j] < l[i] := by
  simp_rw [sortedGT_iff_get, Fin.forall_iff]; grind

@[grind] theorem sortedLE_iff_pairwise : SortedLE l ↔ Pairwise (· ≤ ·) l :=
  sortedLE_iff_get.trans (Iff.symm pairwise_iff_get)
alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
@[grind] theorem sortedGE_iff_pairwise : SortedGE l ↔ Pairwise (· ≥ ·) l :=
  sortedGE_iff_get.trans (Iff.symm pairwise_iff_get)
alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
@[grind] theorem sortedLT_iff_pairwise : SortedLT l ↔ Pairwise (· < ·) l :=
  sortedLT_iff_get.trans (Iff.symm pairwise_iff_get)
alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
@[grind] theorem sortedGT_iff_pairwise : SortedGT l ↔ Pairwise (· > ·) l :=
  sortedGT_iff_get.trans (Iff.symm pairwise_iff_get)
alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise

@[grind] theorem sortedLE_iff_isChain : SortedLE l ↔ IsChain (· ≤ ·) l :=
  sortedLE_iff_pairwise.trans isChain_iff_pairwise.symm
alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
@[grind] theorem sortedGE_iff_isChain : SortedGE l ↔ IsChain (· ≥ ·) l :=
  sortedGE_iff_pairwise.trans isChain_iff_pairwise.symm
alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
@[grind] theorem sortedLT_iff_isChain : SortedLT l ↔ IsChain (· < ·) l :=
  sortedLT_iff_pairwise.trans isChain_iff_pairwise.symm
alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
@[grind] theorem sortedGT_iff_isChain : SortedGT l ↔ IsChain (· > ·) l :=
  sortedGT_iff_pairwise.trans isChain_iff_pairwise.symm
alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

instance decidableSortedLE [DecidableLE α] : Decidable (l.SortedLE) :=
  decidable_of_iff' _ sortedLE_iff_isChain
instance decidableSortedGE [DecidableLE α] : Decidable (l.SortedGE) :=
  decidable_of_iff' _ sortedGE_iff_isChain
instance decidableSortedLT [DecidableLT α] : Decidable (l.SortedLT) :=
  decidable_of_iff' _ sortedLT_iff_isChain
instance decidableSortedGT [DecidableLT α] : Decidable (l.SortedGT) :=
  decidable_of_iff' _ sortedGT_iff_isChain

protected theorem SortedLT.sortedLE {l : List α} (h : l.SortedLT) :
    l.SortedLE := (h.pairwise.imp le_of_lt).isChain.sortedLE

protected theorem SortedGT.sortedGE {l : List α} (h : l.SortedGT) :
    l.SortedGE := (h.pairwise.imp le_of_lt).isChain.sortedGE

theorem SortedLT.nodup (h : l.SortedLT) : l.Nodup := h.pairwise.imp (fun {_ _} ↦ ne_of_lt)
theorem SortedGT.nodup (h : l.SortedGT) : l.Nodup := h.pairwise.imp (fun {_ _} ↦ ne_of_gt)

@[simp] theorem sortedLE_reverse : l.reverse.SortedLE ↔ l.SortedGE := by
  simp_rw [sortedGE_iff_pairwise, sortedLE_iff_pairwise, pairwise_reverse]
alias ⟨_, SortedGE.reverse⟩ := sortedLE_reverse
@[simp] theorem sortedGE_reverse : l.reverse.SortedGE ↔ l.SortedLE := by
  simp_rw [sortedGE_iff_pairwise, sortedLE_iff_pairwise, pairwise_reverse]
alias ⟨_, SortedLE.reverse⟩ := sortedGE_reverse
@[simp] theorem sortedLT_reverse : l.reverse.SortedLT ↔ l.SortedGT := by
  simp_rw [sortedGT_iff_pairwise, sortedLT_iff_pairwise, pairwise_reverse]
alias ⟨_, SortedGT.reverse⟩ := sortedLT_reverse
@[simp] theorem sortedGT_reverse : l.reverse.SortedGT ↔ l.SortedLT := by
  simp_rw [sortedGT_iff_pairwise, sortedLT_iff_pairwise, pairwise_reverse]
alias ⟨_, SortedLT.reverse⟩ := sortedGT_reverse

@[simp] theorem sortedLE_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLE ↔ l.SortedGE := by
  simp_rw [sortedLE_iff_pairwise, sortedGE_iff_pairwise, pairwise_map, OrderDual.ofDual_le_ofDual]

@[simp] theorem sortedLE_map_toDual :
    (l.map OrderDual.toDual).SortedLE ↔ l.SortedGE := by
  simp_rw [sortedLE_iff_pairwise, sortedGE_iff_pairwise, pairwise_map, OrderDual.toDual_le_toDual]

@[simp] theorem sortedGE_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedGE ↔ l.SortedLE := by
  simp_rw [sortedLE_iff_pairwise, sortedGE_iff_pairwise, pairwise_map, OrderDual.ofDual_le_ofDual]

@[simp] theorem sortedGE_map_toDual :
    (l.map OrderDual.toDual).SortedGE ↔ l.SortedLE := by
  simp_rw [sortedLE_iff_pairwise, sortedGE_iff_pairwise, pairwise_map, OrderDual.toDual_le_toDual]

@[simp] theorem sortedLT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLT ↔ l.SortedGT := by
  simp_rw [sortedLT_iff_pairwise, sortedGT_iff_pairwise, pairwise_map, OrderDual.ofDual_lt_ofDual]

@[simp] theorem sortedLT_map_toDual :
    (l.map OrderDual.toDual).SortedLT ↔ l.SortedGT := by
  simp_rw [sortedLT_iff_pairwise, sortedGT_iff_pairwise, pairwise_map, OrderDual.toDual_lt_toDual]

@[simp] theorem sortedGT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedGT ↔ l.SortedLT := by
  simp_rw [sortedLT_iff_pairwise, sortedGT_iff_pairwise, pairwise_map, OrderDual.ofDual_lt_ofDual]

@[simp] theorem sortedGT_map_toDual :
    (l.map OrderDual.toDual).SortedGT ↔ l.SortedLT := by
  simp_rw [sortedLT_iff_pairwise, sortedGT_iff_pairwise, pairwise_map, OrderDual.toDual_lt_toDual]

theorem sortedLT_range (n : ℕ) : (range n).SortedLT := by
  rw [sortedLT_iff_getElem]
  simp

lemma sortedLT_range' (a b) {s} (hs : s ≠ 0) :
    (range' a b s).SortedLT := by
  simp [sortedLT_iff_getElem, Nat.pos_of_ne_zero hs]

lemma sorted_le_range' (a b s) :
    (range' a b s).SortedLE := by
  by_cases hs : s ≠ 0
  · exact (sortedLT_range' a b hs).sortedLE
  · rw [ne_eq, Decidable.not_not] at hs
    rw [hs, range'_0]
    exact pairwise_replicate_of_refl.isChain.sortedLE

section OfFn

variable {n : ℕ} {f : Fin n → α}

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
@[simp] theorem sortedLE_ofFn_iff : (ofFn f).SortedLE ↔ Monotone f :=
  sortedLE_iff_monotone.trans (by simp [Monotone, Fin.forall_iff])

/-- The list `List.ofFn f` is sorted with respect to `(· ≥ ·)` if and only if `f` is antitone. -/
@[simp] theorem sortedGE_ofFn_iff : (ofFn f).SortedGE ↔ Antitone f :=
  sortedGE_iff_antitone.trans (by simp [Antitone, Fin.forall_iff])

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
@[simp] theorem sortedLT_ofFn_iff : (ofFn f).SortedLT ↔ StrictMono f :=
  sortedLT_iff_strictMono.trans (by simp [StrictMono, Fin.forall_iff])

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≥ ·)` if and only if `f` is
strictly antitone. -/
@[simp] theorem sortedGT_ofFn_iff : (ofFn f).SortedGT ↔ StrictAnti f :=
  sortedGT_iff_strictAnti.trans (by simp [StrictAnti, Fin.forall_iff])

/-- The list obtained from a monotone tuple is sorted. -/
alias ⟨_, _root_.Monotone.ofFn_sortedLE⟩ := sortedLE_ofFn_iff
/-- The list obtained from an antitone tuple is sorted. -/
alias ⟨_, _root_.Antitone.ofFn_sortedGE⟩ := sortedGE_ofFn_iff
/-- The list obtained from a strictly monotone tuple is sorted. -/
alias ⟨_, _root_StrictMono.ofFn_sortedLT⟩ := sortedLT_ofFn_iff
/-- The list obtained from an antitone tuple is sorted. -/
alias ⟨_, _root_.StrictAnti.ofFn_sortedGT⟩ := sortedGT_ofFn_iff

end OfFn

end Preorder

section PartialOrder

variable [PartialOrder α]

protected theorem SortedLE.sortedLT {l : List α} (h₁ : l.SortedLE)
    (h₂ : l.Nodup) : l.SortedLT :=
  (h₁.pairwise.imp₂ (fun _ _ => lt_of_le_of_ne) h₂).isChain.sortedLT

protected theorem SortedGE.sortedGT {l : List α} (h₁ : l.SortedGE)
    (h₂ : l.Nodup) : l.SortedGT :=
  (h₁.pairwise.imp₂ (fun _ _ => lt_of_le_of_ne) <| h₂.imp Ne.symm).isChain.sortedGT

theorem sortedLT_iff_nodup_and_sortedLE : l.SortedLT ↔ l.Nodup ∧ l.SortedLE :=
  ⟨fun h => ⟨h.nodup, h.sortedLE⟩, fun h => h.2.sortedLT h.1⟩

theorem sortedGT_iff_nodup_and_sortedGE : l.SortedGT ↔ l.Nodup ∧ l.SortedGE :=
  ⟨fun h => ⟨h.nodup, h.sortedGE⟩, fun h => h.2.sortedGT h.1⟩

theorem SortedLE.eq_of_perm {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : l₁ = l₂ := eq_of_pairwise hp hl₁.pairwise hl₂.pairwise

theorem SortedGE.eq_of_perm {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : l₁ = l₂ := eq_of_pairwise hp hl₁.pairwise hl₂.pairwise

theorem SortedLT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise h

theorem SortedGT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise h

theorem SortedLE.eq_reverse_of_perm_of_sortedGE {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedGE) : l₁ = l₂.reverse :=
  eq_of_pairwise (perm_reverse.mpr hp) hl₁.pairwise (sortedLE_reverse.mpr hl₂).pairwise

theorem SortedGE.eq_reverse_of_perm_of_sortedLE {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedLE) : l₁ = l₂.reverse :=
  eq_of_pairwise (perm_reverse.mpr hp) hl₁.pairwise (sortedGE_reverse.mpr hl₂).pairwise

theorem SortedLT.eq_reverse_of_mem_iff_of_sortedGT {l₁ l₂ : List α}
    (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) (hl₁ : l₁.SortedLT)
    (hl₂ : l₂.SortedGT) : l₁ = l₂.reverse :=
  hl₁.pairwise.eq_of_mem_iff (sortedLT_reverse.mpr hl₂).pairwise (by simp [h])

theorem SortedGT.eq_reverse_of_mem_iff_of_sortedLT {l₁ l₂ : List α}
    (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) (hl₁ : l₁.SortedGT)
    (hl₂ : l₂.SortedLT) : l₁ = l₂.reverse :=
  hl₁.pairwise.eq_of_mem_iff (sortedGT_reverse.mpr hl₂).pairwise (by simp [h])

theorem SortedLE.sublist_of_subperm {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

theorem SortedGE.sublist_of_subperm {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem sortedLE_mergeSort : (l.mergeSort (· ≤ ·)).SortedLE := by
  simp_rw [sortedLE_iff_pairwise, pairwise_mergeSort]

theorem sortedGE_mergeSort : (l.mergeSort (· ≥ ·)).SortedGE := by
  simp_rw [sortedGE_iff_pairwise, pairwise_mergeSort]

theorem sortedLE_insertionSort : (l.insertionSort (· ≤ ·)).SortedLE := by
  simp_rw [sortedLE_iff_pairwise, pairwise_insertionSort]

theorem sortedGE_insertionSort : (l.insertionSort (· ≥ ·)).SortedGE := by
  simp_rw [sortedGE_iff_pairwise, pairwise_insertionSort]

@[simp]
theorem SortedLT.getElem_le_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] ≤ l[j] ↔ i ≤ j := hl.get_strictMono.le_iff_le

@[simp]
theorem SortedGT.getElem_le_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] ≤ l[j] ↔ j ≤ i := hl.get_strictAnti.le_iff_ge

@[simp]
theorem SortedLT.getElem_lt_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ i < j := by
  simp_rw [lt_iff_le_and_ne, hl.getElem_le_getElem_iff, ne_eq, hl.nodup.getElem_inj_iff]

@[simp]
theorem SortedGT.getElem_lt_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ j < i := by
  simp_rw [lt_iff_le_and_ne, hl.getElem_le_getElem_iff, ne_eq, hl.nodup.getElem_inj_iff, eq_comm]

end LinearOrder

end Sorted

end List

namespace RelEmbedding

open List

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
theorem pairwise_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra := by
  simp [pairwise_map, e.map_rel_iff]

@[simp]
theorem pairwise_swap_listMap (e : ra ↪r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) := by
  simp [pairwise_map, e.map_rel_iff]

end RelEmbedding

namespace RelIso

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
theorem pairwise_listMap (e : ra ≃r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra :=
  e.toRelEmbedding.pairwise_listMap

@[simp]
theorem pairwise_swap_listMap (e : ra ≃r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) :=
  e.toRelEmbedding.pairwise_swap_listMap

end RelIso

namespace OrderEmbedding

open List

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem sortedLE_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedLE ↔ l.SortedLE := by
  simp_rw [sortedLE_iff_pairwise, e.pairwise_listMap]

@[simp]
theorem sortedLT_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedLT ↔ l.SortedLT := by
  simp_rw [sortedLT_iff_pairwise]
  exact e.ltEmbedding.pairwise_listMap

@[simp]
theorem sortedGE_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedGE ↔ l.SortedGE := by
  simp_rw [← sortedLE_reverse, ← map_reverse, sortedLE_listMap]

@[simp]
theorem sortedGT_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedGT ↔ l.SortedGT := by
  simp_rw [← sortedLT_reverse, ← map_reverse, sortedLT_listMap]

end OrderEmbedding

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem sortedLT_listMap (e : α ≃o β) {l : List α} :
    (l.map e).SortedLT ↔ l.SortedLT :=
  e.toOrderEmbedding.sortedLT_listMap

@[simp]
theorem sortedGT_listMap (e : α ≃o β) {l : List α} :
    (l.map e).SortedGT ↔ l.SortedGT :=
  e.toOrderEmbedding.sortedGT_listMap

end OrderIso

namespace StrictMono

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

theorem sortedLE_listMap (hf : StrictMono f) :
    (l.map f).SortedLE ↔ l.SortedLE :=
  (OrderEmbedding.ofStrictMono f hf).sortedLE_listMap

theorem sortedGE_listMap (hf : StrictMono f) :
    (l.map f).SortedGE ↔ l.SortedGE :=
  (OrderEmbedding.ofStrictMono f hf).sortedGE_listMap

theorem sortedLT_listMap (hf : StrictMono f) :
    (l.map f).SortedLT ↔ l.SortedLT :=
  (OrderEmbedding.ofStrictMono f hf).sortedLT_listMap

theorem sortedGT_listMap (hf : StrictMono f) :
    (l.map f).SortedGT ↔ l.SortedGT :=
  (OrderEmbedding.ofStrictMono f hf).sortedGT_listMap

end StrictMono

namespace StrictAnti

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

theorem sorted_le_listMap (hf : StrictAnti f) :
    (l.map f).SortedLE ↔ l.SortedGE := by
  simp_rw [← List.sortedGE_map_toDual, List.map_map, hf.dual_right.sortedGE_listMap]

theorem sorted_ge_listMap (hf : StrictAnti f) :
    (l.map f).SortedGE ↔ l.SortedLE := by
  simp_rw [← List.sortedLE_map_toDual, List.map_map, hf.dual_right.sortedLE_listMap]

theorem sorted_lt_listMap (hf : StrictAnti f) :
    (l.map f).SortedLT ↔ l.SortedGT := by
  simp_rw [← List.sortedGT_map_toDual, List.map_map, hf.dual_right.sortedGT_listMap]

theorem sorted_gt_listMap (hf : StrictAnti f) :
    (l.map f).SortedGT ↔ l.SortedLT := by
  simp_rw [← List.sortedLT_map_toDual, List.map_map, hf.dual_right.sortedLT_listMap]

end StrictAnti
