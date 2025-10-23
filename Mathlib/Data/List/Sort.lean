/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Wrenna Robson
-/
import Mathlib.Data.List.Nodup
import Mathlib.Order.Fin.Basic

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

/-- `Sorted r l` is the same as `List.Pairwise r l` and has been deprecated. -/
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
alias sorted_cons := pairwise_cons

@[deprecated (since := "2025-10-11")]
alias Sorted.filter := Pairwise.filter

@[deprecated (since := "2025-10-11")]
alias sorted_singleton := pairwise_singleton

@[deprecated (since := "2025-10-11")]
alias Sorted.rel_of_mem_take_of_mem_drop := Pairwise.rel_of_mem_take_of_mem_drop

@[deprecated (since := "2025-10-11")]
alias Sorted.filterMap := Pairwise.filterMap

end Sorted

section sort

variable {α β : Type*} (r : α → α → Prop) (s : β → β → Prop)

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

theorem orderedInsert_length (L : List α) (a : α) :
    (L.orderedInsert r a).length = L.length + 1 := by
  induction L <;> grind [orderedInsert]

/-- An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`. -/
theorem orderedInsert_eq_take_drop (a : α) (l : List α) :
      l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b := by
    induction l <;> grind [orderedInsert, takeWhile, dropWhile]

theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _

@[simp]
theorem mem_orderedInsert {a b : α} {l : List α} :
    a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l := by
  induction l <;> grind [orderedInsert]

theorem map_orderedInsert (f : α → β) (l : List α) (x : α)
    (hl₁ : ∀ a ∈ l, a ≼ x ↔ f a ≼ f x) (hl₂ : ∀ a ∈ l, x ≼ a ↔ f x ≼ f a) :
    (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x) := by
  induction l <;> grind [orderedInsert]

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

@[deprecated (since := "2025-10-11")]
alias Sorted.insertionSort_eq := Pairwise.insertionSort_eq

/-- For a reflexive relation, insert then erasing is the identity. -/
theorem erase_orderedInsert [DecidableEq α] [IsRefl α r] (x : α) (xs : List α) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind [orderedInsert, IsRefl]

/-- Inserting then erasing an element that is absent is the identity. -/
theorem erase_orderedInsert_of_notMem [DecidableEq α]
    {x : α} {xs : List α} (hx : x ∉ xs) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind [orderedInsert, IsRefl]

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
  induction xs <;> grind [orderedInsert]

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
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
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

@[deprecated (since := "2025-10-11")]
alias Sorted.orderedInsert := Pairwise.orderedInsert

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

variable [Preorder α] {n : ℕ} {f : Fin n → α}

/-!
These predicates are equivalent to `Monotone l.get` etc., but they are also equivalent to
`IsChain (· < ·)` and `Pairwise (· < ·)`. API is provided to move between these proofs.

API has deliberately not been provided for decomposed lists to avoid unneeded API replication.
The provided API should be used to move to and from `Monotone` (or its equivalents),
`Pairwise` or `IsChain` as needed.
--/

/-- `SortedLE l` means that the list is monotonic. -/
@[irreducible] def SortedLE (l : List α) := l.IsChain (· ≤ ·)
/-- `SortedGE l` means that the list is antitonic. -/
@[irreducible] def SortedGE (l : List α) := l.IsChain (· ≥ ·)
/-- `SortedLT l` means that the list is strictly monotonic. -/
@[irreducible] def SortedLT (l : List α) := l.IsChain (· < ·)
/-- `SortedGT l` means that the list is strictly antitonic. -/
@[irreducible] def SortedGT (l : List α) := l.IsChain (· > ·)

unseal SortedLE in theorem sortedLE_iff_isChain : SortedLE l ↔ IsChain (· ≤ ·) l := Iff.rfl
alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
unseal SortedGE in theorem sortedGE_iff_isChain : SortedGE l ↔ IsChain (· ≥ ·) l := Iff.rfl
alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
unseal SortedLT in theorem sortedLT_iff_isChain : SortedLT l ↔ IsChain (· < ·) l := Iff.rfl
alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
unseal SortedGT in theorem sortedGT_iff_isChain : SortedGT l ↔ IsChain (· > ·) l := Iff.rfl
alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

attribute [grind] sortedLE_iff_isChain sortedGE_iff_isChain
  sortedLT_iff_isChain sortedGT_iff_isChain

instance decidableSortedLE [DecidableLE α] : Decidable (l.SortedLE) :=
  decidable_of_iff' _ sortedLE_iff_isChain
instance decidableSortedGE [DecidableLE α] : Decidable (l.SortedGE) :=
  decidable_of_iff' _ sortedGE_iff_isChain
instance decidableSortedLT [DecidableLT α] : Decidable (l.SortedLT) :=
  decidable_of_iff' _ sortedLT_iff_isChain
instance decidableSortedGT [DecidableLT α] : Decidable (l.SortedGT) :=
  decidable_of_iff' _ sortedGT_iff_isChain

theorem sortedLE_iff_pairwise : SortedLE l ↔ Pairwise (· ≤ ·) l :=
  sortedLE_iff_isChain.trans isChain_iff_pairwise
alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
theorem sortedGE_iff_pairwise : SortedGE l ↔ Pairwise (· ≥ ·) l :=
  sortedGE_iff_isChain.trans isChain_iff_pairwise
alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
theorem sortedLT_iff_pairwise : SortedLT l ↔ Pairwise (· < ·) l :=
  sortedLT_iff_isChain.trans isChain_iff_pairwise
alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
theorem sortedGT_iff_pairwise : SortedGT l ↔ Pairwise (· > ·) l :=
  sortedGT_iff_isChain.trans isChain_iff_pairwise
alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise

theorem sortedLE_iff_getElem : l.SortedLE ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[i] ≤ l[j] :=
  sortedLE_iff_pairwise.trans pairwise_iff_getElem
alias ⟨SortedLE.getElem_le_getElem, _⟩ := sortedLE_iff_getElem
theorem sortedGE_iff_getElem : l.SortedGE ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[j] ≤ l[i] :=
  sortedGE_iff_pairwise.trans pairwise_iff_getElem
alias ⟨SortedGE.getElem_le_getElem, _⟩ := sortedGE_iff_getElem
theorem sortedLT_iff_getElem : l.SortedLT ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[i] < l[j] :=
  sortedLT_iff_pairwise.trans pairwise_iff_getElem
alias ⟨SortedLT.getElem_lt_getElem, _⟩ := sortedLT_iff_getElem
theorem sortedGT_iff_getElem : l.SortedGT ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), i < j → l[j] < l[i] :=
  sortedGT_iff_pairwise.trans pairwise_iff_getElem
alias ⟨SortedGT.getElem_lt_getElem, _⟩ := sortedGT_iff_getElem

theorem sortedLE_iff_get : l.SortedLE ↔ ∀ (i j : Fin l.length), i < j → l.get i ≤ l.get j := by
  simp_rw [sortedLE_iff_getElem, Fin.forall_iff]; grind
alias ⟨SortedLE.get_le_get, _⟩ := sortedLE_iff_get
theorem sortedGE_iff_get : l.SortedGE ↔ ∀ (i j : Fin l.length), i < j → l.get j ≤ l.get i := by
  simp_rw [sortedGE_iff_getElem, Fin.forall_iff]; grind
alias ⟨SortedGE.get_le_get, _⟩ := sortedGE_iff_get
theorem sortedLT_iff_get : l.SortedLT ↔ ∀ (i j : Fin l.length), i < j → l.get i < l.get j := by
  simp_rw [sortedLT_iff_getElem, Fin.forall_iff]; grind
alias ⟨SortedLT.get_lt_get, _⟩ := sortedLT_iff_get
theorem sortedGT_iff_get : l.SortedGT ↔ ∀ (i j : Fin l.length), i < j → l.get j < l.get i := by
  simp_rw [sortedGT_iff_getElem, Fin.forall_iff]; grind
alias ⟨SortedGT.get_lt_get, _⟩ := sortedGT_iff_get

theorem sortedLE_iff_monotone : l.SortedLE ↔ Monotone l.get :=
  sortedLE_iff_get.trans monotone_iff_forall_lt.symm
alias ⟨SortedLE.get_mono, _root_.Monotone.sortedLE⟩ := sortedLE_iff_monotone
theorem sortedGE_iff_antitone : l.SortedGE ↔ Antitone l.get :=
  sortedGE_iff_get.trans antitone_iff_forall_lt.symm
alias ⟨SortedGE.get_anti, _root_.Antitone.sortedGE⟩ := sortedGE_iff_antitone
theorem sortedLT_iff_strictMono : l.SortedLT ↔ StrictMono l.get := sortedLT_iff_get
alias ⟨SortedLT.get_strictMono, _root_.StrictMono.sortedLT⟩ := sortedLT_iff_strictMono
theorem sortedGT_iff_strictAnti : l.SortedGT ↔ StrictAnti l.get := sortedGT_iff_get
alias ⟨SortedGT.get_strictAnti, _root_.StrictAnti.sortedGT⟩ := sortedGT_iff_strictAnti

section OfFn

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
@[simp] theorem sortedLE_ofFn_iff : (ofFn f).SortedLE ↔ Monotone f :=
  sortedLE_iff_monotone.trans (by simp [Monotone, Fin.forall_iff])

/-- The list obtained from a monotone tuple is sorted. -/
alias ⟨_, _root_.Monotone.sortedLE_ofFn⟩ := sortedLE_ofFn_iff

@[deprecated (since := "2025-10-13")]
alias _root_.Monotone.ofFn_sorted := Monotone.sortedLE_ofFn

/-- The list `List.ofFn f` is sorted with respect to `(· ≥ ·)` if and only if `f` is antitone. -/
@[simp] theorem sortedGE_ofFn_iff : (ofFn f).SortedGE ↔ Antitone f :=
  sortedGE_iff_antitone.trans (by simp [Antitone, Fin.forall_iff])

/-- The list obtained from an antitone tuple is sorted. -/
alias ⟨_, _root_.Antitone.sortedGE_ofFn⟩ := sortedGE_ofFn_iff

@[deprecated (since := "2025-10-13")]
alias _root_.Antitone.ofFn_sorted := Antitone.sortedGE_ofFn

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
@[simp] theorem sortedLT_ofFn_iff : (ofFn f).SortedLT ↔ StrictMono f :=
  sortedLT_iff_strictMono.trans (by simp [StrictMono, Fin.forall_iff])

/-- The list obtained from a strictly monotone tuple is sorted. -/
alias ⟨_, _root_.StrictMono.sortedLT_ofFn⟩ := sortedLT_ofFn_iff

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≥ ·)` if and only if `f` is
strictly antitone. -/
@[simp] theorem sortedGT_ofFn_iff : (ofFn f).SortedGT ↔ StrictAnti f :=
  sortedGT_iff_strictAnti.trans (by simp [StrictAnti, Fin.forall_iff])

/-- The list obtained from a strictly antitone tuple is sorted. -/
alias ⟨_, _root_.StrictAnti.sortedGT_ofFn⟩ := sortedGT_ofFn_iff

end OfFn

protected theorem SortedLT.sortedLE {l : List α} (h : l.SortedLT) :
    l.SortedLE := (h.pairwise.imp le_of_lt).sortedLE

protected theorem SortedGT.sortedGE {l : List α} (h : l.SortedGT) :
    l.SortedGE := (h.pairwise.imp le_of_lt).sortedGE

theorem SortedLT.nodup (h : l.SortedLT) : l.Nodup := h.pairwise.nodup
theorem SortedGT.nodup (h : l.SortedGT) : l.Nodup := h.pairwise.nodup

@[simp] theorem sortedLE_reverse : l.reverse.SortedLE ↔ l.SortedGE := by
  simp_rw [sortedGE_iff_pairwise, sortedLE_iff_pairwise, pairwise_reverse]
alias ⟨SortedLE.of_reverse, SortedGE.reverse⟩ := sortedLE_reverse
@[simp] theorem sortedGE_reverse : l.reverse.SortedGE ↔ l.SortedLE := by
  simp_rw [sortedGE_iff_pairwise, sortedLE_iff_pairwise, pairwise_reverse]
alias ⟨SortedGE.of_reverse, SortedLE.reverse⟩ := sortedGE_reverse
@[simp] theorem sortedLT_reverse : l.reverse.SortedLT ↔ l.SortedGT := by
  simp_rw [sortedGT_iff_pairwise, sortedLT_iff_pairwise, pairwise_reverse]
alias ⟨SortedLT.of_reverse, SortedGT.reverse⟩ := sortedLT_reverse
@[simp] theorem sortedGT_reverse : l.reverse.SortedGT ↔ l.SortedLT := by
  simp_rw [sortedGT_iff_pairwise, sortedLT_iff_pairwise, pairwise_reverse]
alias ⟨SortedGT.of_reverse, SortedLT.reverse⟩ := sortedGT_reverse

@[simp] theorem sortedLE_dual {l : List αᵒᵈ} :
    l.SortedLE ↔ (l.map OrderDual.ofDual).SortedGE := by
  simp_rw [sortedLE_iff_pairwise, sortedGE_iff_pairwise, pairwise_map, OrderDual.ofDual_le_ofDual]
alias ⟨SortedLE.of_dual, _⟩ := sortedLE_dual

@[simp] theorem sortedGE_dual {l : List αᵒᵈ} :
    l.SortedGE ↔ (l.map OrderDual.ofDual).SortedLE := by
  simp_rw [sortedLE_iff_pairwise, sortedGE_iff_pairwise, pairwise_map, OrderDual.ofDual_le_ofDual]
alias ⟨SortedGE.of_dual, _⟩ := sortedLE_dual

@[simp] theorem sortedLT_dual {l : List αᵒᵈ} :
    l.SortedLT ↔ (l.map OrderDual.ofDual).SortedGT := by
  simp_rw [sortedLT_iff_pairwise, sortedGT_iff_pairwise, pairwise_map, OrderDual.ofDual_lt_ofDual]
alias ⟨SortedLT.of_dual, _⟩ := sortedLE_dual

@[simp] theorem sortedGT_dual {l : List αᵒᵈ} :
    l.SortedGT ↔ (l.map OrderDual.ofDual).SortedLT := by
  simp_rw [sortedLT_iff_pairwise, sortedGT_iff_pairwise, pairwise_map, OrderDual.ofDual_lt_ofDual]
alias ⟨SortedGT.of_dual, _⟩ := sortedLE_dual

theorem sortedLE_map_toDual :
    (l.map OrderDual.toDual).SortedLE ↔ l.SortedGE := by simp
alias ⟨SortedLE.dual, _⟩ := sortedLE_dual

theorem sortedGE_map_toDual :
    (l.map OrderDual.toDual).SortedGE ↔ l.SortedLE := by simp
alias ⟨SortedGE.dual, _⟩ := sortedGE_dual

theorem sortedLT_map_toDual :
    (l.map OrderDual.toDual).SortedLT ↔ l.SortedGT := by simp
alias ⟨SortedLT.dual, _⟩ := sortedLT_dual

theorem sortedGT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedGT ↔ l.SortedLT := by simp
alias ⟨SortedGT.dual, _⟩ := sortedGT_dual

theorem sortedLT_range (n : ℕ) : (range n).SortedLT := by simp [sortedLT_iff_getElem]

lemma sortedLT_range' (a b) {s} (hs : s ≠ 0) :
    (range' a b s).SortedLT := by simp [sortedLT_iff_getElem, Nat.pos_of_ne_zero hs]

lemma sortedLE_range' (a b s) :
    (range' a b s).SortedLE := by
  simp only [sortedLE_iff_getElem, length_range', getElem_range', Nat.add_le_add_iff_left]
  exact fun _ _ _ _ h => Nat.mul_le_mul_left _ h.le

end Preorder

section PartialOrder

variable [PartialOrder α]

protected theorem SortedLE.sortedLT {l : List α} (h₁ : l.SortedLE)
    (h₂ : l.Nodup) : l.SortedLT :=
  (h₁.pairwise.imp₂ (fun _ _ => lt_of_le_of_ne) h₂).sortedLT

protected theorem SortedGE.sortedGT {l : List α} (h₁ : l.SortedGE)
    (h₂ : l.Nodup) : l.SortedGT :=
  (h₁.pairwise.imp₂ (fun _ _ => lt_of_le_of_ne) <| h₂.imp Ne.symm).sortedGT

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

open List

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

theorem sortedLE_listMap (hf : StrictAnti f) :
    (l.map f).SortedLE ↔ l.SortedGE := by
  simpa using hf.dual_right.sortedGE_listMap

theorem sortedGE_listMap (hf : StrictAnti f) :
    (l.map f).SortedGE ↔ l.SortedLE := by
  simpa using hf.dual_right.sortedLE_listMap

theorem sortedLT_listMap (hf : StrictAnti f) :
    (l.map f).SortedLT ↔ l.SortedGT := by
  simpa using hf.dual_right.sortedGT_listMap

theorem sortedGT_listMap (hf : StrictAnti f) :
    (l.map f).SortedGT ↔ l.SortedLT := by
  simpa using hf.dual_right.sortedLT_listMap

end StrictAnti
