/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Wrenna Robson
-/
module

public import Mathlib.Order.Fin.Basic
import all Init.Data.List.Sort.Basic  -- for exposing `mergeSort`
public import Batteries.Data.List.Basic
import Batteries.Data.List.Perm
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Translate.ToDual
import Mathlib.Util.CompileInductive

/-!
# Sorting algorithms on lists

In this file we define the sorting algorithm `List.insertionSort r` and prove
that we have `(l.insertionSort r l).Pairwise r` under suitable conditions on `r`.

We then define `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`,
predicates which are equivalent to `List.Pairwise` when the relation derives from a
preorder (but which are defined in terms of the monotonicity predicates).
-/

public section

namespace List

section sort

variable {α β : Type*} (r : α → α → Prop) (s : β → β → Prop)

variable [DecidableRel r] [DecidableRel s]

local infixl:50 " ≼ " => r
local infixl:50 " ≼ " => s

/-! ### Insertion sort -/

section InsertionSort

/-- `orderedInsert a l` inserts `a` into `l` at such that
  `orderedInsert a l` is sorted if `l` is. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

@[simp, grind =] theorem orderedInsert_nil (a : α) : [].orderedInsert r a = [a] := .refl _

@[simp, grind =] theorem orderedInsert_cons (a b : α) (l : List α) :
    (b :: l).orderedInsert r a = if r a b then a :: b :: l else b :: l.orderedInsert r a :=
  .refl _

theorem orderedInsert_cons_of_le {a b : α} (l : List α) (h : a ≼ b) :
    orderedInsert r a (b :: l) = a :: b :: l :=
  dif_pos h

@[deprecated (since := "2025-11-27")] alias orderedInsert_of_le := orderedInsert_cons_of_le

theorem orderedInsert_of_not_le {a b : α} (l : List α) (h : ¬ a ≼ b) :
    orderedInsert r a (b :: l) = b :: orderedInsert r a l := dif_neg h

/-- `insertionSort l` returns `l` sorted using the insertion sort algorithm. -/
def insertionSort : List α → List α := foldr (orderedInsert r) []

@[simp, grind =]
theorem insertionSort_nil : [].insertionSort r = [] := .refl _

@[simp, grind =] theorem insertionSort_cons (a : α) (l : List α) :
    (a :: l).insertionSort r = orderedInsert r a (insertionSort r l) := .refl _

-- A quick check that insertionSort is stable:
example :
    insertionSort (fun m n => m / 10 ≤ n / 10) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] =
      [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567] := rfl

theorem orderedInsert_length (L : List α) (a : α) :
    (L.orderedInsert r a).length = L.length + 1 := by
  induction L <;> grind

/-- An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`. -/
theorem orderedInsert_eq_take_drop (a : α) (l : List α) :
    l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b := by
  induction l <;> grind [takeWhile, dropWhile]

theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _

@[simp]
theorem mem_orderedInsert {a b : α} {l : List α} :
    a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l := by
  induction l <;> grind

theorem map_orderedInsert (f : α → β) (l : List α) (x : α)
    (hl₁ : ∀ a ∈ l, a ≼ x ↔ f a ≼ f x) (hl₂ : ∀ a ∈ l, x ≼ a ↔ f x ≼ f a) :
    (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x) := by
  induction l <;> grind

section Correctness

theorem perm_orderedInsert (a) : ∀ l : List α, orderedInsert r a l ~ a :: l
  | [] => Perm.refl _
  | b :: l => by
    by_cases h : a ≼ b
    · simp [h]
    · simpa [h] using ((perm_orderedInsert a l).cons _).trans (Perm.swap _ _ _)

theorem orderedInsert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if b = a then 1 else 0 := by
  rw [(L.perm_orderedInsert r b).count_eq, count_cons]
  simp

theorem perm_insertionSort (l : List α) : insertionSort r l ~ l := by
  induction l <;> grind [List.Perm, perm_orderedInsert]

@[simp]
theorem mem_insertionSort {l : List α} {x : α} : x ∈ l.insertionSort r ↔ x ∈ l :=
  (perm_insertionSort r l).mem_iff

@[simp]
theorem length_insertionSort (l : List α) : (insertionSort r l).length = l.length :=
  (perm_insertionSort r _).length_eq

theorem insertionSort_cons_of_forall_rel {a : α} {l : List α} (h : ∀ b ∈ l, r a b) :
    insertionSort r (a :: l) = a :: insertionSort r l := by
  rw [insertionSort_cons]
  cases hi : insertionSort r l with
  | nil => rfl
  | cons b m =>
    rw [orderedInsert_cons_of_le]
    apply h b <| (mem_insertionSort r).1 _
    rw [hi]
    exact mem_cons_self

theorem map_insertionSort (f : α → β) (l : List α) (hl : ∀ a ∈ l, ∀ b ∈ l, a ≼ b ↔ f a ≼ f b) :
    (l.insertionSort r).map f = (l.map f).insertionSort s := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp_rw [List.forall_mem_cons, forall_and] at hl
    simp_rw [List.map, insertionSort_cons]
    rw [List.map_orderedInsert _ s, ih hl.2.2]
    · simpa only [mem_insertionSort] using hl.2.1
    · simpa only [mem_insertionSort] using hl.1.2

variable {r}

/-- If `l` is already `List.Pairwise` with respect to `r`, then `insertionSort` does not change
it. -/
theorem Pairwise.insertionSort_eq {l : List α} : Pairwise r l → insertionSort r l = l := by
  induction l <;> grind [cases List]

/-- For a reflexive relation, insert then erasing is the identity. -/
theorem erase_orderedInsert [DecidableEq α] [Std.Refl r] (x : α) (xs : List α) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind [Std.Refl]

/-- Inserting then erasing an element that is absent is the identity. -/
theorem erase_orderedInsert_of_notMem [DecidableEq α]
    {x : α} {xs : List α} (hx : x ∉ xs) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind

/-- For an antisymmetric relation, erasing then inserting is the identity. -/
theorem orderedInsert_erase [DecidableEq α] [Std.Antisymm r] (x : α) (xs : List α) (hx : x ∈ xs)
    (hxs : Pairwise r xs) :
    (xs.erase x).orderedInsert r x = xs := by
  induction xs with grind +splitIndPred

theorem sublist_orderedInsert (x : α) (xs : List α) : xs <+ xs.orderedInsert r x := by
  induction xs <;> grind

theorem cons_sublist_orderedInsert {l c : List α} {a : α} (hl : c <+ l) (ha : ∀ a' ∈ c, a ≼ a') :
    a :: c <+ orderedInsert r a l := by
  induction l <;> grind

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
      · exact .cons_cons _ <| .cons _ ‹a :: as <+ bs›
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        simp only [hr, orderedInsert_cons, ite_true] at ih
        exact .trans ih <| .cons _ (.refl _)
      · have hba := pairwise_cons.mp hb |>.left _ (mem_of_cons_sublist ‹a :: as <+ bs›)
        exact absurd (trans_of _ ‹r x b› hba) hr
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        rw [orderedInsert_cons, if_neg hr] at ih
        exact .cons _ ih
      · simp_all
      · exact .cons_cons _ <| orderedInsert_sublist x ‹as <+ bs› hb.of_cons

section TotalAndTransitive

variable [Std.Total r] [IsTrans α r]

theorem Pairwise.orderedInsert (a : α) : ∀ l, Pairwise r l → Pairwise r (orderedInsert r a l)
  | [], _ => pairwise_singleton _ a
  | b :: l, h => by
    by_cases h' : a ≼ b
    · grind
    · suffices ∀ b' : α, b' ∈ List.orderedInsert r a l → r b b' by
        simpa [orderedInsert_cons, h', h.of_cons.orderedInsert a l]
      intro b' bm
      rcases (mem_orderedInsert r).mp bm with rfl | bm
      · exact (total_of r _ _).resolve_left h'
      · exact rel_of_pairwise_cons h bm

variable (r)

/-- The list `List.insertionSort r l` is `List.Pairwise` with respect to `r`. -/
theorem pairwise_insertionSort : ∀ l, Pairwise r (insertionSort r l)
  | [] => Pairwise.nil
  | a :: l => (pairwise_insertionSort l).orderedInsert a _

end TotalAndTransitive

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
If `c` is a sorted sublist of `l`, then `c` is still a sublist of `insertionSort r l`.
-/
theorem sublist_insertionSort {l c : List α} (hr : c.Pairwise r) (hc : c <+ l) :
    c <+ insertionSort r l := by
  induction l generalizing c with
  | nil         => grind
  | cons _ _ ih =>
    cases hc with
    | cons  _ h => exact ih hr h |>.trans (sublist_orderedInsert ..)
    | cons_cons _ h =>
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

variable [Std.Antisymm r] [Std.Total r] [IsTrans α r]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
A version of `insertionSort_stable` which only assumes `c <+~ l` (instead of `c <+ l`), but
additionally requires `Std.Antisymm r`, `Std.Total r` and `IsTrans α r`.
-/
theorem sublist_insertionSort' {l c : List α} (hs : c.Pairwise r) (hc : c <+~ l) :
    c <+ insertionSort r l := by
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil         => grind [nil_perm]
  | cons a _ ih =>
    cases hd with
    | cons  _ h => exact ih hs _ hc h |>.trans (sublist_orderedInsert ..)
    | cons_cons _ h =>
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

section Antisymm

variable {r : α → α → Prop} [Std.Antisymm r]

/-- Variant of `Perm.eq_of_pairwise` using relation typeclasses. -/
theorem Perm.eq_of_pairwise' {l₁ l₂ : List α} :
    Pairwise r l₁ → Pairwise r l₂ → (hl : l₁ ~ l₂) → l₁ = l₂ :=
  eq_of_pairwise (fun _ _ _ _ => antisymm)

theorem sublist_of_subperm_of_pairwise {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
    (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := hp
  exact Sublist.trans (h.eq_of_pairwise' (hs₂.sublist h') hs₁ ▸ Sublist.refl _) h'

theorem Subset.antisymm_of_pairwise [Std.Irrefl r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (hl₁₂ : l₁ ⊆ l₂) (hl₁₂' : l₂ ⊆ l₁) : l₁ = l₂ :=
  ((subperm_of_subset h₁.nodup hl₁₂).antisymm
    (subperm_of_subset h₂.nodup hl₁₂')).eq_of_pairwise' h₁ h₂

theorem Pairwise.eq_of_mem_iff [Std.Irrefl r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  Subset.antisymm_of_pairwise h₁ h₂ (by grind) (by grind)

end Antisymm

section TotalAndTransitive

variable {r} [Std.Total r] [IsTrans α r]

theorem Pairwise.merge {l l' : List α} (h : Pairwise r l) (h' : Pairwise r l') :
    Pairwise r (merge l l' (r · ·)) := by
  simpa using pairwise_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using Std.Total.total a b)
    l l' (by simpa using h) (by simpa using h')

@[deprecated (since := "2025-11-27")] alias Sorted.merge := Pairwise.merge

variable (r)

/-- Variant of `pairwise_mergeSort` using relation typeclasses. -/
theorem pairwise_mergeSort' (l : List α) : Pairwise r (mergeSort l (r · ·)) := by
  simpa using pairwise_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

@[deprecated (since := "2025-11-27")] alias sorted_mergeSort' := pairwise_mergeSort'

variable [Std.Antisymm r]

theorem mergeSort_eq_self {l : List α} : Pairwise r l → mergeSort l (r · ·) = l :=
  (mergeSort_perm _ _).eq_of_pairwise' (pairwise_mergeSort' _ l)

theorem mergeSort_eq_insertionSort (l : List α) :
    mergeSort l (r · ·) = insertionSort r l :=
  ((mergeSort_perm l _).trans (perm_insertionSort r l).symm).eq_of_pairwise'
    (pairwise_mergeSort' r l) (pairwise_insertionSort r l)

end TotalAndTransitive

end Correctness

end MergeSort

end sort

section Sorted

variable {α : Type*} {l : List α}

/-!
### The predicates `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`
-/

section Preorder

variable [Preorder α]

/-!
These predicates are equivalent to `Monotone l.get`, but they are also equivalent to
`IsChain (· < ·)` and `Pairwise (· < ·)`. API is provided to move between these forms.

API has deliberately not been provided for decomposed lists to avoid unneeded API replication.
The provided API should be used to move to and from `IsChain`,
`Pairwise` or `Monotone` as needed.
--/

/-- `l.SortedLE` means that the list is monotonic. -/
def SortedLE (l : List α) := Monotone l.get
/-- `l.SortedGE` means that the list is antitonic. -/
@[to_dual existing SortedLE] def SortedGE (l : List α) := Antitone l.get
/-- `l.SortedLT` means that the list is strictly monotonic. -/
def SortedLT (l : List α) := StrictMono l.get
/-- `l.SortedGT` means that the list is strictly antitonic. -/
@[to_dual existing SortedLT] def SortedGT (l : List α) := StrictAnti l.get

section Get

theorem sortedLE_iff_monotone_get : l.SortedLE ↔ Monotone l.get := .rfl
theorem sortedGE_iff_antitone_get : l.SortedGE ↔ Antitone l.get := .rfl
theorem sortedLT_iff_strictMono_get : l.SortedLT ↔ StrictMono l.get := .rfl
theorem sortedGT_iff_strictAnti_get : l.SortedGT ↔ StrictAnti l.get := .rfl

protected alias ⟨SortedLE.monotone_get, _root_.Monotone.sortedLE⟩ := sortedLE_iff_monotone_get
protected alias ⟨SortedGE.antitone_get, _root_.Antitone.sortedGE⟩ := sortedGE_iff_antitone_get
protected alias ⟨SortedLT.strictMono_get, _root_.StrictMono.sortedLT⟩ := sortedLT_iff_strictMono_get
protected alias ⟨SortedGT.strictAnti_get, _root_.StrictAnti.sortedGT⟩ := sortedGT_iff_strictAnti_get

end Get

section Pairwise

@[grind =] theorem sortedLE_iff_pairwise : l.SortedLE ↔ l.Pairwise (· ≤ ·) := by
  simp only [sortedLE_iff_monotone_get, monotone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
@[grind =] theorem sortedGE_iff_pairwise : l.SortedGE ↔ l.Pairwise (· ≥ ·) := by
  simp only [sortedGE_iff_antitone_get, antitone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
@[grind =] theorem sortedLT_iff_pairwise : l.SortedLT ↔ l.Pairwise (· < ·) := by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff]
  grind [pairwise_iff_getElem]
@[grind =] theorem sortedGT_iff_pairwise : l.SortedGT ↔ l.Pairwise (· > ·) := by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff]
  grind [pairwise_iff_getElem]

protected alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
protected alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
protected alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
protected alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise

end Pairwise

section IsChain

theorem sortedLE_iff_isChain : l.SortedLE ↔ IsChain (· ≤ ·) l :=
  sortedLE_iff_pairwise.trans isChain_iff_pairwise.symm
theorem sortedGE_iff_isChain : l.SortedGE ↔ IsChain (· ≥ ·) l :=
  sortedGE_iff_pairwise.trans isChain_iff_pairwise.symm
theorem sortedLT_iff_isChain : l.SortedLT ↔ IsChain (· < ·) l :=
  sortedLT_iff_pairwise.trans isChain_iff_pairwise.symm
theorem sortedGT_iff_isChain : l.SortedGT ↔ IsChain (· > ·) l :=
  sortedGT_iff_pairwise.trans isChain_iff_pairwise.symm

protected alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
protected alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
protected alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
protected alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

section Decidable

instance decidableSortedLE [DecidableLE α] : DecidablePred (SortedLE (α := α)) :=
  fun _ => decidable_of_iff' _ sortedLE_iff_isChain
instance decidableSortedGE [DecidableLE α] : DecidablePred (SortedGE (α := α)) :=
  fun _ => decidable_of_iff' _ sortedGE_iff_isChain
instance decidableSortedLT [DecidableLT α] : DecidablePred (SortedLT (α := α)) :=
  fun _ => decidable_of_iff' _ sortedLT_iff_isChain
instance decidableSortedGT [DecidableLT α] : DecidablePred (SortedGT (α := α)) :=
  fun _ => decidable_of_iff' _ sortedGT_iff_isChain

end Decidable

end IsChain

section GetElem

theorem sortedLE_iff_getElem_le_getElem_of_le :
    l.SortedLE ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i ≤ j → l[i] ≤ l[j] :=
  ⟨fun h _ _ _ _ hij => h.monotone_get hij, fun h => Monotone.sortedLE <| fun _ _ => (h ·)⟩
theorem sortedGE_iff_getElem_ge_getElem_of_le :
    l.SortedGE ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j ≤ i → l[i] ≤ l[j] :=
  ⟨fun h _ _ _ _ hij => h.antitone_get hij, fun h => Antitone.sortedGE <| fun _ _ => (h ·)⟩
theorem sortedLT_iff_getElem_lt_getElem_of_lt :
    l.SortedLT ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i < j → l[i] < l[j] :=
  ⟨fun h _ _ _ _ hij => h.strictMono_get hij, fun h => StrictMono.sortedLT <| fun _ _ => (h ·)⟩
theorem sortedGT_iff_getElem_gt_getElem_of_lt :
    l.SortedGT ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j < i → l[i] < l[j] :=
  ⟨fun h _ _ _ _ hij => h.strictAnti_get hij, fun h => StrictAnti.sortedGT <| fun _ _ => (h ·)⟩

alias ⟨SortedLE.getElem_le_getElem_of_le, sortedLE_of_getElem_le_getElem_of_le⟩ :=
  sortedLE_iff_getElem_le_getElem_of_le
alias ⟨SortedGE.getElem_ge_getElem_of_le, sortedGE_of_getElem_ge_getElem_of_le⟩ :=
  sortedGE_iff_getElem_ge_getElem_of_le
alias ⟨SortedLT.getElem_lt_getElem_of_lt, sortedLT_of_getElem_lt_getElem_of_lt⟩ :=
  sortedLT_iff_getElem_lt_getElem_of_lt
alias ⟨SortedGT.getElem_gt_getElem_of_lt, sortedGT_of_getElem_gt_getElem_of_lt⟩ :=
  sortedGT_iff_getElem_gt_getElem_of_lt

end GetElem

section

protected theorem SortedLT.sortedLE {l : List α} (h : l.SortedLT) : l.SortedLE :=
  h.strictMono_get.monotone.sortedLE
protected theorem SortedGT.sortedGE {l : List α} (h : l.SortedGT) : l.SortedGE :=
  h.strictAnti_get.antitone.sortedGE

@[deprecated (since := "2025-11-27")] alias Sorted.le_of_lt := SortedLT.sortedLE
@[deprecated (since := "2025-11-27")] alias Sorted.ge_of_gt := SortedGT.sortedGE

protected theorem SortedLT.nodup (h : l.SortedLT) : l.Nodup := h.strictMono_get.injective.nodup
protected theorem SortedGT.nodup (h : l.SortedGT) : l.Nodup := h.strictAnti_get.injective.nodup

theorem sortedLE_replicate {a : α} (n : ℕ) : (replicate n a).SortedLE :=
  (pairwise_replicate.mpr (Or.inr le_rfl)).sortedLE

@[deprecated (since := "2025-11-27")] alias sorted_le_replicate := sortedLE_replicate

theorem sortedLT_finRange (n : ℕ) : (finRange n).SortedLT :=
  sortedLT_of_getElem_lt_getElem_of_lt <| by simp

theorem sortedLT_range (n : ℕ) : (range n).SortedLT := pairwise_lt_range.sortedLT

@[deprecated (since := "2025-11-27")] alias sorted_lt_range := sortedLT_range

@[deprecated "use sortedLT_range.sortedLE" (since := "2025-11-27")]
theorem sorted_le_range (n) :
    (range n).SortedLE := (sortedLT_range n).sortedLE

theorem sortedLT_range' (a b) {s} (hs : s ≠ 0) :
    (range' a b s).SortedLT := (pairwise_lt_range' _ (Nat.pos_of_ne_zero hs)).sortedLT

@[deprecated (since := "2025-11-27")] alias sorted_lt_range' := sortedLT_range'

@[deprecated "use sortedLT_range'.sortedLE" (since := "2025-11-27")]
theorem sorted_le_range' (a b) {s} (hs : s ≠ 0) :
    (range' a b s).SortedLE := (sortedLT_range' a b hs).sortedLE

theorem sortedLE_range' (a b s) :
    (range' a b s).SortedLE := (pairwise_le_range' _).sortedLE

end

section OfFn

variable {n : ℕ} {f : Fin n → α}

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
@[simp] theorem sortedLE_ofFn_iff : (ofFn f).SortedLE ↔ Monotone f := by
  simp only [sortedLE_iff_monotone_get, Monotone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

/-- The list `List.ofFn f` is sorted with respect to `(· ≥ ·)` if and only if `f` is antitone. -/
@[simp] theorem sortedGE_ofFn_iff : (ofFn f).SortedGE ↔ Antitone f := by
  simp only [sortedGE_iff_antitone_get, Antitone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
@[simp] theorem sortedLT_ofFn_iff : (ofFn f).SortedLT ↔ StrictMono f := by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≥ ·)` if and only if `f` is
strictly antitone. -/
@[simp] theorem sortedGT_ofFn_iff : (ofFn f).SortedGT ↔ StrictAnti f := by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

@[deprecated (since := "2025-11-27")] alias sorted_le_ofFn_iff := sortedLE_ofFn_iff
@[deprecated (since := "2025-11-27")] alias sorted_lt_ofFn_iff := sortedLT_ofFn_iff
@[deprecated (since := "2025-11-27")] alias sorted_ge_ofFn_iff := sortedGE_ofFn_iff
@[deprecated (since := "2025-11-27")] alias sorted_gt_ofFn_iff := sortedGT_ofFn_iff

/-- The list obtained from a monotone tuple is sorted. -/
protected alias ⟨SortedLE.monotone, _root_.Monotone.sortedLE_ofFn⟩ := sortedLE_ofFn_iff
/-- The list obtained from an antitone tuple is sorted. -/
protected alias ⟨SortedGE.antitone, _root_.Antitone.sortedGE_ofFn⟩ := sortedGE_ofFn_iff
/-- The list obtained from a strictly monotone tuple is sorted. -/
protected alias ⟨SortedLT.strictMono, _root_.StrictMono.sortedLT_ofFn⟩ := sortedLT_ofFn_iff
/-- The list obtained from a strictly antitone tuple is sorted. -/
protected alias ⟨SortedGT.strictAnti, _root_.StrictAnti.sortedGT_ofFn⟩ := sortedGT_ofFn_iff

end OfFn

section Reverse

@[simp] theorem sortedLE_reverse : l.reverse.SortedLE ↔ l.SortedGE := by grind
@[simp] theorem sortedGE_reverse : l.reverse.SortedGE ↔ l.SortedLE := by grind
@[simp] theorem sortedLT_reverse : l.reverse.SortedLT ↔ l.SortedGT := by grind
@[simp] theorem sortedGT_reverse : l.reverse.SortedGT ↔ l.SortedLT := by grind

protected alias ⟨SortedLE.of_reverse, SortedGE.reverse⟩ := sortedLE_reverse
protected alias ⟨SortedGE.of_reverse, SortedLE.reverse⟩ := sortedGE_reverse
protected alias ⟨SortedLT.of_reverse, SortedGT.reverse⟩ := sortedLT_reverse
protected alias ⟨SortedGT.of_reverse, SortedLT.reverse⟩ := sortedGT_reverse

end Reverse

section Dual

section OfDual

variable {l : List αᵒᵈ}

@[simp] theorem sortedLE_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLE ↔ l.SortedGE := by
  grind [OrderDual.ofDual_le_ofDual]
@[simp] theorem sortedGE_map_ofDual :
    (l.map OrderDual.ofDual).SortedGE ↔ l.SortedLE := by
  grind [OrderDual.ofDual_le_ofDual]
@[simp] theorem sortedLT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLT ↔ l.SortedGT := by
  grind [OrderDual.ofDual_lt_ofDual]
@[simp] theorem sortedGT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedGT ↔ l.SortedLT := by
  grind [OrderDual.ofDual_lt_ofDual]

protected alias ⟨SortedLE.map_ofDual, SortedGE.of_map_ofDual⟩ := sortedLE_map_ofDual
protected alias ⟨SortedGE.map_ofDual, SortedLE.of_map_ofDual⟩ := sortedGE_map_ofDual
protected alias ⟨SortedLT.map_ofDual, SortedGT.of_map_ofDual⟩ := sortedLT_map_ofDual
protected alias ⟨SortedGT.map_ofDual, SortedLT.of_map_ofDual⟩ := sortedGT_map_ofDual

end OfDual

section ToDual

variable {l : List α}

theorem sortedLE_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedLE ↔ l.SortedGE := by
  grind [OrderDual.toDual_le_toDual]
theorem sortedGE_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedGE ↔ l.SortedLE := by
  grind [OrderDual.toDual_le_toDual]
theorem sortedLT_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedLT ↔ l.SortedGT := by
  grind [OrderDual.toDual_lt_toDual]
theorem sortedGT_map_toDual {l : List αᵒᵈ} :
    (l.map OrderDual.toDual).SortedGT ↔ l.SortedLT := by
  grind [OrderDual.toDual_lt_toDual]

protected alias ⟨SortedLE.map_toDual, SortedGE.of_map_toDual⟩ := sortedLE_map_toDual
protected alias ⟨SortedGE.map_toDual, SortedLE.of_map_toDual⟩ := sortedGE_map_toDual
protected alias ⟨SortedLT.map_toDual, SortedGT.of_map_toDual⟩ := sortedLT_map_toDual
protected alias ⟨SortedGT.map_toDual, SortedLT.of_map_toDual⟩ := sortedGT_map_toDual

end ToDual

end Dual

end Preorder

section PartialOrder

variable [PartialOrder α]

protected theorem SortedLE.sortedLT_of_nodup {l : List α} (h₁ : l.SortedLE) (h₂ : l.Nodup) :
    l.SortedLT := (h₁.monotone_get.strictMono_of_injective h₂.injective_get).sortedLT

protected theorem SortedGE.sortedGT_of_nodup {l : List α} (h₁ : l.SortedGE) (h₂ : l.Nodup) :
    l.SortedGT := (h₁.antitone_get.strictAnti_of_injective h₂.injective_get).sortedGT

@[deprecated (since := "2025-11-27")] alias Sorted.lt_of_le := SortedLE.sortedLT_of_nodup
@[deprecated (since := "2025-11-27")] alias Sorted.gt_of_ge := SortedGE.sortedGT_of_nodup

theorem sortedLT_iff_nodup_and_sortedLE : l.SortedLT ↔ l.Nodup ∧ l.SortedLE :=
  ⟨fun h => ⟨h.nodup, h.sortedLE⟩, fun h => h.2.sortedLT_of_nodup h.1⟩

theorem sortedGT_iff_nodup_and_sortedGE : l.SortedGT ↔ l.Nodup ∧ l.SortedGE :=
  ⟨fun h => ⟨h.nodup, h.sortedGE⟩, fun h => h.2.sortedGT_of_nodup h.1⟩

theorem Perm.eq_of_sortedLE {l₁ l₂ : List α} (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : (hl₁₂ : l₁ ~ l₂) → l₁ = l₂ :=
  Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

theorem Perm.eq_of_sortedGE {l₁ l₂ : List α} (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : (hl₁₂ : l₁ ~ l₂) → l₁ = l₂ :=
  Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

theorem Subset.antisymm_of_sortedLT {l₁ l₂ : List α} (hl₁₂ : l₁ ⊆ l₂) (hl₁₂' : l₂ ⊆ l₁)
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) : l₁ = l₂ :=
  hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

theorem Subset.antisymm_of_sortedGT {l₁ l₂ : List α} (hl₁₂ : l₁ ⊆ l₂) (hl₁₂' : l₂ ⊆ l₁)
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) : l₁ = l₂ :=
  hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

theorem SortedLT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) : (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise

theorem SortedGT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise h

theorem Perm.eq_reverse_of_sortedLE_of_sortedGE {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedGE) : l₁ = l₂.reverse :=
  (perm_reverse.mpr hp).eq_of_sortedLE hl₁ hl₂.reverse

theorem SortedLT.eq_reverse_of_mem_iff_of_sortedGT {l₁ l₂ : List α}
    (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) (hl₁ : l₁.SortedLT)
    (hl₂ : l₂.SortedGT) : l₁ = l₂.reverse := hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

theorem SortedGT.eq_reverse_of_mem_iff_of_sortedLT {l₁ l₂ : List α}
    (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) (hl₁ : l₁.SortedGT)
    (hl₂ : l₂.SortedLT) : l₁ = l₂.reverse :=
  hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

theorem sublist_of_subperm_of_sortedLE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

theorem sublist_of_subperm_of_sortedGE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem sortedLE_mergeSort : (l.mergeSort (· ≤ ·)).SortedLE :=
  (pairwise_mergeSort' _ _).sortedLE

theorem sortedGE_mergeSort : (l.mergeSort (· ≥ ·)).SortedGE :=
  (pairwise_mergeSort' _ _).sortedGE

theorem sortedLE_insertionSort : (l.insertionSort (· ≤ ·)).SortedLE :=
  (pairwise_insertionSort _ _).sortedLE

theorem sortedGE_insertionSort : (l.insertionSort (· ≥ ·)).SortedGE :=
  (pairwise_insertionSort _ _).sortedGE

@[simp]
theorem SortedLT.getElem_le_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] ≤ l[j] ↔ i ≤ j := hl.strictMono_get.le_iff_le

@[simp]
theorem SortedGT.getElem_le_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] ≤ l[j] ↔ j ≤ i := hl.strictAnti_get.le_iff_ge

@[simp]
theorem SortedLT.getElem_lt_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ i < j := hl.strictMono_get.lt_iff_lt

@[simp]
theorem SortedGT.getElem_lt_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ j < i := hl.strictAnti_get.lt_iff_gt

end LinearOrder

end Sorted

end List

namespace RelEmbedding

open List

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
theorem pairwise_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra := by
  simp [pairwise_map, e.map_rel_iff]

@[deprecated (since := "2025-11-27")] alias sorted_listMap := pairwise_listMap

@[simp]
theorem pairwise_swap_listMap (e : ra ↪r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) := by
  simp [pairwise_map, e.map_rel_iff]

@[deprecated (since := "2025-11-27")] alias sorted_swap_listMap := pairwise_swap_listMap

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

@[deprecated (since := "2025-11-27")] alias sorted_le_listMap := sortedLE_listMap
@[deprecated (since := "2025-11-27")] alias sorted_lt_listMap := sortedLT_listMap
@[deprecated (since := "2025-11-27")] alias sorted_ge_listMap := sortedGE_listMap
@[deprecated (since := "2025-11-27")] alias sorted_gt_listMap := sortedGT_listMap

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
  grind [hf.le_iff_ge]

theorem sortedGE_listMap (hf : StrictAnti f) :
    (l.map f).SortedGE ↔ l.SortedLE := by
  grind [hf.le_iff_ge]

theorem sortedLT_listMap (hf : StrictAnti f) :
    (l.map f).SortedLT ↔ l.SortedGT := by
  grind [hf.lt_iff_gt]

theorem sortedGT_listMap (hf : StrictAnti f) :
    (l.map f).SortedGT ↔ l.SortedLT := by
  grind [hf.lt_iff_gt]

end StrictAnti
