/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Batteries.Data.List.Perm
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeWhile
import Mathlib.Order.Fin.Basic

/-!
# Sorting algorithms on lists

In this file we define `List.Sorted r l` to be an alias for `List.Pairwise r l`.
This alias is preferred in the case that `r` is a `<` or `≤`-like relation.
Then we define the sorting algorithm
`List.insertionSort` and prove its correctness.
-/

open List.Perm

universe u v

namespace List

/-!
### The predicate `List.Sorted`
-/

section Sorted

variable {α : Type u} {r : α → α → Prop} {a : α} {l : List α}

/-- `Sorted r l` is the same as `List.Pairwise r l`, preferred in the case that `r`
  is a `<` or `≤`-like relation (transitive and antisymmetric or asymmetric) -/
def Sorted :=
  @Pairwise

instance decidableSorted [DecidableRel r] (l : List α) : Decidable (Sorted r l) :=
  List.instDecidablePairwise _

protected theorem Sorted.le_of_lt [Preorder α] {l : List α} (h : l.Sorted (· < ·)) :
    l.Sorted (· ≤ ·) :=
  h.imp le_of_lt

protected theorem Sorted.lt_of_le [PartialOrder α] {l : List α} (h₁ : l.Sorted (· ≤ ·))
    (h₂ : l.Nodup) : l.Sorted (· < ·) :=
  h₁.imp₂ (fun _ _ => lt_of_le_of_ne) h₂

protected theorem Sorted.ge_of_gt [Preorder α] {l : List α} (h : l.Sorted (· > ·)) :
    l.Sorted (· ≥ ·) :=
  h.imp le_of_lt

protected theorem Sorted.gt_of_ge [PartialOrder α] {l : List α} (h₁ : l.Sorted (· ≥ ·))
    (h₂ : l.Nodup) : l.Sorted (· > ·) :=
  h₁.imp₂ (fun _ _ => lt_of_le_of_ne) <| by simp_rw [ne_comm]; exact h₂

@[simp]
theorem sorted_nil : Sorted r [] :=
  Pairwise.nil

theorem Sorted.of_cons : Sorted r (a :: l) → Sorted r l :=
  Pairwise.of_cons

theorem Sorted.tail {r : α → α → Prop} {l : List α} (h : Sorted r l) : Sorted r l.tail :=
  Pairwise.tail h

theorem rel_of_sorted_cons {a : α} {l : List α} : Sorted r (a :: l) → ∀ b ∈ l, r a b :=
  rel_of_pairwise_cons

nonrec theorem Sorted.cons {r : α → α → Prop} [IsTrans α r] {l : List α} {a b : α}
    (hab : r a b) (h : Sorted r (b :: l)) : Sorted r (a :: b :: l) :=
  h.cons <| forall_mem_cons.2 ⟨hab, fun _ hx => _root_.trans hab <| rel_of_sorted_cons h _ hx⟩

theorem sorted_cons_cons {r : α → α → Prop} [IsTrans α r] {l : List α} {a b : α} :
    Sorted r (b :: a :: l) ↔ r b a ∧ Sorted r (a :: l) := by
  constructor
  · intro h
    exact ⟨rel_of_sorted_cons h _ mem_cons_self, h.of_cons⟩
  · rintro ⟨h, ha⟩
    exact ha.cons h

theorem Sorted.head!_le [Inhabited α] [Preorder α] {a : α} {l : List α} (h : Sorted (· < ·) l)
    (ha : a ∈ l) : l.head! ≤ a := by
  rw [← List.cons_head!_tail (List.ne_nil_of_mem ha)] at h ha
  cases ha
  · exact le_rfl
  · exact le_of_lt (rel_of_sorted_cons h a (by assumption))

theorem Sorted.le_head! [Inhabited α] [Preorder α] {a : α} {l : List α} (h : Sorted (· > ·) l)
    (ha : a ∈ l) : a ≤ l.head! := by
  rw [← List.cons_head!_tail (List.ne_nil_of_mem ha)] at h ha
  cases ha
  · exact le_rfl
  · exact le_of_lt (rel_of_sorted_cons h a (by assumption))

@[simp]
theorem sorted_cons {a : α} {l : List α} : Sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ Sorted r l :=
  pairwise_cons

protected theorem Sorted.nodup {r : α → α → Prop} [IsIrrefl α r] {l : List α} (h : Sorted r l) :
    Nodup l :=
  Pairwise.nodup h

protected theorem Sorted.filter {l : List α} (f : α → Bool) (h : Sorted r l) :
    Sorted r (filter f l) :=
  h.sublist filter_sublist

theorem eq_of_perm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hs₁ : Sorted r l₁)
    (hs₂ : Sorted r l₂) : l₁ = l₂ := by
  induction hs₁ generalizing l₂ with
  | nil => exact hp.nil_eq
  | @cons a l₁ h₁ hs₁ IH =>
    have : a ∈ l₂ := hp.subset mem_cons_self
    rcases append_of_mem this with ⟨u₂, v₂, rfl⟩
    have hp' := (perm_cons a).1 (hp.trans perm_middle)
    obtain rfl := IH hp' (hs₂.sublist <| by simp)
    change a :: u₂ ++ v₂ = u₂ ++ ([a] ++ v₂)
    rw [← append_assoc]
    congr
    have : ∀ x ∈ u₂, x = a := fun x m =>
      antisymm ((pairwise_append.1 hs₂).2.2 _ m a mem_cons_self) (h₁ _ (by simp [m]))
    rw [(@eq_replicate_iff _ a (length u₂ + 1) (a :: u₂)).2,
        (@eq_replicate_iff _ a (length u₂ + 1) (u₂ ++ [a])).2] <;>
        constructor <;>
      simp [iff_true_intro this, or_comm]

theorem Sorted.eq_of_mem_iff [IsAntisymm α r] [IsIrrefl α r] {l₁ l₂ : List α}
    (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  eq_of_perm_of_sorted ((perm_ext_iff_of_nodup h₁.nodup h₂.nodup).2 h) h₁ h₂

theorem sublist_of_subperm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
    (hs₁ : l₁.Sorted r) (hs₂ : l₂.Sorted r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := hp
  rwa [← eq_of_perm_of_sorted h (hs₂.sublist h') hs₁]

@[simp 1100] -- Higher priority shortcut lemma.
theorem sorted_singleton (a : α) : Sorted r [a] := by
  simp

theorem sorted_lt_range (n : ℕ) : Sorted (· < ·) (range n) := by
  rw [Sorted, pairwise_iff_get]
  simp

theorem sorted_replicate (n : ℕ) (a : α) : Sorted r (replicate n a) ↔ n ≤ 1 ∨ r a a :=
  pairwise_replicate

theorem sorted_le_replicate (n : ℕ) (a : α) [Preorder α] : Sorted (· ≤ ·) (replicate n a) := by
  simp [sorted_replicate]

theorem sorted_le_range (n : ℕ) : Sorted (· ≤ ·) (range n) :=
  (sorted_lt_range n).le_of_lt

lemma sorted_lt_range' (a b) {s} (hs : s ≠ 0) :
    Sorted (· < ·) (range' a b s) := by
  induction b generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ]
    refine List.sorted_cons.mpr ⟨fun b hb ↦ ?_, @ih (a + s)⟩
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_of_ne_zero hs))
      (List.left_le_of_mem_range' hb)

lemma sorted_le_range' (a b s) :
    Sorted (· ≤ ·) (range' a b s) := by
  by_cases hs : s ≠ 0
  · exact (sorted_lt_range' a b hs).le_of_lt
  · rw [ne_eq, Decidable.not_not] at hs
    simpa [hs] using sorted_le_replicate b a

theorem Sorted.rel_get_of_lt {l : List α} (h : l.Sorted r) {a b : Fin l.length} (hab : a < b) :
    r (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab

theorem Sorted.rel_get_of_le [IsRefl α r] {l : List α} (h : l.Sorted r) {a b : Fin l.length}
    (hab : a ≤ b) : r (l.get a) (l.get b) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, h.rel_get_of_lt hlt]

theorem Sorted.rel_of_mem_take_of_mem_drop {l : List α} (h : List.Sorted r l) {k : ℕ} {x y : α}
    (hx : x ∈ List.take k l) (hy : y ∈ List.drop k l) : r x y := by
  obtain ⟨iy, hiy, rfl⟩ := getElem_of_mem hy
  obtain ⟨ix, hix, rfl⟩ := getElem_of_mem hx
  rw [getElem_take, getElem_drop]
  rw [length_take] at hix
  exact h.rel_get_of_lt (Nat.lt_add_right _ (Nat.lt_min.mp hix).left)

/--
If a list is sorted with respect to a decidable relation,
then it is sorted with respect to the corresponding Bool-valued relation.
-/
theorem Sorted.decide [DecidableRel r] (l : List α) (h : Sorted r l) :
    Sorted (fun a b => decide (r a b) = true) l := by
  refine h.imp fun {a b} h => by simpa using h

end Sorted

section Monotone

variable {n : ℕ} {α : Type u} {f : Fin n → α}

open scoped Relator in
theorem sorted_ofFn_iff {r : α → α → Prop} : (ofFn f).Sorted r ↔ ((· < ·) ⇒ r) f f := by
  simp_rw [Sorted, pairwise_iff_get, get_ofFn, Relator.LiftFun]
  exact Iff.symm (Fin.rightInverse_cast _).surjective.forall₂

variable [Preorder α]

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
@[simp] theorem sorted_lt_ofFn_iff : (ofFn f).Sorted (· < ·) ↔ StrictMono f := sorted_ofFn_iff

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≥ ·)` if and only if `f` is
strictly antitone. -/
@[simp] theorem sorted_gt_ofFn_iff : (ofFn f).Sorted (· > ·) ↔ StrictAnti f := sorted_ofFn_iff

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
@[simp] theorem sorted_le_ofFn_iff : (ofFn f).Sorted (· ≤ ·) ↔ Monotone f :=
  sorted_ofFn_iff.trans monotone_iff_forall_lt.symm

/-- The list obtained from a monotone tuple is sorted. -/
alias ⟨_, _root_.Monotone.ofFn_sorted⟩ := sorted_le_ofFn_iff

/-- The list `List.ofFn f` is sorted with respect to `(· ≥ ·)` if and only if `f` is antitone. -/
@[simp] theorem sorted_ge_ofFn_iff : (ofFn f).Sorted (· ≥ ·) ↔ Antitone f :=
  sorted_ofFn_iff.trans antitone_iff_forall_lt.symm

/-- The list obtained from an antitone tuple is sorted. -/
alias ⟨_, _root_.Antitone.ofFn_sorted⟩ := sorted_ge_ofFn_iff

end Monotone

lemma Sorted.filterMap {α β : Type*} {p : α → Option β} {l : List α}
    {r : α → α → Prop} {r' : β → β → Prop} (hl : l.Sorted r)
    (hp : ∀ (a b : α) (c d : β), p a = some c → p b = some d → r a b → r' c d) :
    (l.filterMap p).Sorted r' := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filterMap_cons]
    cases ha : p a with
    | none =>
      exact ih (List.sorted_cons.mp hl).right
    | some b =>
      rw [List.sorted_cons]
      refine ⟨fun x hx ↦ ?_, ih (List.sorted_cons.mp hl).right⟩
      obtain ⟨u, hu, hu'⟩ := List.mem_filterMap.mp hx
      exact hp a u b x ha hu' <| (List.sorted_cons.mp hl).left u hu

end List

open List

namespace RelEmbedding

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
theorem sorted_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Sorted rb ↔ l.Sorted ra := by
  simp [Sorted, pairwise_map, e.map_rel_iff]

@[simp]
theorem sorted_swap_listMap (e : ra ↪r rb) {l : List α} :
    (l.map e).Sorted (Function.swap rb) ↔ l.Sorted (Function.swap ra) := by
  simp [Sorted, pairwise_map, e.map_rel_iff]

end RelEmbedding

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem sorted_lt_listMap (e : α ↪o β) {l : List α} :
    (l.map e).Sorted (· < ·) ↔ l.Sorted (· < ·) :=
  e.ltEmbedding.sorted_listMap

@[simp]
theorem sorted_gt_listMap (e : α ↪o β) {l : List α} :
    (l.map e).Sorted (· > ·) ↔ l.Sorted (· > ·) :=
  e.ltEmbedding.sorted_swap_listMap

end OrderEmbedding

namespace RelIso

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
theorem sorted_listMap (e : ra ≃r rb) {l : List α} : (l.map e).Sorted rb ↔ l.Sorted ra :=
  e.toRelEmbedding.sorted_listMap

@[simp]
theorem sorted_swap_listMap (e : ra ≃r rb) {l : List α} :
    (l.map e).Sorted (Function.swap rb) ↔ l.Sorted (Function.swap ra) :=
  e.toRelEmbedding.sorted_swap_listMap

end RelIso

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem sorted_lt_listMap (e : α ≃o β) {l : List α} :
    (l.map e).Sorted (· < ·) ↔ l.Sorted (· < ·) :=
  e.toOrderEmbedding.sorted_lt_listMap

@[simp]
theorem sorted_gt_listMap (e : α ≃o β) {l : List α} :
    (l.map e).Sorted (· > ·) ↔ l.Sorted (· > ·) :=
  e.toOrderEmbedding.sorted_gt_listMap

end OrderIso

namespace StrictMono

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

theorem sorted_le_listMap (hf : StrictMono f) :
    (l.map f).Sorted (· ≤ ·) ↔ l.Sorted (· ≤ ·) :=
  (OrderEmbedding.ofStrictMono f hf).sorted_listMap

theorem sorted_ge_listMap (hf : StrictMono f) :
    (l.map f).Sorted (· ≥ ·) ↔ l.Sorted (· ≥ ·) :=
  (OrderEmbedding.ofStrictMono f hf).sorted_swap_listMap

theorem sorted_lt_listMap (hf : StrictMono f) :
    (l.map f).Sorted (· < ·) ↔ l.Sorted (· < ·) :=
  (OrderEmbedding.ofStrictMono f hf).sorted_lt_listMap

theorem sorted_gt_listMap (hf : StrictMono f) :
    (l.map f).Sorted (· > ·) ↔ l.Sorted (· > ·) :=
  (OrderEmbedding.ofStrictMono f hf).sorted_gt_listMap

end StrictMono

namespace StrictAnti

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

theorem sorted_le_listMap (hf : StrictAnti f) :
    (l.map f).Sorted (· ≤ ·) ↔ l.Sorted (· ≥ ·) :=
  hf.dual_right.sorted_ge_listMap

theorem sorted_ge_listMap (hf : StrictAnti f) :
    (l.map f).Sorted (· ≥ ·) ↔ l.Sorted (· ≤ ·) :=
  hf.dual_right.sorted_le_listMap

theorem sorted_lt_listMap (hf : StrictAnti f) :
    (l.map f).Sorted (· < ·) ↔ l.Sorted (· > ·) :=
  hf.dual_right.sorted_gt_listMap

theorem sorted_gt_listMap (hf : StrictAnti f) :
    (l.map f).Sorted (· > ·) ↔ l.Sorted (· < ·) :=
  hf.dual_right.sorted_lt_listMap

end StrictAnti

namespace List

section sort

variable {α : Type u} {β : Type v} (r : α → α → Prop) (s : β → β → Prop)
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
    · simp [orderedInsert]
    · rw [mem_cons, mem_cons, mem_orderedInsert, or_left_comm]

theorem map_orderedInsert (f : α → β) (l : List α) (x : α)
    (hl₁ : ∀ a ∈ l, a ≼ x ↔ f a ≼ f x) (hl₂ : ∀ a ∈ l, x ≼ a ↔ f x ≼ f a) :
    (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.forall_mem_cons] at hl₁ hl₂
    simp only [List.map, List.orderedInsert, ← hl₁.1, ← hl₂.1]
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

/-- If `l` is already `List.Sorted` with respect to `r`, then `insertionSort` does not change
it. -/
theorem Sorted.insertionSort_eq : ∀ {l : List α}, Sorted r l → insertionSort r l = l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [insertionSort, Sorted.insertionSort_eq, orderedInsert, if_pos]
    exacts [rel_of_sorted_cons h _ mem_cons_self, h.tail]

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
    (hxs : Sorted r xs) :
    (xs.erase x).orderedInsert r x = xs := by
  induction xs generalizing x with
  | nil => cases hx
  | cons y ys ih =>
    rw [sorted_cons] at hxs
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

theorem Sublist.orderedInsert_sublist [IsTrans α r] {as bs} (x) (hs : as <+ bs) (hb : bs.Sorted r) :
    orderedInsert r x as <+ orderedInsert r x bs := by
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
      · simp_all only [sorted_cons, cons_sublist_cons]
      · exact .cons₂ _ <| orderedInsert_sublist x ‹as <+ bs› hb.of_cons

section TotalAndTransitive

variable [IsTotal α r] [IsTrans α r]

theorem Sorted.orderedInsert (a : α) : ∀ l, Sorted r l → Sorted r (orderedInsert r a l)
  | [], _ => sorted_singleton a
  | b :: l, h => by
    by_cases h' : a ≼ b
    · simpa [orderedInsert, h', h] using fun b' bm => _root_.trans h' (rel_of_sorted_cons h _ bm)
    · suffices ∀ b' : α, b' ∈ List.orderedInsert r a l → r b b' by
        simpa [orderedInsert, h', h.of_cons.orderedInsert a l]
      intro b' bm
      rcases (mem_orderedInsert r).mp bm with be | bm
      · subst b'
        exact (total_of r _ _).resolve_left h'
      · exact rel_of_sorted_cons h _ bm

variable (r)

/-- The list `List.insertionSort r l` is `List.Sorted` with respect to `r`. -/
theorem sorted_insertionSort : ∀ l, Sorted r (insertionSort r l)
  | [] => sorted_nil
  | a :: l => (sorted_insertionSort l).orderedInsert a _

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
theorem sublist_insertionSort' {l c : List α} (hs : c.Sorted r) (hc : c <+~ l) :
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
      exact he ▸ Sublist.orderedInsert_sublist _ ih (sorted_insertionSort ..)

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

section TotalAndTransitive

variable {r} [IsTotal α r] [IsTrans α r]

theorem Sorted.merge {l l' : List α} (h : Sorted r l) (h' : Sorted r l') :
    Sorted r (merge l l' (r · ·)) := by
  simpa using sorted_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using IsTotal.total a b)
    l l' (by simpa using h) (by simpa using h')

variable (r)

/-- Variant of `sorted_mergeSort` using relation typeclasses. -/
theorem sorted_mergeSort' (l : List α) : Sorted r (mergeSort l (r · ·)) := by
  simpa using sorted_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

variable [IsAntisymm α r]

theorem mergeSort_eq_self {l : List α} : Sorted r l → mergeSort l (r · ·) = l :=
  eq_of_perm_of_sorted (mergeSort_perm _ _) (sorted_mergeSort' _ l)

theorem mergeSort_eq_insertionSort (l : List α) :
    mergeSort l (r · ·) = insertionSort r l :=
  eq_of_perm_of_sorted ((mergeSort_perm l _).trans (perm_insertionSort r l).symm)
    (sorted_mergeSort' r l) (sorted_insertionSort r l)

end TotalAndTransitive

end Correctness

end MergeSort

end sort

end List
