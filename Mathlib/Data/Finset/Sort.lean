/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.RelIso.Set
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

/-!
# Construct a sorted list from a finset.
-/


namespace Finset

open Multiset Nat

variable {α β : Type*}

/-! ### sort -/


section sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Finset α) : List α :=
  Multiset.sort r s.1

@[simp]
theorem sort_val (s : Finset α) : Multiset.sort r s.val = sort r s :=
  rfl

@[simp]
theorem sort_sorted (s : Finset α) : List.Sorted r (sort r s) :=
  Multiset.sort_sorted _ _

@[simp]
theorem sort_eq (s : Finset α) : ↑(sort r s) = s.1 :=
  Multiset.sort_eq _ _

@[simp]
theorem sort_nodup (s : Finset α) : (sort r s).Nodup :=
  (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort r s))

@[simp]
theorem sort_toFinset [DecidableEq α] (s : Finset α) : (sort r s).toFinset = s :=
  List.toFinset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)

@[simp]
theorem mem_sort {s : Finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
  Multiset.mem_sort _

@[simp]
theorem length_sort {s : Finset α} : (sort r s).length = s.card :=
  Multiset.length_sort _

@[simp]
theorem sort_empty : sort r ∅ = [] :=
  Multiset.sort_zero r

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  Multiset.sort_singleton r a

theorem sort_cons {a : α} {s : Finset α} (h₁ : ∀ b ∈ s, r a b) (h₂ : a ∉ s) :
    sort r (cons a s h₂) = a :: sort r s := by
  rw [sort, cons_val, Multiset.sort_cons r a _ h₁, sort_val]

theorem sort_insert [DecidableEq α] {a : α} {s : Finset α} (h₁ : ∀ b ∈ s, r a b) (h₂ : a ∉ s) :
    sort r (insert a s) = a :: sort r s := by
  rw [← cons_eq_insert _ _ h₂, sort_cons r h₁]

@[simp]
theorem sort_range (n : ℕ) : sort (· ≤ ·) (range n) = List.range n :=
  Multiset.sort_range n

open scoped List in
theorem sort_perm_toList (s : Finset α) : sort r s ~ s.toList := by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_toList, sort_eq]

theorem _root_.List.toFinset_sort [DecidableEq α] {l : List α} (hl : l.Nodup) :
    sort r l.toFinset = l ↔ l.Sorted r := by
  refine ⟨?_, List.eq_of_perm_of_sorted ((sort_perm_toList r _).trans (List.toFinset_toList hl))
    (sort_sorted r _)⟩
  intro h
  rw [← h]
  exact sort_sorted r _

end sort

section SortLinearOrder

variable [LinearOrder α]

theorem sort_sorted_lt (s : Finset α) : List.Sorted (· < ·) (sort (· ≤ ·) s) :=
  (sort_sorted _ _).lt_of_le (sort_nodup _ _)

theorem sort_sorted_gt (s : Finset α) : List.Sorted (· > ·) (sort (· ≥ ·) s) :=
  (sort_sorted _ _).gt_of_ge (sort_nodup _ _)

theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·)).get ⟨0, h⟩ = s.min' H := by
  let l := s.sort (· ≤ ·)
  apply le_antisymm
  · have : s.min' H ∈ l := (Finset.mem_sort (α := α) (· ≤ ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.sort_sorted (· ≤ ·)).rel_get_of_le (Nat.zero_le i)
  · have : l.get ⟨0, h⟩ ∈ s := (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l _)
    exact s.min'_le _ this

theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·))[0] = s.min' (card_pos.1 <| by rwa [length_sort] at h) :=
  sorted_zero_eq_min'_aux _ _ _

theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h = (s.sort (· ≤ ·))[0]'(by rw [length_sort]; exact card_pos.2 h) :=
  (sorted_zero_eq_min'_aux _ _ _).symm

theorem sorted_last_eq_max'_aux (s : Finset α)
    (h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·))[(s.sort (· ≤ ·)).length - 1] = s.max' H := by
  let l := s.sort (· ≤ ·)
  apply le_antisymm
  · have : l.get ⟨(s.sort (· ≤ ·)).length - 1, h⟩ ∈ s :=
      (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l _)
    exact s.le_max' _ this
  · have : s.max' H ∈ l := (Finset.mem_sort (α := α) (· ≤ ·)).mpr (s.max'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.max' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.sort_sorted (· ≤ ·)).rel_get_of_le (Nat.le_sub_one_of_lt i.prop)

theorem sorted_last_eq_max' {s : Finset α}
    {h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·))[(s.sort (· ≤ ·)).length - 1] =
      s.max' (by rw [length_sort] at h; exact card_pos.1 (lt_of_le_of_lt bot_le h)) :=
  sorted_last_eq_max'_aux _ h _

theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      (s.sort (· ≤ ·))[(s.sort (· ≤ ·)).length - 1]'
        (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) :=
  (sorted_last_eq_max'_aux _ (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) _).symm

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderIsoOfFin s h`
is the increasing bijection between `Fin k` and `s` as an `OrderIso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `Fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s :=
  OrderIso.trans (Fin.castOrderIso ((length_sort (α := α) (· ≤ ·)).trans h).symm) <|
    (s.sort_sorted_lt.getIso _).trans <| OrderIso.setCongr _ _ <| Set.ext fun _ => mem_sort _

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderEmbOfFin s h` is
the increasing bijection between `Fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `Fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]
theorem coe_orderIsoOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl

theorem orderIsoOfFin_symm_apply (s : Finset α) {k : ℕ} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = (s.sort (· ≤ ·)).indexOf ↑x :=
  rfl

theorem orderEmbOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i = (s.sort (· ≤ ·))[i]'(by rw [length_sort, h]; exact i.2) :=
  rfl

@[simp]
theorem orderEmbOfFin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2

@[simp]
theorem range_orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ → α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.subtype_apply, OrderIso.coe_toOrderEmbedding, eq_self_iff_true,
    Subtype.range_coe_subtype, Finset.setOf_mem, Finset.coe_inj]

/-- The bijection `orderEmbOfFin s h` sends `0` to the minimum of `s`. -/
theorem orderEmbOfFin_zero {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [orderEmbOfFin_apply, Fin.getElem_fin, sorted_zero_eq_min']

/-- The bijection `orderEmbOfFin s h` sends `k-1` to the maximum of `s`. -/
theorem orderEmbOfFin_last {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ =
      s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]

/-- `orderEmbOfFin {a} h` sends any argument to `a`. -/
@[simp]
theorem orderEmbOfFin_singleton (a : α) (i : Fin 1) :
    orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elim i ⟨0, Nat.zero_lt_one⟩, orderEmbOfFin_zero _ Nat.zero_lt_one,
    min'_singleton]

/-- Any increasing map `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α}
    (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h := by
  rw [← hmono.range_inj (s.orderEmbOfFin h).strictMono, range_orderEmbOfFin, ← Set.image_univ,
    ← coe_univ, ← coe_image, coe_inj]
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]

/-- An order embedding `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
theorem orderEmbOfFin_unique' {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k ↪o α}
    (hfs : ∀ x, f x ∈ s) : f = s.orderEmbOfFin h :=
  RelEmbedding.ext <| funext_iff.1 <| orderEmbOfFin_unique h hfs f.strictMono

/-- Two parametrizations `orderEmbOfFin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `Fin k` and `Fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
theorem orderEmbOfFin_eq_orderEmbOfFin_iff {k l : ℕ} {s : Finset α} {i : Fin k} {j : Fin l}
    {h : s.card = k} {h' : s.card = l} :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : ℕ) = (j : ℕ) := by
  substs k l
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `orderEmbOfCardLe`
is an order embedding from `Fin k` to `α` whose image is contained in `s`. Specifically, it maps
`Fin k` to an initial segment of `s`. -/
def orderEmbOfCardLe (s : Finset α) {k : ℕ} (h : k ≤ s.card) : Fin k ↪o α :=
  (Fin.castLEOrderEmb h).trans (s.orderEmbOfFin rfl)

theorem orderEmbOfCardLe_mem (s : Finset α) {k : ℕ} (h : k ≤ s.card) (a) :
    orderEmbOfCardLe s h a ∈ s := by
  simp only [orderEmbOfCardLe, RelEmbedding.coe_trans, Finset.orderEmbOfFin_mem,
    Function.comp_apply]

end SortLinearOrder

unsafe instance [Repr α] : Repr (Finset α) where
  reprPrec s _ :=
    -- multiset uses `0` not `∅` for empty sets
    if s.card = 0 then "∅" else repr s.1

end Finset

namespace Fin

theorem sort_univ (n : ℕ) : Finset.univ.sort (fun x y : Fin n => x ≤ y) = List.finRange n :=
  List.eq_of_perm_of_sorted
    (List.perm_of_nodup_nodup_toFinset_eq
      (Finset.univ.sort_nodup _) (List.nodup_finRange n) (by simp))
    (Finset.univ.sort_sorted LE.le)
    (List.pairwise_le_finRange n)

end Fin

/-- Given a `Fintype` `α` of cardinality `k`, the map `orderIsoFinOfCardEq s h` is the increasing
bijection between `Fin k` and `α` as an `OrderIso`. Here, `h` is a proof that the cardinality of `α`
is `k`. We use this instead of an iso `Fin (Fintype.card α) ≃o α` to avoid casting issues in further
uses of this function. -/
def Fintype.orderIsoFinOfCardEq
    (α : Type*) [LinearOrder α] [Fintype α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (Finset.univ.orderIsoOfFin h).trans
    ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)

/-- Any finite linear order order-embeds into any infinite linear order. -/
lemma nonempty_orderEmbedding_of_finite_infinite
    (α : Type*) [LinearOrder α] [hα : Finite α]
    (β : Type*) [LinearOrder β] [hβ : Infinite β] : Nonempty (α ↪o β) := by
  haveI := Fintype.ofFinite α
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq β (Fintype.card α)
  exact ⟨((Fintype.orderIsoFinOfCardEq α rfl).symm.toOrderEmbedding).trans (s.orderEmbOfFin hs)⟩
