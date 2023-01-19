/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.finset.sort
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.RelIso.Set
import Mathbin.Data.Fintype.Lattice
import Mathbin.Data.Multiset.Sort
import Mathbin.Data.List.NodupEquivFin

/-!
# Construct a sorted list from a finset.
-/


namespace Finset

open Multiset Nat

variable {α β : Type _}

/-! ### sort -/


section Sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Finset α) : List α :=
  sort r s.1
#align finset.sort Finset.sort

@[simp]
theorem sort_sorted (s : Finset α) : List.Sorted r (sort r s) :=
  sort_sorted _ _
#align finset.sort_sorted Finset.sort_sorted

@[simp]
theorem sort_eq (s : Finset α) : ↑(sort r s) = s.1 :=
  sort_eq _ _
#align finset.sort_eq Finset.sort_eq

@[simp]
theorem sort_nodup (s : Finset α) : (sort r s).Nodup :=
  (by rw [sort_eq] <;> exact s.2 : @Multiset.Nodup α (sort r s))
#align finset.sort_nodup Finset.sort_nodup

@[simp]
theorem sort_to_finset [DecidableEq α] (s : Finset α) : (sort r s).toFinset = s :=
  List.toFinset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)
#align finset.sort_to_finset Finset.sort_to_finset

@[simp]
theorem mem_sort {s : Finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
  Multiset.mem_sort _
#align finset.mem_sort Finset.mem_sort

@[simp]
theorem length_sort {s : Finset α} : (sort r s).length = s.card :=
  Multiset.length_sort _
#align finset.length_sort Finset.length_sort

@[simp]
theorem sort_empty : sort r ∅ = [] :=
  Multiset.sort_zero r
#align finset.sort_empty Finset.sort_empty

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  Multiset.sort_singleton r a
#align finset.sort_singleton Finset.sort_singleton

theorem sort_perm_to_list (s : Finset α) : sort r s ~ s.toList :=
  by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_to_list, sort_eq]
#align finset.sort_perm_to_list Finset.sort_perm_to_list

end Sort

section SortLinearOrder

variable [LinearOrder α]

theorem sort_sorted_lt (s : Finset α) : List.Sorted (· < ·) (sort (· ≤ ·) s) :=
  (sort_sorted _ _).imp₂ (@lt_of_le_of_ne _ _) (sort_nodup _ _)
#align finset.sort_sorted_lt Finset.sort_sorted_lt

theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·)).nthLe 0 h = s.min' H :=
  by
  let l := s.sort (· ≤ ·)
  apply le_antisymm
  · have : s.min' H ∈ l := (Finset.mem_sort (· ≤ ·)).mpr (s.min'_mem H)
    obtain ⟨i, i_lt, hi⟩ : ∃ (i : _)(hi : i < l.length), l.nth_le i hi = s.min' H :=
      List.mem_iff_nthLe.1 this
    rw [← hi]
    exact (s.sort_sorted (· ≤ ·)).rel_nth_le_of_le _ _ (Nat.zero_le i)
  · have : l.nth_le 0 h ∈ s := (Finset.mem_sort (· ≤ ·)).1 (List.nthLe_mem l 0 h)
    exact s.min'_le _ this
#align finset.sorted_zero_eq_min'_aux Finset.sorted_zero_eq_min'_aux

theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·)).nthLe 0 h = s.min' (card_pos.1 <| by rwa [length_sort] at h) :=
  sorted_zero_eq_min'_aux _ _ _
#align finset.sorted_zero_eq_min' Finset.sorted_zero_eq_min'

theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h =
      (s.sort (· ≤ ·)).nthLe 0
        (by
          rw [length_sort]
          exact card_pos.2 h) :=
  (sorted_zero_eq_min'_aux _ _ _).symm
#align finset.min'_eq_sorted_zero Finset.min'_eq_sorted_zero

theorem sorted_last_eq_max'_aux (s : Finset α)
    (h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1) h = s.max' H :=
  by
  let l := s.sort (· ≤ ·)
  apply le_antisymm
  · have : l.nth_le ((s.sort (· ≤ ·)).length - 1) h ∈ s :=
      (Finset.mem_sort (· ≤ ·)).1 (List.nthLe_mem l _ h)
    exact s.le_max' _ this
  · have : s.max' H ∈ l := (Finset.mem_sort (· ≤ ·)).mpr (s.max'_mem H)
    obtain ⟨i, i_lt, hi⟩ : ∃ (i : _)(hi : i < l.length), l.nth_le i hi = s.max' H :=
      List.mem_iff_nthLe.1 this
    rw [← hi]
    have : i ≤ l.length - 1 := Nat.le_pred_of_lt i_lt
    exact (s.sort_sorted (· ≤ ·)).rel_nth_le_of_le _ _ (Nat.le_pred_of_lt i_lt)
#align finset.sorted_last_eq_max'_aux Finset.sorted_last_eq_max'_aux

theorem sorted_last_eq_max' {s : Finset α}
    {h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1) h =
      s.max'
        (by
          rw [length_sort] at h
          exact card_pos.1 (lt_of_le_of_lt bot_le h)) :=
  sorted_last_eq_max'_aux _ _ _
#align finset.sorted_last_eq_max' Finset.sorted_last_eq_max'

theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1)
        (by simpa using Nat.sub_lt (card_pos.mpr h) zero_lt_one) :=
  (sorted_last_eq_max'_aux _ _ _).symm
#align finset.max'_eq_sorted_last Finset.max'_eq_sorted_last

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_iso_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `order_iso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s :=
  OrderIso.trans (Fin.cast ((length_sort (· ≤ ·)).trans h).symm) <|
    (s.sort_sorted_lt.nthLeIso _).trans <| OrderIso.setCongr _ _ <| Set.ext fun x => mem_sort _
#align finset.order_iso_of_fin Finset.orderIsoOfFin

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_emb_of_fin s h` is
the increasing bijection between `fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)
#align finset.order_emb_of_fin Finset.orderEmbOfFin

@[simp]
theorem coe_order_iso_of_fin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl
#align finset.coe_order_iso_of_fin_apply Finset.coe_order_iso_of_fin_apply

theorem order_iso_of_fin_symm_apply (s : Finset α) {k : ℕ} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = (s.sort (· ≤ ·)).indexOf x :=
  rfl
#align finset.order_iso_of_fin_symm_apply Finset.order_iso_of_fin_symm_apply

theorem order_emb_of_fin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i =
      (s.sort (· ≤ ·)).nthLe i
        (by
          rw [length_sort, h]
          exact i.2) :=
  rfl
#align finset.order_emb_of_fin_apply Finset.order_emb_of_fin_apply

@[simp]
theorem order_emb_of_fin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2
#align finset.order_emb_of_fin_mem Finset.order_emb_of_fin_mem

@[simp]
theorem range_order_emb_of_fin (s : Finset α) {k : ℕ} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp only [order_emb_of_fin, Set.range_comp coe (s.order_iso_of_fin h), RelEmbedding.coe_trans,
    Set.image_univ, Finset.orderEmbOfFin.equations._eqn_1, RelIso.range_eq,
    OrderEmbedding.subtype_apply, OrderIso.coe_toOrderEmbedding, eq_self_iff_true,
    Subtype.range_coe_subtype, Finset.setOf_mem, Finset.coe_inj]
#align finset.range_order_emb_of_fin Finset.range_order_emb_of_fin

/-- The bijection `order_emb_of_fin s h` sends `0` to the minimum of `s`. -/
theorem order_emb_of_fin_zero {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [order_emb_of_fin_apply, Fin.val_mk, sorted_zero_eq_min']
#align finset.order_emb_of_fin_zero Finset.order_emb_of_fin_zero

/-- The bijection `order_emb_of_fin s h` sends `k-1` to the maximum of `s`. -/
theorem order_emb_of_fin_last {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Buffer.lt_aux_2 hz⟩ = s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [order_emb_of_fin_apply, max'_eq_sorted_last, h]
#align finset.order_emb_of_fin_last Finset.order_emb_of_fin_last

/-- `order_emb_of_fin {a} h` sends any argument to `a`. -/
@[simp]
theorem order_emb_of_fin_singleton (a : α) (i : Fin 1) :
    orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elim i ⟨0, zero_lt_one⟩, order_emb_of_fin_zero _ zero_lt_one, min'_singleton]
#align finset.order_emb_of_fin_singleton Finset.order_emb_of_fin_singleton

/-- Any increasing map `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
theorem order_emb_of_fin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α}
    (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h :=
  by
  apply Fin.strictMono_unique hmono (s.order_emb_of_fin h).StrictMono
  rw [range_order_emb_of_fin, ← Set.image_univ, ← coe_univ, ← coe_image, coe_inj]
  refine' eq_of_subset_of_card_le (fun x hx => _) _
  · rcases mem_image.1 hx with ⟨x, hx, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]
#align finset.order_emb_of_fin_unique Finset.order_emb_of_fin_unique

/-- An order embedding `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
theorem order_emb_of_fin_unique' {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k ↪o α}
    (hfs : ∀ x, f x ∈ s) : f = s.orderEmbOfFin h :=
  RelEmbedding.ext <| Function.funext_iff.1 <| order_emb_of_fin_unique h hfs f.StrictMono
#align finset.order_emb_of_fin_unique' Finset.order_emb_of_fin_unique'

/-- Two parametrizations `order_emb_of_fin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `fin k` and `fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
theorem order_emb_of_fin_eq_order_emb_of_fin_iff {k l : ℕ} {s : Finset α} {i : Fin k} {j : Fin l}
    {h : s.card = k} {h' : s.card = l} :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : ℕ) = (j : ℕ) :=
  by
  substs k l
  exact (s.order_emb_of_fin rfl).eq_iff_eq.trans Fin.ext_iff
#align
  finset.order_emb_of_fin_eq_order_emb_of_fin_iff Finset.order_emb_of_fin_eq_order_emb_of_fin_iff

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `order_emb_of_card_le`
is an order embedding from `fin k` to `α` whose image is contained in `s`. Specifically, it maps
`fin k` to an initial segment of `s`. -/
def orderEmbOfCardLe (s : Finset α) {k : ℕ} (h : k ≤ s.card) : Fin k ↪o α :=
  (Fin.castLe h).trans (s.orderEmbOfFin rfl)
#align finset.order_emb_of_card_le Finset.orderEmbOfCardLe

theorem order_emb_of_card_le_mem (s : Finset α) {k : ℕ} (h : k ≤ s.card) (a) :
    orderEmbOfCardLe s h a ∈ s := by
  simp only [order_emb_of_card_le, RelEmbedding.coe_trans, Finset.order_emb_of_fin_mem]
#align finset.order_emb_of_card_le_mem Finset.order_emb_of_card_le_mem

end SortLinearOrder

unsafe instance [Repr α] : Repr (Finset α) :=
  ⟨fun s => repr s.1⟩

end Finset

