/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.RelIso.Set
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.NodupEquivFin

#align_import data.finset.sort from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

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
#align finset.sort Finset.sort

@[simp]
theorem sort_sorted (s : Finset α) : List.Sorted r (sort r s) :=
  Multiset.sort_sorted _ _
#align finset.sort_sorted Finset.sort_sorted

@[simp]
theorem sort_eq (s : Finset α) : ↑(sort r s) = s.1 :=
  Multiset.sort_eq _ _
#align finset.sort_eq Finset.sort_eq

@[simp]
theorem sort_nodup (s : Finset α) : (sort r s).Nodup :=
  (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort r s))
      -- ⊢ Nodup s.val
                    -- 🎉 no goals
#align finset.sort_nodup Finset.sort_nodup

@[simp]
theorem sort_toFinset [DecidableEq α] (s : Finset α) : (sort r s).toFinset = s :=
  List.toFinset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)
#align finset.sort_to_finset Finset.sort_toFinset

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

theorem sort_perm_toList (s : Finset α) : sort r s ~ s.toList := by
  rw [← Multiset.coe_eq_coe]
  -- ⊢ ↑(sort r s) = ↑(toList s)
  simp only [coe_toList, sort_eq]
  -- 🎉 no goals
#align finset.sort_perm_to_list Finset.sort_perm_toList

end sort

section SortLinearOrder

variable [LinearOrder α]

theorem sort_sorted_lt (s : Finset α) : List.Sorted (· < ·) (sort (· ≤ ·) s) :=
  (sort_sorted _ _).lt_of_le (sort_nodup _ _)
#align finset.sort_sorted_lt Finset.sort_sorted_lt

theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·)).nthLe 0 h = s.min' H := by
  let l := s.sort (· ≤ ·)
  -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) 0 h = min' s H
  apply le_antisymm
  -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) 0 h ≤ min' s H
  · have : s.min' H ∈ l := (Finset.mem_sort (α := α) (· ≤ ·)).mpr (s.min'_mem H)
    -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) 0 h ≤ min' s H
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.min' H := List.mem_iff_get.1 this
    -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) 0 h ≤ min' s H
    rw [← hi]
    -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) 0 h ≤ List.get l i
    exact (s.sort_sorted (· ≤ ·)).rel_nthLe_of_le _ _ (Nat.zero_le i)
    -- 🎉 no goals
  · have : l.get ⟨0, h⟩ ∈ s := (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l 0 h)
    -- ⊢ min' s H ≤ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) 0 h
    exact s.min'_le _ this
    -- 🎉 no goals
#align finset.sorted_zero_eq_min'_aux Finset.sorted_zero_eq_min'_aux

theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·)).nthLe 0 h = s.min' (card_pos.1 <| by rwa [length_sort] at h) :=
                                                          -- 🎉 no goals
  sorted_zero_eq_min'_aux _ _ _
#align finset.sorted_zero_eq_min' Finset.sorted_zero_eq_min'

theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h = (s.sort (· ≤ ·)).nthLe 0 (by rw [length_sort]; exact card_pos.2 h) :=
                                            -- ⊢ 0 < card s
                                                              -- 🎉 no goals
  (sorted_zero_eq_min'_aux _ _ _).symm
#align finset.min'_eq_sorted_zero Finset.min'_eq_sorted_zero

theorem sorted_last_eq_max'_aux (s : Finset α)
    (h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1) h = s.max' H := by
  let l := s.sort (· ≤ ·)
  -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) (List.length (sort (fun x x_1 =>  …
  apply le_antisymm
  -- ⊢ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) (List.length (sort (fun x x_1 =>  …
  · have : l.get ⟨(s.sort (· ≤ ·)).length - 1, h⟩ ∈ s :=
      (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l _ h)
    exact s.le_max' _ this
    -- 🎉 no goals
  · have : s.max' H ∈ l := (Finset.mem_sort (α := α) (· ≤ ·)).mpr (s.max'_mem H)
    -- ⊢ max' s H ≤ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) (List.length (sort (fu …
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.max' H := List.mem_iff_get.1 this
    -- ⊢ max' s H ≤ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) (List.length (sort (fu …
    rw [← hi]
    -- ⊢ List.get l i ≤ List.nthLe (sort (fun x x_1 => x ≤ x_1) s) (List.length (sort …
    exact (s.sort_sorted (· ≤ ·)).rel_nthLe_of_le _ _ (Nat.le_pred_of_lt i.prop)
    -- 🎉 no goals
#align finset.sorted_last_eq_max'_aux Finset.sorted_last_eq_max'_aux

theorem sorted_last_eq_max' {s : Finset α}
    {h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1) h =
      s.max' (by rw [length_sort] at h; exact card_pos.1 (lt_of_le_of_lt bot_le h)) :=
                 -- ⊢ Finset.Nonempty s
                                        -- 🎉 no goals
  sorted_last_eq_max'_aux _ _ _
#align finset.sorted_last_eq_max' Finset.sorted_last_eq_max'

theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1)
        (by simpa using Nat.sub_lt (card_pos.mpr h) zero_lt_one) :=
            -- 🎉 no goals
  (sorted_last_eq_max'_aux _ _ _).symm
#align finset.max'_eq_sorted_last Finset.max'_eq_sorted_last

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderIsoOfFin s h`
is the increasing bijection between `Fin k` and `s` as an `OrderIso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `Fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s :=
  OrderIso.trans (Fin.castIso ((length_sort (α := α) (· ≤ ·)).trans h).symm) <|
    (s.sort_sorted_lt.getIso _).trans <| OrderIso.setCongr _ _ <| Set.ext fun _ => mem_sort _
#align finset.order_iso_of_fin Finset.orderIsoOfFin

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderEmbOfFin s h` is
the increasing bijection between `Fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `Fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)
#align finset.order_emb_of_fin Finset.orderEmbOfFin

@[simp]
theorem coe_orderIsoOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl
#align finset.coe_order_iso_of_fin_apply Finset.coe_orderIsoOfFin_apply

theorem orderIsoOfFin_symm_apply (s : Finset α) {k : ℕ} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = (s.sort (· ≤ ·)).indexOf ↑x :=
  rfl
#align finset.order_iso_of_fin_symm_apply Finset.orderIsoOfFin_symm_apply

theorem orderEmbOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i =
      (s.sort (· ≤ ·)).nthLe i (by rw [length_sort, h]; exact i.2) :=
                                   -- ⊢ ↑i < k
                                                        -- 🎉 no goals
  rfl
#align finset.order_emb_of_fin_apply Finset.orderEmbOfFin_apply

@[simp]
theorem orderEmbOfFin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2
#align finset.order_emb_of_fin_mem Finset.orderEmbOfFin_mem

@[simp]
theorem range_orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ → α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.subtype_apply, OrderIso.coe_toOrderEmbedding, eq_self_iff_true,
    Subtype.range_coe_subtype, Finset.setOf_mem, Finset.coe_inj]
#align finset.range_order_emb_of_fin Finset.range_orderEmbOfFin

/-- The bijection `orderEmbOfFin s h` sends `0` to the minimum of `s`. -/
theorem orderEmbOfFin_zero {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [orderEmbOfFin_apply, Fin.val_mk, sorted_zero_eq_min']
  -- 🎉 no goals
#align finset.order_emb_of_fin_zero Finset.orderEmbOfFin_zero

/-- The bijection `orderEmbOfFin s h` sends `k-1` to the maximum of `s`. -/
theorem orderEmbOfFin_last {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ =
      s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]
  -- 🎉 no goals
#align finset.order_emb_of_fin_last Finset.orderEmbOfFin_last

/-- `orderEmbOfFin {a} h` sends any argument to `a`. -/
@[simp]
theorem orderEmbOfFin_singleton (a : α) (i : Fin 1) :
    orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elim i ⟨0, zero_lt_one⟩, orderEmbOfFin_zero _ zero_lt_one, min'_singleton]
  -- 🎉 no goals
#align finset.order_emb_of_fin_singleton Finset.orderEmbOfFin_singleton

/-- Any increasing map `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α}
    (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h := by
  apply Fin.strictMono_unique hmono (s.orderEmbOfFin h).strictMono
  -- ⊢ Set.range f = Set.range ↑(orderEmbOfFin s h)
  rw [range_orderEmbOfFin, ← Set.image_univ, ← coe_univ, ← coe_image, coe_inj]
  -- ⊢ image f univ = s
  refine' eq_of_subset_of_card_le (fun x hx => _) _
  -- ⊢ x ∈ s
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    -- ⊢ f x ∈ s
    exact hfs x
    -- 🎉 no goals
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]
    -- 🎉 no goals
#align finset.order_emb_of_fin_unique Finset.orderEmbOfFin_unique

/-- An order embedding `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
theorem orderEmbOfFin_unique' {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k ↪o α}
    (hfs : ∀ x, f x ∈ s) : f = s.orderEmbOfFin h :=
  RelEmbedding.ext <| Function.funext_iff.1 <| orderEmbOfFin_unique h hfs f.strictMono
#align finset.order_emb_of_fin_unique' Finset.orderEmbOfFin_unique'

/-- Two parametrizations `orderEmbOfFin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `Fin k` and `Fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
theorem orderEmbOfFin_eq_orderEmbOfFin_iff {k l : ℕ} {s : Finset α} {i : Fin k} {j : Fin l}
    {h : s.card = k} {h' : s.card = l} :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : ℕ) = (j : ℕ) := by
  substs k l
  -- ⊢ ↑(orderEmbOfFin s (_ : card s = card s)) i = ↑(orderEmbOfFin s (_ : card s = …
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff
  -- 🎉 no goals
#align finset.order_emb_of_fin_eq_order_emb_of_fin_iff Finset.orderEmbOfFin_eq_orderEmbOfFin_iff

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `orderEmbOfCardLe`
is an order embedding from `Fin k` to `α` whose image is contained in `s`. Specifically, it maps
`Fin k` to an initial segment of `s`. -/
def orderEmbOfCardLe (s : Finset α) {k : ℕ} (h : k ≤ s.card) : Fin k ↪o α :=
  (Fin.castLEEmb h).trans (s.orderEmbOfFin rfl)
#align finset.order_emb_of_card_le Finset.orderEmbOfCardLe

theorem orderEmbOfCardLe_mem (s : Finset α) {k : ℕ} (h : k ≤ s.card) (a) :
    orderEmbOfCardLe s h a ∈ s := by
  simp only [orderEmbOfCardLe, RelEmbedding.coe_trans, Finset.orderEmbOfFin_mem,
    Function.comp_apply]
#align finset.order_emb_of_card_le_mem Finset.orderEmbOfCardLe_mem

end SortLinearOrder

unsafe instance [Repr α] : Repr (Finset α) where
  reprPrec s _ :=
    -- multiset uses `0` not `∅` for empty sets
    if s.card = 0 then "∅" else repr s.1

end Finset
