/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module data.list.nodup_equiv_fin
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.List.Sort
import Mathbin.Data.List.Duplicate

/-!
# Equivalence between `fin (length l)` and elements of a list

Given a list `l`,

* if `l` has no duplicates, then `list.nodup.nth_le_equiv` is the equivalence between
  `fin (length l)` and `{x // x ∈ l}` sending `⟨i, hi⟩` to `⟨nth_le l i hi, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨index_of x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `list.nodup.nth_le_equiv_of_forall_mem_list` defines an equivalence between
  `fin (length l)` and `α`;  if `α` does not have decidable equality, then
  there is a bijection `list.nodup.nth_le_bijection_of_forall_mem_list`;

* if `l` is sorted w.r.t. `(<)`, then `list.sorted.nth_le_iso` is the same bijection reinterpreted
  as an `order_iso`.

-/


namespace List

variable {α : Type _}

namespace Nodup

/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
a bijection `fin l.length → α`.  See `list.nodup.nth_le_equiv_of_forall_mem_list`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
def nthLeBijectionOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) :
    { f : Fin l.length → α // Function.Bijective f } :=
  ⟨fun i => l.nthLe i i.property, fun i j h => Fin.ext <| (nd.nth_le_inj_iff _ _).1 h, fun x =>
    let ⟨i, hi, hl⟩ := List.mem_iff_nthLe.1 (h x)
    ⟨⟨i, hi⟩, hl⟩⟩
#align list.nodup.nth_le_bijection_of_forall_mem_list List.Nodup.nthLeBijectionOfForallMemList

variable [DecidableEq α]

/-- If `l` has no duplicates, then `list.nth_le` defines an equivalence between `fin (length l)` and
the set of elements of `l`. -/
@[simps]
def nthLeEquiv (l : List α) (H : Nodup l) : Fin (length l) ≃ { x // x ∈ l }
    where
  toFun i := ⟨nthLe l i i.2, nthLe_mem l i i.2⟩
  invFun x := ⟨indexOf (↑x) l, indexOf_lt_length.2 x.2⟩
  left_inv i := by simp [H]
  right_inv x := by simp
#align list.nodup.nth_le_equiv List.Nodup.nthLeEquiv

/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
an equivalence between `fin l.length` and `α`.

See `list.nodup.nth_le_bijection_of_forall_mem_list` for a version without
decidable equality. -/
@[simps]
def nthLeEquivOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) : Fin l.length ≃ α
    where
  toFun i := l.nthLe i i.2
  invFun a := ⟨_, indexOf_lt_length.2 (h a)⟩
  left_inv i := by simp [nd]
  right_inv a := by simp
#align list.nodup.nth_le_equiv_of_forall_mem_list List.Nodup.nthLeEquivOfForallMemList

end Nodup

namespace Sorted

variable [Preorder α] {l : List α}

theorem nth_le_mono (h : l.Sorted (· ≤ ·)) : Monotone fun i : Fin l.length => l.nthLe i i.2 :=
  fun i j => h.rel_nth_le_of_le _ _
#align list.sorted.nth_le_mono List.Sorted.nth_le_mono

theorem nth_le_strict_mono (h : l.Sorted (· < ·)) :
    StrictMono fun i : Fin l.length => l.nthLe i i.2 := fun i j => h.rel_nth_le_of_lt _ _
#align list.sorted.nth_le_strict_mono List.Sorted.nth_le_strict_mono

variable [DecidableEq α]

/-- If `l` is a list sorted w.r.t. `(<)`, then `list.nth_le` defines an order isomorphism between
`fin (length l)` and the set of elements of `l`. -/
def nthLeIso (l : List α) (H : Sorted (· < ·) l) : Fin (length l) ≃o { x // x ∈ l }
    where
  toEquiv := H.Nodup.nthLeEquiv l
  map_rel_iff' i j := H.nth_le_strict_mono.le_iff_le
#align list.sorted.nth_le_iso List.Sorted.nthLeIso

variable (H : Sorted (· < ·) l) {x : { x // x ∈ l }} {i : Fin l.length}

@[simp]
theorem coe_nth_le_iso_apply : (H.nthLeIso l i : α) = nthLe l i i.2 :=
  rfl
#align list.sorted.coe_nth_le_iso_apply List.Sorted.coe_nth_le_iso_apply

@[simp]
theorem coe_nth_le_iso_symm_apply : ((H.nthLeIso l).symm x : ℕ) = indexOf (↑x) l :=
  rfl
#align list.sorted.coe_nth_le_iso_symm_apply List.Sorted.coe_nth_le_iso_symm_apply

end Sorted

section Sublist

/-- If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `sublist l l'`.
-/
theorem sublist_of_order_embedding_nth_eq {l l' : List α} (f : ℕ ↪o ℕ)
    (hf : ∀ ix : ℕ, l.nth ix = l'.nth (f ix)) : l <+ l' :=
  by
  induction' l with hd tl IH generalizing l' f
  · simp
  have : some hd = _ := hf 0
  rw [eq_comm, List.get?_eq_some'] at this
  obtain ⟨w, h⟩ := this
  let f' : ℕ ↪o ℕ :=
    OrderEmbedding.ofMapLeIff (fun i => f (i + 1) - (f 0 + 1)) fun a b => by
      simp [tsub_le_tsub_iff_right, Nat.succ_le_iff, Nat.lt_succ_iff]
  have : ∀ ix, tl.nth ix = (l'.drop (f 0 + 1)).nth (f' ix) :=
    by
    intro ix
    simp [List.get?_drop, add_tsub_cancel_of_le, Nat.succ_le_iff, ← hf]
  rw [← List.take_append_drop (f 0 + 1) l', ← List.singleton_append]
  apply List.Sublist.append _ (IH _ this)
  rw [List.singleton_sublist, ← h, l'.nth_le_take _ (Nat.lt_succ_self _)]
  apply List.nthLe_mem
#align list.sublist_of_order_embedding_nth_eq List.sublist_of_order_embedding_nth_eq

/-- A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_order_embedding_nth_eq {l l' : List α} :
    l <+ l' ↔ ∃ f : ℕ ↪o ℕ, ∀ ix : ℕ, l.nth ix = l'.nth (f ix) :=
  by
  constructor
  · intro H
    induction' H with xs ys y H IH xs ys x H IH
    · simp
    · obtain ⟨f, hf⟩ := IH
      refine' ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), _⟩
      simpa using hf
    · obtain ⟨f, hf⟩ := IH
      refine'
        ⟨OrderEmbedding.ofMapLeIff (fun ix : ℕ => if ix = 0 then 0 else (f ix.pred).succ) _, _⟩
      · rintro ⟨_ | a⟩ ⟨_ | b⟩ <;> simp [Nat.succ_le_succ_iff]
      · rintro ⟨_ | i⟩
        · simp
        · simpa using hf _
  · rintro ⟨f, hf⟩
    exact sublist_of_order_embedding_nth_eq f hf
#align list.sublist_iff_exists_order_embedding_nth_eq List.sublist_iff_exists_order_embedding_nth_eq

/-- A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `fin l.length` into `fin l'.length` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_fin_order_embedding_nth_le_eq {l l' : List α} :
    l <+ l' ↔
      ∃ f : Fin l.length ↪o Fin l'.length,
        ∀ ix : Fin l.length, l.nthLe ix ix.is_lt = l'.nthLe (f ix) (f ix).is_lt :=
  by
  rw [sublist_iff_exists_order_embedding_nth_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h : ∀ {i : ℕ} (h : i < l.length), f i < l'.length :=
      by
      intro i hi
      specialize hf i
      rw [nth_le_nth hi, eq_comm, nth_eq_some] at hf
      obtain ⟨h, -⟩ := hf
      exact h
    refine' ⟨OrderEmbedding.ofMapLeIff (fun ix => ⟨f ix, h ix.is_lt⟩) _, _⟩
    · simp
    · intro i
      apply Option.some_injective
      simpa [← nth_le_nth] using hf _
  · rintro ⟨f, hf⟩
    refine'
      ⟨OrderEmbedding.ofStrictMono (fun i => if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length)
          _,
        _⟩
    · intro i j h
      dsimp only
      split_ifs with hi hj hj hi
      · simpa using h
      · rw [add_comm]
        exact lt_add_of_lt_of_pos (Fin.is_lt _) (i.zero_le.trans_lt h)
      · exact absurd (h.trans hj) hi
      · simpa using h
    · intro i
      simp only [OrderEmbedding.coe_ofStrictMono]
      split_ifs with hi
      · rw [nth_le_nth hi, nth_le_nth, ← hf]
        simp
      · rw [nth_len_le, nth_len_le]
        · simp
        · simpa using hi
#align
  list.sublist_iff_exists_fin_order_embedding_nth_le_eq List.sublist_iff_exists_fin_order_embedding_nth_le_eq

/-- An element `x : α` of `l : list α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
theorem duplicate_iff_exists_distinct_nth_le {l : List α} {x : α} :
    l.Duplicate x ↔
      ∃ (n : ℕ)(hn : n < l.length)(m : ℕ)(hm : m < l.length)(h : n < m),
        x = l.nthLe n hn ∧ x = l.nthLe m hm :=
  by
  classical
    rw [duplicate_iff_two_le_count, le_count_iff_replicate_sublist,
      sublist_iff_exists_fin_order_embedding_nth_le_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine' ⟨f ⟨0, by simp⟩, Fin.is_lt _, f ⟨1, by simp⟩, Fin.is_lt _, by simp, _, _⟩
      · simpa using hf ⟨0, by simp⟩
      · simpa using hf ⟨1, by simp⟩
    · rintro ⟨n, hn, m, hm, hnm, h, h'⟩
      refine' ⟨OrderEmbedding.ofStrictMono (fun i => if (i : ℕ) = 0 then ⟨n, hn⟩ else ⟨m, hm⟩) _, _⟩
      · rintro ⟨⟨_ | i⟩, hi⟩ ⟨⟨_ | j⟩, hj⟩
        · simp
        · simp [hnm]
        · simp
        · simp only [Nat.lt_succ_iff, Nat.succ_le_succ_iff, replicate, length,
            nonpos_iff_eq_zero] at hi hj
          simp [hi, hj]
      · rintro ⟨⟨_ | i⟩, hi⟩
        · simpa using h
        · simpa using h'
#align list.duplicate_iff_exists_distinct_nth_le List.duplicate_iff_exists_distinct_nth_le

end Sublist

end List

