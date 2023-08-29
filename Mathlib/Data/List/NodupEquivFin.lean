/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Duplicate

#align_import data.list.nodup_equiv_fin from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Equivalence between `Fin (length l)` and elements of a list

Given a list `l`,

* if `l` has no duplicates, then `List.Nodup.getEquiv` is the equivalence between
  `Fin (length l)` and `{x // x ∈ l}` sending `i` to `⟨get l i, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨indexOf x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `List.Nodup.getEquivOfForallMemList` defines an equivalence between
  `Fin (length l)` and `α`;  if `α` does not have decidable equality, then
  there is a bijection `List.Nodup.getBijectionOfForallMemList`;

* if `l` is sorted w.r.t. `(<)`, then `List.Sorted.getIso` is the same bijection reinterpreted
  as an `OrderIso`.

-/


namespace List

variable {α : Type*}

namespace Nodup

/-- If `l` lists all the elements of `α` without duplicates, then `List.get` defines
a bijection `Fin l.length → α`.  See `List.Nodup.getEquivOfForallMemList`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
def getBijectionOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) :
    { f : Fin l.length → α // Function.Bijective f } :=
  ⟨fun i => l.get i, fun _ _ h => Fin.ext <| (nd.nthLe_inj_iff _ _).1 h,
   fun x =>
    let ⟨i, hl⟩ := List.mem_iff_get.1 (h x)
    ⟨i, hl⟩⟩
#align list.nodup.nth_le_bijection_of_forall_mem_list List.Nodup.getBijectionOfForallMemList

variable [DecidableEq α]

/-- If `l` has no duplicates, then `List.get` defines an equivalence between `Fin (length l)` and
the set of elements of `l`. -/
@[simps]
def getEquiv (l : List α) (H : Nodup l) : Fin (length l) ≃ { x // x ∈ l } where
  toFun i := ⟨get l i, get_mem l i i.2⟩
  invFun x := ⟨indexOf (↑x) l, indexOf_lt_length.2 x.2⟩
  left_inv i := by simp only [List.get_indexOf, eq_self_iff_true, Fin.eta, Subtype.coe_mk, H]
                   -- 🎉 no goals
  right_inv x := by simp
                    -- 🎉 no goals
#align list.nodup.nth_le_equiv List.Nodup.getEquiv

/-- If `l` lists all the elements of `α` without duplicates, then `List.get` defines
an equivalence between `Fin l.length` and `α`.

See `List.Nodup.getBijectionOfForallMemList` for a version without
decidable equality. -/
@[simps]
def getEquivOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) : Fin l.length ≃ α
    where
  toFun i := l.get i
  invFun a := ⟨_, indexOf_lt_length.2 (h a)⟩
  left_inv i := by simp [List.get_indexOf, nd]
                   -- 🎉 no goals
  right_inv a := by simp
                    -- 🎉 no goals
#align list.nodup.nth_le_equiv_of_forall_mem_list List.Nodup.getEquivOfForallMemList

end Nodup

namespace Sorted

variable [Preorder α] {l : List α}

theorem get_mono (h : l.Sorted (· ≤ ·)) : Monotone l.get := fun _ _ => h.rel_get_of_le
#align list.sorted.nth_le_mono List.Sorted.get_mono

theorem get_strictMono (h : l.Sorted (· < ·)) : StrictMono l.get := fun _ _ => h.rel_get_of_lt
#align list.sorted.nth_le_strict_mono List.Sorted.get_strictMono

variable [DecidableEq α]

/-- If `l` is a list sorted w.r.t. `(<)`, then `List.get` defines an order isomorphism between
`Fin (length l)` and the set of elements of `l`. -/
def getIso (l : List α) (H : Sorted (· < ·) l) : Fin (length l) ≃o { x // x ∈ l } where
  toEquiv := H.nodup.getEquiv l
  map_rel_iff' := H.get_strictMono.le_iff_le
#align list.sorted.nth_le_iso List.Sorted.getIso

variable (H : Sorted (· < ·) l) {x : { x // x ∈ l }} {i : Fin l.length}

@[simp]
theorem coe_getIso_apply : (H.getIso l i : α) = get l i :=
  rfl
#align list.sorted.coe_nth_le_iso_apply List.Sorted.coe_getIso_apply

@[simp]
theorem coe_getIso_symm_apply : ((H.getIso l).symm x : ℕ) = indexOf (↑x) l :=
  rfl
#align list.sorted.coe_nth_le_iso_symm_apply List.Sorted.coe_getIso_symm_apply

end Sorted

section Sublist

/-- If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `Sublist l l'`.
-/
theorem sublist_of_orderEmbedding_get?_eq {l l' : List α} (f : ℕ ↪o ℕ)
    (hf : ∀ ix : ℕ, l.get? ix = l'.get? (f ix)) : l <+ l' := by
  induction' l with hd tl IH generalizing l' f
  -- ⊢ [] <+ l'
  · simp
    -- 🎉 no goals
  have : some hd = _ := hf 0
  -- ⊢ hd :: tl <+ l'
  rw [eq_comm, List.get?_eq_some] at this
  -- ⊢ hd :: tl <+ l'
  obtain ⟨w, h⟩ := this
  -- ⊢ hd :: tl <+ l'
  let f' : ℕ ↪o ℕ :=
    OrderEmbedding.ofMapLEIff (fun i => f (i + 1) - (f 0 + 1)) fun a b => by
      dsimp only
      rw [tsub_le_tsub_iff_right, OrderEmbedding.le_iff_le, Nat.succ_le_succ_iff]
      rw [Nat.succ_le_iff, OrderEmbedding.lt_iff_lt]
      exact b.succ_pos
  have : ∀ ix, tl.get? ix = (l'.drop (f 0 + 1)).get? (f' ix) := by
    intro ix
    rw [List.get?_drop, OrderEmbedding.coe_ofMapLEIff, add_tsub_cancel_of_le, ←hf, List.get?]
    rw [Nat.succ_le_iff, OrderEmbedding.lt_iff_lt]
    exact ix.succ_pos
  rw [← List.take_append_drop (f 0 + 1) l', ← List.singleton_append]
  -- ⊢ [hd] ++ tl <+ take (↑f 0 + 1) l' ++ drop (↑f 0 + 1) l'
  apply List.Sublist.append _ (IH _ this)
  -- ⊢ [hd] <+ take (↑f 0 + 1) l'
  rw [List.singleton_sublist, ← h, l'.get_take _ (Nat.lt_succ_self _)]
  -- ⊢ get (take (Nat.succ (↑f 0)) l') { val := ↑f 0, isLt := (_ : ↑f 0 < length (t …
  apply List.get_mem
  -- 🎉 no goals
#align list.sublist_of_order_embedding_nth_eq List.sublist_of_orderEmbedding_get?_eq

/-- A `l : List α` is `Sublist l l'` for `l' : List α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_orderEmbedding_get?_eq {l l' : List α} :
    l <+ l' ↔ ∃ f : ℕ ↪o ℕ, ∀ ix : ℕ, l.get? ix = l'.get? (f ix) := by
  constructor
  -- ⊢ l <+ l' → ∃ f, ∀ (ix : ℕ), get? l ix = get? l' (↑f ix)
  · intro H
    -- ⊢ ∃ f, ∀ (ix : ℕ), get? l ix = get? l' (↑f ix)
    induction' H with xs ys y _H IH xs ys x _H IH
    · simp
      -- 🎉 no goals
    · obtain ⟨f, hf⟩ := IH
      -- ⊢ ∃ f, ∀ (ix : ℕ), get? xs ix = get? (y :: ys) (↑f ix)
      refine' ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), _⟩
      -- ⊢ ∀ (ix : ℕ), get? xs ix = get? (y :: ys) (↑(RelEmbedding.trans f (OrderEmbedd …
      simpa using hf
      -- 🎉 no goals
    · obtain ⟨f, hf⟩ := IH
      -- ⊢ ∃ f, ∀ (ix : ℕ), get? (x :: xs) ix = get? (x :: ys) (↑f ix)
      refine'
        ⟨OrderEmbedding.ofMapLEIff (fun ix : ℕ => if ix = 0 then 0 else (f ix.pred).succ) _, _⟩
      · rintro ⟨_ | a⟩ ⟨_ | b⟩ <;> simp [Nat.succ_le_succ_iff]
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
      · rintro ⟨_ | i⟩
        -- ⊢ get? (x :: xs) Nat.zero = get? (x :: ys) (↑(OrderEmbedding.ofMapLEIff (fun i …
        · simp
          -- 🎉 no goals
        · simpa using hf _
          -- 🎉 no goals
  · rintro ⟨f, hf⟩
    -- ⊢ l <+ l'
    exact sublist_of_orderEmbedding_get?_eq f hf
    -- 🎉 no goals
#align list.sublist_iff_exists_order_embedding_nth_eq List.sublist_iff_exists_orderEmbedding_get?_eq

/-- A `l : List α` is `Sublist l l'` for `l' : List α` iff
there is `f`, an order-preserving embedding of `Fin l.length` into `Fin l'.length` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_fin_orderEmbedding_get_eq {l l' : List α} :
    l <+ l' ↔
      ∃ f : Fin l.length ↪o Fin l'.length,
        ∀ ix : Fin l.length, l.get ix = l'.get (f ix) := by
  rw [sublist_iff_exists_orderEmbedding_get?_eq]
  -- ⊢ (∃ f, ∀ (ix : ℕ), get? l ix = get? l' (↑f ix)) ↔ ∃ f, ∀ (ix : Fin (length l) …
  constructor
  -- ⊢ (∃ f, ∀ (ix : ℕ), get? l ix = get? l' (↑f ix)) → ∃ f, ∀ (ix : Fin (length l) …
  · rintro ⟨f, hf⟩
    -- ⊢ ∃ f, ∀ (ix : Fin (length l)), get l ix = get l' (↑f ix)
    have h : ∀ {i : ℕ} (_ : i < l.length), f i < l'.length := by
      intro i hi
      specialize hf i
      rw [get?_eq_get hi, eq_comm, get?_eq_some] at hf
      obtain ⟨h, -⟩ := hf
      exact h
    refine' ⟨OrderEmbedding.ofMapLEIff (fun ix => ⟨f ix, h ix.is_lt⟩) _, _⟩
    -- ⊢ ∀ (a b : Fin (length l)), (fun ix => { val := ↑f ↑ix, isLt := (_ : ↑f ↑ix <  …
    · simp
      -- 🎉 no goals
    · intro i
      -- ⊢ get l i = get l' (↑(OrderEmbedding.ofMapLEIff (fun ix => { val := ↑f ↑ix, is …
      apply Option.some_injective
      -- ⊢ some (get l i) = some (get l' (↑(OrderEmbedding.ofMapLEIff (fun ix => { val  …
      simpa [get?_eq_get i.2, get?_eq_get (h i.2)] using hf i
      -- 🎉 no goals
  · rintro ⟨f, hf⟩
    -- ⊢ ∃ f, ∀ (ix : ℕ), get? l ix = get? l' (↑f ix)
    refine'
      ⟨OrderEmbedding.ofStrictMono (fun i => if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length)
          _,
        _⟩
    · intro i j h
      -- ⊢ (fun i => if hi : i < length l then ↑(↑f { val := i, isLt := hi }) else i +  …
      dsimp only
      -- ⊢ (if hi : i < length l then ↑(↑f { val := i, isLt := hi }) else i + length l' …
      split_ifs with hi hj hj
      · rwa [Fin.val_fin_lt, f.lt_iff_lt]
        -- 🎉 no goals
      · rw [add_comm]
        -- ⊢ ↑(↑f { val := i, isLt := hi }) < length l' + j
        exact lt_add_of_lt_of_pos (Fin.is_lt _) (i.zero_le.trans_lt h)
        -- 🎉 no goals
      · exact absurd (h.trans hj) hi
        -- 🎉 no goals
      · simpa using h
        -- 🎉 no goals
    · intro i
      -- ⊢ get? l i = get? l' (↑(OrderEmbedding.ofStrictMono (fun i => if hi : i < leng …
      simp only [OrderEmbedding.coe_ofStrictMono]
      -- ⊢ get? l i = get? l' (if h : i < length l then ↑(↑f { val := i, isLt := (_ : i …
      split_ifs with hi
      -- ⊢ get? l i = get? l' ↑(↑f { val := i, isLt := (_ : i < length l) })
      · rw [get?_eq_get hi, get?_eq_get, ← hf]
        -- 🎉 no goals
      · rw [get?_eq_none.mpr, get?_eq_none.mpr]
        -- ⊢ length l' ≤ i + length l'
        · simp
          -- 🎉 no goals
        · simpa using hi
          -- 🎉 no goals
#align list.sublist_iff_exists_fin_order_embedding_nth_le_eq List.sublist_iff_exists_fin_orderEmbedding_get_eq

/-- An element `x : α` of `l : List α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
theorem duplicate_iff_exists_distinct_get {l : List α} {x : α} :
    l.Duplicate x ↔
      ∃ (n m : Fin l.length) (_ : n < m),
        x = l.get n ∧ x = l.get m := by
  classical
    rw [duplicate_iff_two_le_count, le_count_iff_replicate_sublist,
      sublist_iff_exists_fin_orderEmbedding_get_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine' ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩,
        f.lt_iff_lt.2 (show (0 : ℕ) < 1 from zero_lt_one), _⟩
      · rw [← hf, ← hf]; simp
    · rintro ⟨n, m, hnm, h, h'⟩
      refine' ⟨OrderEmbedding.ofStrictMono (fun i => if (i : ℕ) = 0 then n else m) _, _⟩
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

/-- An element `x : α` of `l : List α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
@[deprecated duplicate_iff_exists_distinct_get]
theorem duplicate_iff_exists_distinct_nthLe {l : List α} {x : α} :
    l.Duplicate x ↔
      ∃ (n : ℕ) (hn : n < l.length) (m : ℕ) (hm : m < l.length) (_ : n < m),
        x = l.nthLe n hn ∧ x = l.nthLe m hm :=
  duplicate_iff_exists_distinct_get.trans
    ⟨fun ⟨n, m, h⟩ => ⟨n.1, n.2, m.1, m.2, h⟩,
    fun ⟨n, hn, m, hm, h⟩ => ⟨⟨n, hn⟩, ⟨m, hm⟩, h⟩⟩
#align list.duplicate_iff_exists_distinct_nth_le List.duplicate_iff_exists_distinct_nthLe

end Sublist

end List
