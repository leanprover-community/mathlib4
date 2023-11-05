/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky
-/
import Mathlib.Data.List.Perm
import Mathlib.Data.List.Range

#align_import data.list.rotate from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# List rotation

This file proves basic results about `List.rotate`, the list rotation.

## Main declarations

* `List.IsRotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `List.cyclicPermutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/


universe u

variable {α : Type u}

open Nat Function

namespace List

theorem rotate_mod (l : List α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n := by simp [rotate]

@[simp]
theorem rotate_nil (n : ℕ) : ([] : List α).rotate n = [] := by simp [rotate]

@[simp]
theorem rotate_zero (l : List α) : l.rotate 0 = l := by simp [rotate]

--Porting note: removing simp, simp can prove it
theorem rotate'_nil (n : ℕ) : ([] : List α).rotate' n = [] := by cases n <;> rfl

@[simp]
theorem rotate'_zero (l : List α) : l.rotate' 0 = l := by cases l <;> rfl

theorem rotate'_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp]
theorem length_rotate' : ∀ (l : List α) (n : ℕ), (l.rotate' n).length = l.length
  | [], _ => by simp
  | a :: l, 0 => rfl
  | a :: l, n + 1 => by rw [List.rotate', length_rotate' (l ++ [a]) n]; simp

theorem rotate'_eq_drop_append_take :
    ∀ {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = l.drop n ++ l.take n
  | [], n, h => by simp [drop_append_of_le_length h]
  | l, 0, h => by simp [take_append_of_le_length h]
  | a :: l, n + 1, h => by
    have hnl : n ≤ l.length := le_of_succ_le_succ h
    have hnl' : n ≤ (l ++ [a]).length := by
      rw [length_append, length_cons, List.length]; exact le_of_succ_le h
    rw [rotate'_cons_succ, rotate'_eq_drop_append_take hnl', drop, take,
        drop_append_of_le_length hnl, take_append_of_le_length hnl]; simp

theorem rotate'_rotate' : ∀ (l : List α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
  | a :: l, 0, m => by simp
  | [], n, m => by simp
  | a :: l, n + 1, m => by
    rw [rotate'_cons_succ, rotate'_rotate' _ n, add_right_comm, ← rotate'_cons_succ]

@[simp]
theorem rotate'_length (l : List α) : rotate' l l.length = l := by
  rw [rotate'_eq_drop_append_take le_rfl]; simp

@[simp]
theorem rotate'_length_mul (l : List α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
  | 0 => by simp
  | n + 1 =>
    calc
      l.rotate' (l.length * (n + 1)) =
          (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length :=
        by simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul l n]

theorem rotate'_mod (l : List α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
  calc
    l.rotate' (n % l.length) =
        (l.rotate' (n % l.length)).rotate' ((l.rotate' (n % l.length)).length * (n / l.length)) :=
      by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]

theorem rotate_eq_rotate' (l : List α) (n : ℕ) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then by simp_all [length_eq_zero]
  else by
    rw [← rotate'_mod,
        rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))];
      simp [rotate]

theorem rotate_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate n.succ = (l ++ [a]).rotate n := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp]
theorem mem_rotate : ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
  | [], _, n => by simp
  | a :: l, _, 0 => by simp
  | a :: l, _, n + 1 => by simp [rotate_cons_succ, mem_rotate, or_comm]

@[simp]
theorem length_rotate (l : List α) (n : ℕ) : (l.rotate n).length = l.length := by
  rw [rotate_eq_rotate', length_rotate']

-- porting note: todo: add `@[simp]`
theorem rotate_replicate (a : α) (n : ℕ) (k : ℕ) : (replicate n a).rotate k = replicate n a :=
  eq_replicate.2 ⟨by rw [length_rotate, length_replicate], fun b hb =>
    eq_of_mem_replicate <| mem_rotate.1 hb⟩

theorem rotate_eq_drop_append_take {l : List α} {n : ℕ} :
    n ≤ l.length → l.rotate n = l.drop n ++ l.take n := by
  rw [rotate_eq_rotate']; exact rotate'_eq_drop_append_take

theorem rotate_eq_drop_append_take_mod {l : List α} {n : ℕ} :
    l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) := by
  cases' l.length.zero_le.eq_or_lt with hl hl
  · simp [eq_nil_of_length_eq_zero hl.symm]
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le, rotate_mod]

@[simp]
theorem rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' ++ l := by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
  · simp_all [rotate']

theorem rotate_rotate (l : List α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n + m) := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']

@[simp]
theorem rotate_length (l : List α) : rotate l l.length = l := by
  rw [rotate_eq_rotate', rotate'_length]

@[simp]
theorem rotate_length_mul (l : List α) (n : ℕ) : l.rotate (l.length * n) = l := by
  rw [rotate_eq_rotate', rotate'_length_mul]

theorem prod_rotate_eq_one_of_prod_eq_one [Group α] :
    ∀ {l : List α} (_ : l.prod = 1) (n : ℕ), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl;
      rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq, ←
        one_mul (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_self, mul_one]

theorem rotate_perm (l : List α) (n : ℕ) : l.rotate n ~ l := by
  rw [rotate_eq_rotate']
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)

@[simp]
theorem nodup_rotate {l : List α} {n : ℕ} : Nodup (l.rotate n) ↔ Nodup l :=
  (rotate_perm l n).nodup_iff

@[simp]
theorem rotate_eq_nil_iff {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] := by
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · simp [rotate_cons_succ, hn]

@[simp]
theorem nil_eq_rotate_iff {l : List α} {n : ℕ} : [] = l.rotate n ↔ [] = l := by
  rw [eq_comm, rotate_eq_nil_iff, eq_comm]

@[simp]
theorem rotate_singleton (x : α) (n : ℕ) : [x].rotate n = [x] :=
  rotate_replicate x 1 n

theorem zipWith_rotate_distrib {α β γ : Type*} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)
    (h : l.length = l'.length) :
    (zipWith f l l').rotate n = zipWith f (l.rotate n) (l'.rotate n) := by
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod,
    rotate_eq_drop_append_take_mod, h, zipWith_append, ← zipWith_distrib_drop, ←
    zipWith_distrib_take, List.length_zipWith, h, min_self]
  rw [length_drop, length_drop, h]

attribute [local simp] rotate_cons_succ

--Porting note: removing @[simp], simp can prove it
theorem zipWith_rotate_one {β : Type*} (f : α → α → β) (x y : α) (l : List α) :
    zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (l ++ [x]) := by
  simp

theorem get?_rotate {l : List α} {n m : ℕ} (hml : m < l.length) :
    (l.rotate n).get? m = l.get? ((m + n) % l.length) := by
  rw [rotate_eq_drop_append_take_mod]
  rcases lt_or_le m (l.drop (n % l.length)).length with hm | hm
  · rw [get?_append hm, get?_drop, add_comm m, ← mod_add_mod]
    rw [length_drop, lt_tsub_iff_left] at hm
    rw [mod_eq_of_lt hm]
  · have hlt : n % length l < length l := mod_lt _ (m.zero_le.trans_lt hml)
    rw [get?_append_right hm, get?_take, length_drop]
    · congr 1
      rw [length_drop] at hm
      have hm' := tsub_le_iff_left.1 hm
      have : n % length l + m - length l < length l := by
        rw [tsub_lt_iff_left hm']
        exact Nat.add_lt_add hlt hml
      conv_rhs => rw [add_comm m, ← mod_add_mod, mod_eq_sub_mod hm', mod_eq_of_lt this]
      rw [← add_right_inj l.length, ← add_tsub_assoc_of_le, add_tsub_tsub_cancel,
        add_tsub_cancel_of_le, add_comm]
      exacts [hm', hlt.le, hm]
    · rwa [tsub_lt_iff_left hm, length_drop, tsub_add_cancel_of_le hlt.le]

-- porting note: new lemma
theorem get_rotate (l : List α) (n : ℕ) (k : Fin (l.rotate n).length) :
    (l.rotate n).get k =
      l.get ⟨(k + n) % l.length, mod_lt _ (length_rotate l n ▸ k.1.zero_le.trans_lt k.2)⟩ := by
  rw [← Option.some_inj, ← get?_eq_get, ← get?_eq_get, get?_rotate]
  exact k.2.trans_eq (length_rotate _ _)

theorem head?_rotate {l : List α} {n : ℕ} (h : n < l.length) : head? (l.rotate n) = l.get? n := by
  rw [← get?_zero, get?_rotate (n.zero_le.trans_lt h), zero_add, Nat.mod_eq_of_lt h]

-- porting note: moved down from its original location below `get_rotate` so that the
-- non-deprecated lemma does not use the deprecated version
set_option linter.deprecated false in
@[deprecated get_rotate]
theorem nthLe_rotate (l : List α) (n k : ℕ) (hk : k < (l.rotate n).length) :
    (l.rotate n).nthLe k hk =
      l.nthLe ((k + n) % l.length) (mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt hk)) :=
  get_rotate l n ⟨k, hk⟩

set_option linter.deprecated false in
theorem nthLe_rotate_one (l : List α) (k : ℕ) (hk : k < (l.rotate 1).length) :
    (l.rotate 1).nthLe k hk =
      l.nthLe ((k + 1) % l.length) (mod_lt _ (length_rotate l 1 ▸ k.zero_le.trans_lt hk)) :=
  nthLe_rotate l 1 k hk

-- porting note: new lemma
/-- A version of `List.get_rotate` that represents `List.get l` in terms of
`List.get (List.rotate l n)`, not vice versa. Can be used instead of rewriting `List.get_rotate`
from right to left. -/
theorem get_eq_get_rotate (l : List α) (n : ℕ) (k : Fin l.length) :
    l.get k = (l.rotate n).get ⟨(l.length - n % l.length + k) % l.length,
      (Nat.mod_lt _ (k.1.zero_le.trans_lt k.2)).trans_eq (length_rotate _ _).symm⟩ := by
  rw [get_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod, add_right_comm, tsub_add_cancel_of_le, add_mod_left, mod_eq_of_lt]
  exacts [k.2, (mod_lt _ (k.1.zero_le.trans_lt k.2)).le]

set_option linter.deprecated false in
/-- A variant of `List.nthLe_rotate` useful for rewrites from right to left. -/
@[deprecated get_eq_get_rotate]
theorem nthLe_rotate' (l : List α) (n k : ℕ) (hk : k < l.length) :
    (l.rotate n).nthLe ((l.length - n % l.length + k) % l.length)
        ((Nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_le (length_rotate _ _).ge) =
      l.nthLe k hk :=
  (get_eq_get_rotate l n ⟨k, hk⟩).symm

theorem rotate_eq_self_iff_eq_replicate [hα : Nonempty α] :
    ∀ {l : List α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = replicate l.length a
  | [] => by simp
  | a :: l => ⟨fun h => ⟨a, ext_get (length_replicate _ _).symm fun n h₁ h₂ => by
      rw [get_replicate, ← Option.some_inj, ← get?_eq_get, ← head?_rotate h₁, h, head?_cons]⟩,
    fun ⟨b, hb⟩ n => by rw [hb, rotate_replicate]⟩

theorem rotate_one_eq_self_iff_eq_replicate [Nonempty α] {l : List α} :
    l.rotate 1 = l ↔ ∃ a : α, l = List.replicate l.length a :=
  ⟨fun h =>
    rotate_eq_self_iff_eq_replicate.mp fun n =>
      Nat.rec l.rotate_zero (fun n hn => by rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn]) n,
    fun h => rotate_eq_self_iff_eq_replicate.mpr h 1⟩

theorem rotate_injective (n : ℕ) : Function.Injective fun l : List α => l.rotate n := by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h (by simp_all)
  rw [← take_append_drop _ l, ht, hd, take_append_drop]

@[simp]
theorem rotate_eq_rotate {l l' : List α} {n : ℕ} : l.rotate n = l'.rotate n ↔ l = l' :=
  (rotate_injective n).eq_iff

theorem rotate_eq_iff {l l' : List α} {n : ℕ} :
    l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) := by
  rw [← @rotate_eq_rotate _ l _ n, rotate_rotate, ← rotate_mod l', add_mod]
  cases' l'.length.zero_le.eq_or_lt with hl hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil, rotate_eq_nil_iff]
  · cases' (Nat.zero_le (n % l'.length)).eq_or_lt with hn hn
    · simp [← hn]
    · rw [mod_eq_of_lt (tsub_lt_self hl hn), tsub_add_cancel_of_le, mod_self, rotate_zero]
      exact (Nat.mod_lt _ hl).le

@[simp]
theorem rotate_eq_singleton_iff {l : List α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] := by
  rw [rotate_eq_iff, rotate_singleton]

@[simp]
theorem singleton_eq_rotate_iff {l : List α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l := by
  rw [eq_comm, rotate_eq_singleton_iff, eq_comm]

theorem reverse_rotate (l : List α) (n : ℕ) :
    (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) := by
  rw [← length_reverse l, ← rotate_eq_iff]
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · rw [rotate_cons_succ, Nat.succ_eq_add_one, ← rotate_rotate, hn]
      simp

theorem rotate_reverse (l : List α) (n : ℕ) :
    l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse := by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse l]
  let k := n % l.reverse.length
  cases' hk' : k with k'
  · simp_all! [length_reverse, ← rotate_rotate]
  · cases' l with x l
    · simp
    · rw [Nat.mod_eq_of_lt, tsub_add_cancel_of_le, rotate_length]
      · exact tsub_le_self
      · exact tsub_lt_self (by simp) (by simp_all!)

theorem map_rotate {β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    map f (l.rotate n) = (map f l).rotate n := by
  induction' n with n hn IH generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · simp [hn]

set_option linter.deprecated false in
theorem Nodup.rotate_eq_self_iff {l : List α} (hl : l.Nodup) {n : ℕ} :
    l.rotate n = l ↔ n % l.length = 0 ∨ l = [] := by
  constructor
  · intro h
    cases' l.length.zero_le.eq_or_lt with hl' hl'
    · simp [← length_eq_zero, ← hl']
    left
    rw [nodup_iff_nthLe_inj] at hl
    refine' hl _ _ (mod_lt _ hl') hl' _
    rw [← nthLe_rotate' _ n]
    simp_rw [h, tsub_add_cancel_of_le (mod_lt _ hl').le, mod_self]
  · rintro (h | h)
    · rw [← rotate_mod, h]
      exact rotate_zero l
    · simp [h]

set_option linter.deprecated false in
theorem Nodup.rotate_congr {l : List α} (hl : l.Nodup) (hn : l ≠ []) (i j : ℕ)
    (h : l.rotate i = l.rotate j) : i % l.length = j % l.length := by
  have hi : i % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn)
  have hj : j % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn)
  refine' (nodup_iff_nthLe_inj.mp hl) _ _ hi hj _
  rw [← nthLe_rotate' l i, ← nthLe_rotate' l j]
  simp [tsub_add_cancel_of_le, hi.le, hj.le, h]

section IsRotated

variable (l l' : List α)

/-- `IsRotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
def IsRotated : Prop :=
  ∃ n, l.rotate n = l'

@[inherit_doc List.IsRotated]
infixr:1000 " ~r " => IsRotated

variable {l l'}

@[refl]
theorem IsRotated.refl (l : List α) : l ~r l :=
  ⟨0, by simp⟩

@[symm]
theorem IsRotated.symm (h : l ~r l') : l' ~r l := by
  obtain ⟨n, rfl⟩ := h
  cases' l with hd tl
  · exists 0
  · use (hd :: tl).length * n - n
    rw [rotate_rotate, add_tsub_cancel_of_le, rotate_length_mul]
    exact Nat.le_mul_of_pos_left (by simp)

theorem isRotated_comm : l ~r l' ↔ l' ~r l :=
  ⟨IsRotated.symm, IsRotated.symm⟩

@[simp]
protected theorem IsRotated.forall (l : List α) (n : ℕ) : l.rotate n ~r l :=
  IsRotated.symm ⟨n, rfl⟩

@[trans]
theorem IsRotated.trans : ∀ {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''
  | _, _, _, ⟨n, rfl⟩, ⟨m, rfl⟩ => ⟨n + m, by rw [rotate_rotate]⟩

theorem IsRotated.eqv : Equivalence (@IsRotated α) :=
  Equivalence.mk IsRotated.refl IsRotated.symm IsRotated.trans

/-- The relation `List.IsRotated l l'` forms a `Setoid` of cycles. -/
def IsRotated.setoid (α : Type*) : Setoid (List α) where
  r := IsRotated
  iseqv := IsRotated.eqv

theorem IsRotated.perm (h : l ~r l') : l ~ l' :=
  Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm

theorem IsRotated.nodup_iff (h : l ~r l') : Nodup l ↔ Nodup l' :=
  h.perm.nodup_iff

theorem IsRotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
  h.perm.mem_iff

@[simp]
theorem isRotated_nil_iff : l ~r [] ↔ l = [] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
theorem isRotated_nil_iff' : [] ~r l ↔ [] = l := by
  rw [isRotated_comm, isRotated_nil_iff, eq_comm]

@[simp]
theorem isRotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
theorem isRotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l := by
  rw [isRotated_comm, isRotated_singleton_iff, eq_comm]

theorem isRotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl) :=
  IsRotated.symm ⟨1, by simp⟩

theorem isRotated_append : (l ++ l') ~r (l' ++ l) :=
  ⟨l.length, by simp⟩

theorem IsRotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩

theorem isRotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse := by
  constructor <;>
    · intro h
      simpa using h.reverse

@[simp]
theorem isRotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l' := by
  simp [isRotated_reverse_comm_iff]

theorem isRotated_iff_mod : l ~r l' ↔ ∃ n ≤ l.length, l.rotate n = l' := by
  refine' ⟨fun h => _, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  cases' l with hd tl
  · simp
  · refine' ⟨n % (hd :: tl).length, _, rotate_mod _ _⟩
    refine' (Nat.mod_lt _ _).le
    simp

theorem isRotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (List.range (l.length + 1)).map l.rotate := by
  simp_rw [mem_map, mem_range, isRotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩,
      fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩

-- Porting note: @[congr] only works for equality.
-- @[congr]
theorem IsRotated.map {β : Type*} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α → β) :
    map f l₁ ~r map f l₂ := by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n

/-- List of all cyclic permutations of `l`.
The `cyclicPermutations` of a nonempty list `l` will always contain `List.length l` elements.
This implies that under certain conditions, there are duplicates in `List.cyclicPermutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `List.nthLe_cyclicPermutations`.
The proof that every cyclic permutant of `l` is in the list is `List.mem_cyclicPermutations_iff`.

     cyclicPermutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]] -/
def cyclicPermutations : List α → List (List α)
  | [] => [[]]
  | l@(_ :: _) => dropLast (zipWith (· ++ ·) (tails l) (inits l))

@[simp]
theorem cyclicPermutations_nil : cyclicPermutations ([] : List α) = [[]] :=
  rfl

theorem cyclicPermutations_cons (x : α) (l : List α) :
    cyclicPermutations (x :: l) = dropLast (zipWith (· ++ ·) (tails (x :: l)) (inits (x :: l))) :=
  rfl

theorem cyclicPermutations_of_ne_nil (l : List α) (h : l ≠ []) :
    cyclicPermutations l = dropLast (zipWith (· ++ ·) (tails l) (inits l)) := by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclicPermutations_cons _ _

theorem length_cyclicPermutations_cons (x : α) (l : List α) :
    length (cyclicPermutations (x :: l)) = length l + 1 := by simp [cyclicPermutations_cons]

@[simp]
theorem length_cyclicPermutations_of_ne_nil (l : List α) (h : l ≠ []) :
    length (cyclicPermutations l) = length l := by simp [cyclicPermutations_of_ne_nil _ h]

set_option linter.deprecated false in
@[simp]
theorem nthLe_cyclicPermutations (l : List α) (n : ℕ) (hn : n < length (cyclicPermutations l)) :
    nthLe (cyclicPermutations l) n hn = l.rotate n := by
  obtain rfl | h := eq_or_ne l []
  · simp
  · rw [length_cyclicPermutations_of_ne_nil _ h] at hn
    simp [dropLast_eq_take, cyclicPermutations_of_ne_nil _ h, nthLe_take',
      rotate_eq_drop_append_take hn.le]

set_option linter.deprecated false in
theorem mem_cyclicPermutations_self (l : List α) : l ∈ cyclicPermutations l := by
  cases' l with x l
  · simp
  · rw [mem_iff_nthLe]
    refine' ⟨0, by simp, _⟩
    simp

set_option linter.deprecated false in
theorem length_mem_cyclicPermutations (l : List α) (h : l' ∈ cyclicPermutations l) :
    length l' = length l := by
  obtain ⟨k, hk, rfl⟩ := nthLe_of_mem h
  simp

set_option linter.deprecated false in
@[simp]
theorem mem_cyclicPermutations_iff {l l' : List α} : l ∈ cyclicPermutations l' ↔ l ~r l' := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := nthLe_of_mem h
    simp
  · intro h
    obtain ⟨k, rfl⟩ := h.symm
    rw [mem_iff_nthLe]
    simp only [exists_prop, nthLe_cyclicPermutations]
    cases' l' with x l
    · simp
    · refine' ⟨k % length (x :: l), _, rotate_mod _ _⟩
      simpa using Nat.mod_lt _ (zero_lt_succ _)

@[simp]
theorem cyclicPermutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔ l = [] := by
  refine' ⟨fun h => _, fun h => by simp [h]⟩
  rw [eq_comm, ← isRotated_nil_iff', ← mem_cyclicPermutations_iff, h, mem_singleton]

@[simp]
theorem cyclicPermutations_eq_singleton_iff {l : List α} {x : α} :
    cyclicPermutations l = [[x]] ↔ l = [x] := by
  refine' ⟨fun h => _, fun h => by simp [cyclicPermutations, h, dropLast_eq_take]⟩
  rw [eq_comm, ← isRotated_singleton_iff', ← mem_cyclicPermutations_iff, h, mem_singleton]

set_option linter.deprecated false in
/-- If a `l : List α` is `Nodup l`, then all of its cyclic permutants are distinct. -/
theorem Nodup.cyclicPermutations {l : List α} (hn : Nodup l) : Nodup (cyclicPermutations l) := by
  cases' l with x l
  · simp
  rw [nodup_iff_nthLe_inj]
  intro i j hi hj h
  simp only [length_cyclicPermutations_cons] at hi hj
  rw [← mod_eq_of_lt hi, ← mod_eq_of_lt hj]
  apply hn.rotate_congr
  · simp
  · simpa using h

set_option linter.deprecated false in
@[simp]
theorem cyclicPermutations_rotate (l : List α) (k : ℕ) :
    (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k := by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclicPermutations.rotate k) := by
    cases l
    · simp
    · rw [length_cyclicPermutations_of_ne_nil] <;> simp
  refine' ext_nthLe this fun n hn hn' => _
  rw [nthLe_rotate, nthLe_cyclicPermutations, rotate_rotate, ← rotate_mod, add_comm]
  cases l <;> simp

theorem IsRotated.cyclicPermutations {l l' : List α} (h : l ~r l') :
    l.cyclicPermutations ~r l'.cyclicPermutations := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

set_option linter.deprecated false in
@[simp]
theorem isRotated_cyclicPermutations_iff {l l' : List α} :
    l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l' := by
  by_cases hl : l = []
  · simp [hl, eq_comm]
  have hl' : l.cyclicPermutations.length = l.length := length_cyclicPermutations_of_ne_nil _ hl
  refine' ⟨fun h => _, IsRotated.cyclicPermutations⟩
  obtain ⟨k, hk⟩ := h
  refine' ⟨k % l.length, _⟩
  have hk' : k % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hl)
  rw [← nthLe_cyclicPermutations _ _ (hk'.trans_le hl'.ge), ← nthLe_rotate' _ k]
  simp [hk, hl', tsub_add_cancel_of_le hk'.le]

section Decidable

variable [DecidableEq α]

instance isRotatedDecidable (l l' : List α) : Decidable (l ~r l') :=
  decidable_of_iff' _ isRotated_iff_mem_map_range

instance {l l' : List α} : Decidable (@Setoid.r _ (IsRotated.setoid α) l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List
