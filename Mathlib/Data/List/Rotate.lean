/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky

! This file was ported from Lean 3 source module data.list.rotate
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Perm
import Mathbin.Data.List.Range

/-!
# List rotation

This file proves basic results about `list.rotate`, the list rotation.

## Main declarations

* `is_rotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `cyclic_permutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/


universe u

variable {α : Type u}

open Nat

namespace List

theorem rotate_mod (l : List α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n := by simp [rotate]
#align list.rotate_mod List.rotate_mod

@[simp]
theorem rotate_nil (n : ℕ) : ([] : List α).rotate n = [] := by simp [rotate]
#align list.rotate_nil List.rotate_nil

@[simp]
theorem rotate_zero (l : List α) : l.rotate 0 = l := by simp [rotate]
#align list.rotate_zero List.rotate_zero

@[simp]
theorem rotate'_nil (n : ℕ) : ([] : List α).rotate' n = [] := by cases n <;> rfl
#align list.rotate'_nil List.rotate'_nil

@[simp]
theorem rotate'_zero (l : List α) : l.rotate' 0 = l := by cases l <;> rfl
#align list.rotate'_zero List.rotate'_zero

theorem rotate'_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']
#align list.rotate'_cons_succ List.rotate'_cons_succ

@[simp]
theorem length_rotate' : ∀ (l : List α) (n : ℕ), (l.rotate' n).length = l.length
  | [], n => rfl
  | a :: l, 0 => rfl
  | a :: l, n + 1 => by rw [List.rotate', length_rotate' (l ++ [a]) n] <;> simp
#align list.length_rotate' List.length_rotate'

theorem rotate'_eq_drop_append_take :
    ∀ {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = l.drop n ++ l.take n
  | [], n, h => by simp [drop_append_of_le_length h]
  | l, 0, h => by simp [take_append_of_le_length h]
  | a :: l, n + 1, h => by
    have hnl : n ≤ l.length := le_of_succ_le_succ h
    have hnl' : n ≤ (l ++ [a]).length := by
      rw [length_append, length_cons, List.length, zero_add] <;> exact le_of_succ_le h
    rw [rotate'_cons_succ, rotate'_eq_drop_append_take hnl', drop, take,
        drop_append_of_le_length hnl, take_append_of_le_length hnl] <;>
      simp
#align list.rotate'_eq_drop_append_take List.rotate'_eq_drop_append_take

theorem rotate'_rotate' : ∀ (l : List α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
  | a :: l, 0, m => by simp
  | [], n, m => by simp
  | a :: l, n + 1, m => by
    rw [rotate'_cons_succ, rotate'_rotate', add_right_comm, rotate'_cons_succ]
#align list.rotate'_rotate' List.rotate'_rotate'

@[simp]
theorem rotate'_length (l : List α) : rotate' l l.length = l := by
  rw [rotate'_eq_drop_append_take le_rfl] <;> simp
#align list.rotate'_length List.rotate'_length

@[simp]
theorem rotate'_length_mul (l : List α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
  | 0 => by simp
  | n + 1 =>
    calc
      l.rotate' (l.length * (n + 1)) =
          (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length :=
        by simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul]
      
#align list.rotate'_length_mul List.rotate'_length_mul

theorem rotate'_mod (l : List α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
  calc
    l.rotate' (n % l.length) =
        (l.rotate' (n % l.length)).rotate' ((l.rotate' (n % l.length)).length * (n / l.length)) :=
      by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]
    
#align list.rotate'_mod List.rotate'_mod

theorem rotate_eq_rotate' (l : List α) (n : ℕ) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then by simp_all [length_eq_zero]
  else by
    rw [← rotate'_mod,
        rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))] <;>
      simp [rotate]
#align list.rotate_eq_rotate' List.rotate_eq_rotate'

theorem rotate_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate n.succ = (l ++ [a]).rotate n := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]
#align list.rotate_cons_succ List.rotate_cons_succ

@[simp]
theorem mem_rotate : ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
  | [], _, n => by simp
  | a :: l, _, 0 => by simp
  | a :: l, _, n + 1 => by simp [rotate_cons_succ, mem_rotate, or_comm]
#align list.mem_rotate List.mem_rotate

@[simp]
theorem length_rotate (l : List α) (n : ℕ) : (l.rotate n).length = l.length := by
  rw [rotate_eq_rotate', length_rotate']
#align list.length_rotate List.length_rotate

theorem rotate_eq_drop_append_take {l : List α} {n : ℕ} :
    n ≤ l.length → l.rotate n = l.drop n ++ l.take n := by
  rw [rotate_eq_rotate'] <;> exact rotate'_eq_drop_append_take
#align list.rotate_eq_drop_append_take List.rotate_eq_drop_append_take

theorem rotate_eq_drop_append_take_mod {l : List α} {n : ℕ} :
    l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) :=
  by
  cases' l.length.zero_le.eq_or_lt with hl hl
  · simp [eq_nil_of_length_eq_zero hl.symm]
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le, rotate_mod]
#align list.rotate_eq_drop_append_take_mod List.rotate_eq_drop_append_take_mod

@[simp]
theorem rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' ++ l :=
  by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
  · simp [rotate', l_ih]
#align list.rotate_append_length_eq List.rotate_append_length_eq

theorem rotate_rotate (l : List α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n + m) := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']
#align list.rotate_rotate List.rotate_rotate

@[simp]
theorem rotate_length (l : List α) : rotate l l.length = l := by
  rw [rotate_eq_rotate', rotate'_length]
#align list.rotate_length List.rotate_length

@[simp]
theorem rotate_length_mul (l : List α) (n : ℕ) : l.rotate (l.length * n) = l := by
  rw [rotate_eq_rotate', rotate'_length_mul]
#align list.rotate_length_mul List.rotate_length_mul

theorem prod_rotate_eq_one_of_prod_eq_one [Group α] :
    ∀ {l : List α} (hl : l.Prod = 1) (n : ℕ), (l.rotate n).Prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n =>
    by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by decide))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl <;>
      rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq, ←
        one_mul (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_self, mul_one]
#align list.prod_rotate_eq_one_of_prod_eq_one List.prod_rotate_eq_one_of_prod_eq_one

theorem rotate_perm (l : List α) (n : ℕ) : l.rotate n ~ l :=
  by
  rw [rotate_eq_rotate']
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)
#align list.rotate_perm List.rotate_perm

@[simp]
theorem nodup_rotate {l : List α} {n : ℕ} : Nodup (l.rotate n) ↔ Nodup l :=
  (rotate_perm l n).nodup_iff
#align list.nodup_rotate List.nodup_rotate

@[simp]
theorem rotate_eq_nil_iff {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] :=
  by
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · simp [rotate_cons_succ, hn]
#align list.rotate_eq_nil_iff List.rotate_eq_nil_iff

@[simp]
theorem nil_eq_rotate_iff {l : List α} {n : ℕ} : [] = l.rotate n ↔ [] = l := by
  rw [eq_comm, rotate_eq_nil_iff, eq_comm]
#align list.nil_eq_rotate_iff List.nil_eq_rotate_iff

@[simp]
theorem rotate_singleton (x : α) (n : ℕ) : [x].rotate n = [x] :=
  by
  induction' n with n hn
  · simp
  · rwa [rotate_cons_succ]
#align list.rotate_singleton List.rotate_singleton

@[simp]
theorem rotate_eq_singleton_iff {l : List α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] :=
  by
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · simp [rotate_cons_succ, hn, append_eq_cons_iff, and_comm']
#align list.rotate_eq_singleton_iff List.rotate_eq_singleton_iff

@[simp]
theorem singleton_eq_rotate_iff {l : List α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l := by
  rw [eq_comm, rotate_eq_singleton_iff, eq_comm]
#align list.singleton_eq_rotate_iff List.singleton_eq_rotate_iff

theorem zip_with_rotate_distrib {α β γ : Type _} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)
    (h : l.length = l'.length) : (zipWith f l l').rotate n = zipWith f (l.rotate n) (l'.rotate n) :=
  by
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod,
    rotate_eq_drop_append_take_mod, h, zip_with_append, ← zip_with_distrib_drop, ←
    zip_with_distrib_take, List.length_zip_with, h, min_self]
  rw [length_drop, length_drop, h]
#align list.zip_with_rotate_distrib List.zip_with_rotate_distrib

attribute [local simp] rotate_cons_succ

@[simp]
theorem zip_with_rotate_one {β : Type _} (f : α → α → β) (x y : α) (l : List α) :
    zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (l ++ [x]) := by
  simp
#align list.zip_with_rotate_one List.zip_with_rotate_one

theorem nth_le_rotate_one (l : List α) (k : ℕ) (hk : k < (l.rotate 1).length) :
    (l.rotate 1).nthLe k hk =
      l.nthLe ((k + 1) % l.length) (mod_lt _ (length_rotate l 1 ▸ k.zero_le.trans_lt hk)) :=
  by
  cases' l with hd tl
  · simp
  · have : k ≤ tl.length := by
      refine' Nat.le_of_lt_succ _
      simpa using hk
    rcases this.eq_or_lt with (rfl | hk')
    · simp [nth_le_append_right le_rfl]
    · simpa [nth_le_append _ hk', length_cons, Nat.mod_eq_of_lt (Nat.succ_lt_succ hk')]
#align list.nth_le_rotate_one List.nth_le_rotate_one

theorem nth_le_rotate (l : List α) (n k : ℕ) (hk : k < (l.rotate n).length) :
    (l.rotate n).nthLe k hk =
      l.nthLe ((k + n) % l.length) (mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt hk)) :=
  by
  induction' n with n hn generalizing l k
  · have hk' : k < l.length := by simpa using hk
    simp [Nat.mod_eq_of_lt hk']
  · simp [Nat.succ_eq_add_one, ← rotate_rotate, nth_le_rotate_one, hn l, add_comm, add_left_comm]
#align list.nth_le_rotate List.nth_le_rotate

/-- A variant of `nth_le_rotate` useful for rewrites. -/
theorem nth_le_rotate' (l : List α) (n k : ℕ) (hk : k < l.length) :
    (l.rotate n).nthLe ((l.length - n % l.length + k) % l.length)
        ((Nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_le (length_rotate _ _).ge) =
      l.nthLe k hk :=
  by
  rw [nth_le_rotate]
  congr
  set m := l.length
  rw [mod_add_mod, add_assoc, add_left_comm, add_comm, add_mod, add_mod _ n]
  cases' (n % m).zero_le.eq_or_lt with hn hn
  · simpa [← hn] using Nat.mod_eq_of_lt hk
  · have mpos : 0 < m := k.zero_le.trans_lt hk
    have hm : m - n % m < m := tsub_lt_self mpos hn
    have hn' : n % m < m := Nat.mod_lt _ mpos
    simpa [mod_eq_of_lt hm, tsub_add_cancel_of_le hn'.le] using Nat.mod_eq_of_lt hk
#align list.nth_le_rotate' List.nth_le_rotate'

theorem rotate_injective (n : ℕ) : Function.Injective fun l : List α => l.rotate n :=
  by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h _
  · rw [← take_append_drop _ l, ht, hd, take_append_drop]
  · rw [length_drop, length_drop, hle]
#align list.rotate_injective List.rotate_injective

-- possibly easier to find in doc-gen, otherwise not that useful.
theorem rotate_eq_rotate {l l' : List α} {n : ℕ} : l.rotate n = l'.rotate n ↔ l = l' :=
  (rotate_injective n).eq_iff
#align list.rotate_eq_rotate List.rotate_eq_rotate

theorem rotate_eq_iff {l l' : List α} {n : ℕ} :
    l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) :=
  by
  rw [← @rotate_eq_rotate _ l _ n, rotate_rotate, ← rotate_mod l', add_mod]
  cases' l'.length.zero_le.eq_or_lt with hl hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil, rotate_eq_nil_iff]
  · cases' (Nat.zero_le (n % l'.length)).eq_or_lt with hn hn
    · simp [← hn]
    · rw [mod_eq_of_lt (tsub_lt_self hl hn), tsub_add_cancel_of_le, mod_self, rotate_zero]
      exact (Nat.mod_lt _ hl).le
#align list.rotate_eq_iff List.rotate_eq_iff

theorem reverse_rotate (l : List α) (n : ℕ) :
    (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) :=
  by
  rw [← length_reverse l, ← rotate_eq_iff]
  induction' n with n hn generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · rw [rotate_cons_succ, Nat.succ_eq_add_one, ← rotate_rotate, hn]
      simp
#align list.reverse_rotate List.reverse_rotate

theorem rotate_reverse (l : List α) (n : ℕ) :
    l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse :=
  by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse l]
  set k := n % l.reverse.length with hk
  cases' hk' : k with k'
  · simp [-length_reverse, ← rotate_rotate]
  · cases' l with x l
    · simp
    · have : k'.succ < (x :: l).length := by simp [← hk', hk, Nat.mod_lt]
      rw [Nat.mod_eq_of_lt, tsub_add_cancel_of_le, rotate_length]
      · exact tsub_le_self
      · exact tsub_lt_self (by simp) Nat.succ_pos'
#align list.rotate_reverse List.rotate_reverse

theorem map_rotate {β : Type _} (f : α → β) (l : List α) (n : ℕ) :
    map f (l.rotate n) = (map f l).rotate n :=
  by
  induction' n with n hn IH generalizing l
  · simp
  · cases' l with hd tl
    · simp
    · simp [hn]
#align list.map_rotate List.map_rotate

theorem Nodup.rotate_eq_self_iff {l : List α} (hl : l.Nodup) {n : ℕ} :
    l.rotate n = l ↔ n % l.length = 0 ∨ l = [] :=
  by
  constructor
  · intro h
    cases' l.length.zero_le.eq_or_lt with hl' hl'
    · simp [← length_eq_zero, ← hl']
    left
    rw [nodup_iff_nth_le_inj] at hl
    refine' hl _ _ (mod_lt _ hl') hl' _
    rw [← nth_le_rotate' _ n]
    simp_rw [h, tsub_add_cancel_of_le (mod_lt _ hl').le, mod_self]
  · rintro (h | h)
    · rw [← rotate_mod, h]
      exact rotate_zero l
    · simp [h]
#align list.nodup.rotate_eq_self_iff List.Nodup.rotate_eq_self_iff

theorem Nodup.rotate_congr {l : List α} (hl : l.Nodup) (hn : l ≠ []) (i j : ℕ)
    (h : l.rotate i = l.rotate j) : i % l.length = j % l.length :=
  by
  have hi : i % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn)
  have hj : j % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn)
  refine' (nodup_iff_nth_le_inj.mp hl) _ _ hi hj _
  rw [← nth_le_rotate' l i, ← nth_le_rotate' l j]
  simp [tsub_add_cancel_of_le, hi.le, hj.le, h]
#align list.nodup.rotate_congr List.Nodup.rotate_congr

section IsRotated

variable (l l' : List α)

/-- `is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
def IsRotated : Prop :=
  ∃ n, l.rotate n = l'
#align list.is_rotated List.IsRotated

-- mathport name: «expr ~r »
infixr:1000 " ~r " => IsRotated

variable {l l'}

@[refl]
theorem IsRotated.refl (l : List α) : l ~r l :=
  ⟨0, by simp⟩
#align list.is_rotated.refl List.IsRotated.refl

@[symm]
theorem IsRotated.symm (h : l ~r l') : l' ~r l :=
  by
  obtain ⟨n, rfl⟩ := h
  cases' l with hd tl
  · simp
  · use (hd :: tl).length * n - n
    rw [rotate_rotate, add_tsub_cancel_of_le, rotate_length_mul]
    exact Nat.le_mul_of_pos_left (by simp)
#align list.is_rotated.symm List.IsRotated.symm

theorem is_rotated_comm : l ~r l' ↔ l' ~r l :=
  ⟨IsRotated.symm, IsRotated.symm⟩
#align list.is_rotated_comm List.is_rotated_comm

@[simp]
protected theorem IsRotated.forall (l : List α) (n : ℕ) : l.rotate n ~r l :=
  IsRotated.symm ⟨n, rfl⟩
#align list.is_rotated.forall List.IsRotated.forall

@[trans]
theorem IsRotated.trans : ∀ {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''
  | _, _, _, ⟨n, rfl⟩, ⟨m, rfl⟩ => ⟨n + m, by rw [rotate_rotate]⟩
#align list.is_rotated.trans List.IsRotated.trans

theorem IsRotated.eqv : Equivalence (@IsRotated α) :=
  Equivalence.mk _ IsRotated.refl (fun _ _ => IsRotated.symm) fun _ _ _ => IsRotated.trans
#align list.is_rotated.eqv List.IsRotated.eqv

/-- The relation `list.is_rotated l l'` forms a `setoid` of cycles. -/
def IsRotated.setoid (α : Type _) : Setoid (List α)
    where
  R := IsRotated
  iseqv := IsRotated.eqv
#align list.is_rotated.setoid List.IsRotated.setoid

theorem IsRotated.perm (h : l ~r l') : l ~ l' :=
  Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm
#align list.is_rotated.perm List.IsRotated.perm

theorem IsRotated.nodup_iff (h : l ~r l') : Nodup l ↔ Nodup l' :=
  h.Perm.nodup_iff
#align list.is_rotated.nodup_iff List.IsRotated.nodup_iff

theorem IsRotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
  h.Perm.mem_iff
#align list.is_rotated.mem_iff List.IsRotated.mem_iff

@[simp]
theorem is_rotated_nil_iff : l ~r [] ↔ l = [] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩
#align list.is_rotated_nil_iff List.is_rotated_nil_iff

@[simp]
theorem is_rotated_nil_iff' : [] ~r l ↔ [] = l := by
  rw [is_rotated_comm, is_rotated_nil_iff, eq_comm]
#align list.is_rotated_nil_iff' List.is_rotated_nil_iff'

@[simp]
theorem is_rotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩
#align list.is_rotated_singleton_iff List.is_rotated_singleton_iff

@[simp]
theorem is_rotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l := by
  rw [is_rotated_comm, is_rotated_singleton_iff, eq_comm]
#align list.is_rotated_singleton_iff' List.is_rotated_singleton_iff'

theorem is_rotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl) :=
  IsRotated.symm ⟨1, by simp⟩
#align list.is_rotated_concat List.is_rotated_concat

theorem is_rotated_append : (l ++ l') ~r (l' ++ l) :=
  ⟨l.length, by simp⟩
#align list.is_rotated_append List.is_rotated_append

theorem IsRotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse :=
  by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩
#align list.is_rotated.reverse List.IsRotated.reverse

theorem is_rotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse := by
  constructor <;>
    · intro h
      simpa using h.reverse
#align list.is_rotated_reverse_comm_iff List.is_rotated_reverse_comm_iff

@[simp]
theorem is_rotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l' := by
  simp [is_rotated_reverse_comm_iff]
#align list.is_rotated_reverse_iff List.is_rotated_reverse_iff

theorem is_rotated_iff_mod : l ~r l' ↔ ∃ n ≤ l.length, l.rotate n = l' :=
  by
  refine' ⟨fun h => _, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  cases' l with hd tl
  · simp
  · refine' ⟨n % (hd :: tl).length, _, rotate_mod _ _⟩
    refine' (Nat.mod_lt _ _).le
    simp
#align list.is_rotated_iff_mod List.is_rotated_iff_mod

theorem is_rotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (List.range (l.length + 1)).map l.rotate :=
  by
  simp_rw [mem_map, mem_range, is_rotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩, fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩
#align list.is_rotated_iff_mem_map_range List.is_rotated_iff_mem_map_range

@[congr]
theorem IsRotated.map {β : Type _} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α → β) :
    map f l₁ ~r map f l₂ := by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n
#align list.is_rotated.map List.IsRotated.map

/-- List of all cyclic permutations of `l`.
The `cyclic_permutations` of a nonempty list `l` will always contain `list.length l` elements.
This implies that under certain conditions, there are duplicates in `list.cyclic_permutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `list.nth_le_cyclic_permutations`.
The proof that every cyclic permutant of `l` is in the list is `list.mem_cyclic_permutations_iff`.

     cyclic_permutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]] -/
def cyclicPermutations : List α → List (List α)
  | [] => [[]]
  | l@(_ :: _) => dropLast (zipWith (· ++ ·) (tails l) (inits l))
#align list.cyclic_permutations List.cyclicPermutations

@[simp]
theorem cyclic_permutations_nil : cyclicPermutations ([] : List α) = [[]] :=
  rfl
#align list.cyclic_permutations_nil List.cyclic_permutations_nil

theorem cyclic_permutations_cons (x : α) (l : List α) :
    cyclicPermutations (x :: l) = dropLast (zipWith (· ++ ·) (tails (x :: l)) (inits (x :: l))) :=
  rfl
#align list.cyclic_permutations_cons List.cyclic_permutations_cons

theorem cyclic_permutations_of_ne_nil (l : List α) (h : l ≠ []) :
    cyclicPermutations l = dropLast (zipWith (· ++ ·) (tails l) (inits l)) :=
  by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclic_permutations_cons _ _
#align list.cyclic_permutations_of_ne_nil List.cyclic_permutations_of_ne_nil

theorem length_cyclic_permutations_cons (x : α) (l : List α) :
    length (cyclicPermutations (x :: l)) = length l + 1 := by simp [cyclic_permutations_of_ne_nil]
#align list.length_cyclic_permutations_cons List.length_cyclic_permutations_cons

@[simp]
theorem length_cyclic_permutations_of_ne_nil (l : List α) (h : l ≠ []) :
    length (cyclicPermutations l) = length l := by simp [cyclic_permutations_of_ne_nil _ h]
#align list.length_cyclic_permutations_of_ne_nil List.length_cyclic_permutations_of_ne_nil

@[simp]
theorem nth_le_cyclic_permutations (l : List α) (n : ℕ) (hn : n < length (cyclicPermutations l)) :
    nthLe (cyclicPermutations l) n hn = l.rotate n :=
  by
  obtain rfl | h := eq_or_ne l []
  · simp
  · rw [length_cyclic_permutations_of_ne_nil _ h] at hn
    simp [init_eq_take, cyclic_permutations_of_ne_nil _ h, nth_le_take',
      rotate_eq_drop_append_take hn.le]
#align list.nth_le_cyclic_permutations List.nth_le_cyclic_permutations

theorem mem_cyclic_permutations_self (l : List α) : l ∈ cyclicPermutations l :=
  by
  cases' l with x l
  · simp
  · rw [mem_iff_nth_le]
    refine' ⟨0, by simp, _⟩
    simp
#align list.mem_cyclic_permutations_self List.mem_cyclic_permutations_self

theorem length_mem_cyclic_permutations (l : List α) (h : l' ∈ cyclicPermutations l) :
    length l' = length l := by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h
  simp
#align list.length_mem_cyclic_permutations List.length_mem_cyclic_permutations

@[simp]
theorem mem_cyclic_permutations_iff {l l' : List α} : l ∈ cyclicPermutations l' ↔ l ~r l' :=
  by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h
    simp
  · intro h
    obtain ⟨k, rfl⟩ := h.symm
    rw [mem_iff_nth_le]
    simp only [exists_prop, nth_le_cyclic_permutations]
    cases' l' with x l
    · simp
    · refine' ⟨k % length (x :: l), _, rotate_mod _ _⟩
      simpa using Nat.mod_lt _ (zero_lt_succ _)
#align list.mem_cyclic_permutations_iff List.mem_cyclic_permutations_iff

@[simp]
theorem cyclic_permutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔ l = [] :=
  by
  refine' ⟨fun h => _, fun h => by simp [h]⟩
  rw [eq_comm, ← is_rotated_nil_iff', ← mem_cyclic_permutations_iff, h, mem_singleton]
#align list.cyclic_permutations_eq_nil_iff List.cyclic_permutations_eq_nil_iff

@[simp]
theorem cyclic_permutations_eq_singleton_iff {l : List α} {x : α} :
    cyclicPermutations l = [[x]] ↔ l = [x] :=
  by
  refine' ⟨fun h => _, fun h => by simp [cyclic_permutations, h, init_eq_take]⟩
  rw [eq_comm, ← is_rotated_singleton_iff', ← mem_cyclic_permutations_iff, h, mem_singleton]
#align list.cyclic_permutations_eq_singleton_iff List.cyclic_permutations_eq_singleton_iff

/-- If a `l : list α` is `nodup l`, then all of its cyclic permutants are distinct. -/
theorem Nodup.cyclic_permutations {l : List α} (hn : Nodup l) : Nodup (cyclicPermutations l) :=
  by
  cases' l with x l
  · simp
  rw [nodup_iff_nth_le_inj]
  intro i j hi hj h
  simp only [length_cyclic_permutations_cons] at hi hj
  rw [← mod_eq_of_lt hi, ← mod_eq_of_lt hj, ← length_cons x l]
  apply hn.rotate_congr
  · simp
  · simpa using h
#align list.nodup.cyclic_permutations List.Nodup.cyclic_permutations

@[simp]
theorem cyclic_permutations_rotate (l : List α) (k : ℕ) :
    (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k :=
  by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclic_permutations.rotate k) :=
    by
    cases l
    · simp
    · rw [length_cyclic_permutations_of_ne_nil] <;> simp
  refine' ext_le this fun n hn hn' => _
  rw [nth_le_cyclic_permutations, nth_le_rotate, nth_le_cyclic_permutations, rotate_rotate, ←
    rotate_mod, add_comm]
  cases l <;> simp
#align list.cyclic_permutations_rotate List.cyclic_permutations_rotate

theorem IsRotated.cyclic_permutations {l l' : List α} (h : l ~r l') :
    l.cyclicPermutations ~r l'.cyclicPermutations :=
  by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩
#align list.is_rotated.cyclic_permutations List.IsRotated.cyclic_permutations

@[simp]
theorem is_rotated_cyclic_permutations_iff {l l' : List α} :
    l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l' :=
  by
  by_cases hl : l = []
  · simp [hl, eq_comm]
  have hl' : l.cyclic_permutations.length = l.length := length_cyclic_permutations_of_ne_nil _ hl
  refine' ⟨fun h => _, is_rotated.cyclic_permutations⟩
  obtain ⟨k, hk⟩ := h
  refine' ⟨k % l.length, _⟩
  have hk' : k % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hl)
  rw [← nth_le_cyclic_permutations _ _ (hk'.trans_le hl'.ge), ← nth_le_rotate' _ k]
  simp [hk, hl', tsub_add_cancel_of_le hk'.le]
#align list.is_rotated_cyclic_permutations_iff List.is_rotated_cyclic_permutations_iff

section Decidable

variable [DecidableEq α]

instance isRotatedDecidable (l l' : List α) : Decidable (l ~r l') :=
  decidable_of_iff' _ is_rotated_iff_mem_map_range
#align list.is_rotated_decidable List.isRotatedDecidable

instance {l l' : List α} : Decidable (@Setoid.r _ (IsRotated.setoid α) l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List

