/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Infix
import Mathlib.Data.Quot

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

theorem rotate'_nil (n : ℕ) : ([] : List α).rotate' n = [] := by simp

@[simp]
theorem rotate'_zero (l : List α) : l.rotate' 0 = l := by cases l <;> rfl

theorem rotate'_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp]
theorem length_rotate' : ∀ (l : List α) (n : ℕ), (l.rotate' n).length = l.length
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | a :: l, n + 1 => by rw [List.rotate', length_rotate' (l ++ [a]) n]; simp

theorem rotate'_eq_drop_append_take :
    ∀ {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = l.drop n ++ l.take n
  | [], n, h => by simp
  | l, 0, h => by simp
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
    rw [rotate'_cons_succ, rotate'_rotate' _ n, Nat.add_right_comm, ← rotate'_cons_succ,
      Nat.succ_eq_add_one]

@[simp]
theorem rotate'_length (l : List α) : rotate' l l.length = l := by
  rw [rotate'_eq_drop_append_take le_rfl]; simp

@[simp]
theorem rotate'_length_mul (l : List α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
  | 0 => by simp
  | n + 1 =>
    calc
      l.rotate' (l.length * (n + 1)) =
          (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length := by
        simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul l n]

theorem rotate'_mod (l : List α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
  calc
    l.rotate' (n % l.length) =
        (l.rotate' (n % l.length)).rotate' ((l.rotate' (n % l.length)).length * (n / l.length)) :=
      by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]

theorem rotate_eq_rotate' (l : List α) (n : ℕ) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then by simp_all [length_eq_zero_iff]
  else by
    rw [← rotate'_mod,
        rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))]
    simp [rotate]

@[simp] theorem rotate_cons_succ (l : List α) (a : α) (n : ℕ) :
    (a :: l : List α).rotate (n + 1) = (l ++ [a]).rotate n := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp]
theorem mem_rotate : ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
  | [], _, n => by simp
  | a :: l, _, 0 => by simp
  | a :: l, _, n + 1 => by simp [rotate_cons_succ, mem_rotate, or_comm]

@[simp]
theorem length_rotate (l : List α) (n : ℕ) : (l.rotate n).length = l.length := by
  rw [rotate_eq_rotate', length_rotate']

@[simp]
theorem rotate_replicate (a : α) (n : ℕ) (k : ℕ) : (replicate n a).rotate k = replicate n a :=
  eq_replicate_iff.2 ⟨by rw [length_rotate, length_replicate], fun b hb =>
    eq_of_mem_replicate <| mem_rotate.1 hb⟩

theorem rotate_eq_drop_append_take {l : List α} {n : ℕ} :
    n ≤ l.length → l.rotate n = l.drop n ++ l.take n := by
  rw [rotate_eq_rotate']; exact rotate'_eq_drop_append_take

theorem rotate_eq_drop_append_take_mod {l : List α} {n : ℕ} :
    l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) := by
  rcases l.length.zero_le.eq_or_lt with hl | hl
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

theorem rotate_perm (l : List α) (n : ℕ) : l.rotate n ~ l := by
  rw [rotate_eq_rotate']
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)

@[simp]
theorem nodup_rotate {l : List α} {n : ℕ} : Nodup (l.rotate n) ↔ Nodup l :=
  (rotate_perm l n).nodup_iff

@[simp]
theorem rotate_eq_nil_iff {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] := by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [rotate_cons_succ, hn]

theorem nil_eq_rotate_iff {l : List α} {n : ℕ} : [] = l.rotate n ↔ [] = l := by
  rw [eq_comm, rotate_eq_nil_iff, eq_comm]

@[simp]
theorem rotate_singleton (x : α) (n : ℕ) : [x].rotate n = [x] :=
  rotate_replicate x 1 n

theorem zipWith_rotate_distrib {β γ : Type*} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)
    (h : l.length = l'.length) :
    (zipWith f l l').rotate n = zipWith f (l.rotate n) (l'.rotate n) := by
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod,
    rotate_eq_drop_append_take_mod, h, zipWith_append, ← drop_zipWith, ←
    take_zipWith, List.length_zipWith, h, min_self]
  rw [length_drop, length_drop, h]

theorem zipWith_rotate_one {β : Type*} (f : α → α → β) (x y : α) (l : List α) :
    zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (l ++ [x]) := by
  simp

theorem getElem?_rotate {l : List α} {n m : ℕ} (hml : m < l.length) :
    (l.rotate n)[m]? = l[(m + n) % l.length]? := by
  rw [rotate_eq_drop_append_take_mod]
  rcases lt_or_ge m (l.drop (n % l.length)).length with hm | hm
  · rw [getElem?_append_left hm, getElem?_drop, ← add_mod_mod]
    rw [length_drop, Nat.lt_sub_iff_add_lt] at hm
    rw [mod_eq_of_lt hm, Nat.add_comm]
  · have hlt : n % length l < length l := mod_lt _ (m.zero_le.trans_lt hml)
    rw [getElem?_append_right hm, getElem?_take_of_lt, length_drop]
    · congr 1
      rw [length_drop] at hm
      have hm' := Nat.sub_le_iff_le_add'.1 hm
      have : n % length l + m - length l < length l := by
        rw [Nat.sub_lt_iff_lt_add hm']
        exact Nat.add_lt_add hlt hml
      conv_rhs => rw [Nat.add_comm m, ← mod_add_mod, mod_eq_sub_mod hm', mod_eq_of_lt this]
      cutsat
    · rwa [Nat.sub_lt_iff_lt_add' hm, length_drop, Nat.sub_add_cancel hlt.le]

theorem getElem_rotate (l : List α) (n : ℕ) (k : Nat) (h : k < (l.rotate n).length) :
    (l.rotate n)[k] =
      l[(k + n) % l.length]'(mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt h)) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem, ← getElem?_eq_getElem, getElem?_rotate]
  exact h.trans_eq (length_rotate _ _)

theorem get_rotate (l : List α) (n : ℕ) (k : Fin (l.rotate n).length) :
    (l.rotate n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rotate l n ▸ k.pos)⟩ := by
  simp [getElem_rotate]

theorem head?_rotate {l : List α} {n : ℕ} (h : n < l.length) : head? (l.rotate n) = l[n]? := by
  rw [head?_eq_getElem?, getElem?_rotate (n.zero_le.trans_lt h), Nat.zero_add, Nat.mod_eq_of_lt h]

theorem get_rotate_one (l : List α) (k : Fin (l.rotate 1).length) :
    (l.rotate 1).get k = l.get ⟨(k + 1) % l.length, mod_lt _ (length_rotate l 1 ▸ k.pos)⟩ :=
  get_rotate l 1 k

-- Allow `l[a]'b` to have a line break between `[a]'` and `b`.
set_option linter.style.commandStart false in
/-- A version of `List.getElem_rotate` that represents `l[k]` in terms of
`(List.rotate l n)[⋯]`, not vice versa. Can be used instead of rewriting `List.getElem_rotate`
from right to left. -/
theorem getElem_eq_getElem_rotate (l : List α) (n : ℕ) (k : Nat) (hk : k < l.length) :
    l[k] = ((l.rotate n)[(l.length - n % l.length + k) % l.length]'
      ((Nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_eq (length_rotate _ _).symm)) := by
  rw [getElem_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod, Nat.add_right_comm, Nat.sub_add_cancel, add_mod_left, mod_eq_of_lt]
  exacts [hk, (mod_lt _ (k.zero_le.trans_lt hk)).le]

/-- A version of `List.get_rotate` that represents `List.get l` in terms of
`List.get (List.rotate l n)`, not vice versa. Can be used instead of rewriting `List.get_rotate`
from right to left. -/
theorem get_eq_get_rotate (l : List α) (n : ℕ) (k : Fin l.length) :
    l.get k = (l.rotate n).get ⟨(l.length - n % l.length + k) % l.length,
      (Nat.mod_lt _ (k.1.zero_le.trans_lt k.2)).trans_eq (length_rotate _ _).symm⟩ := by
  rw [get_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod, Nat.add_right_comm, Nat.sub_add_cancel, add_mod_left, mod_eq_of_lt]
  exacts [k.2, (mod_lt _ (k.1.zero_le.trans_lt k.2)).le]

theorem rotate_eq_self_iff_eq_replicate [hα : Nonempty α] :
    ∀ {l : List α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = replicate l.length a
  | [] => by simp
  | a :: l => ⟨fun h => ⟨a, ext_getElem length_replicate.symm fun n h₁ h₂ => by
      rw [getElem_replicate, ← Option.some_inj, ← getElem?_eq_getElem, ← head?_rotate h₁, h,
        head?_cons]⟩,
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
  rcases l'.length.zero_le.eq_or_lt with hl | hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil]
  · rcases (Nat.zero_le (n % l'.length)).eq_or_lt with hn | hn
    · simp [← hn]
    · rw [mod_eq_of_lt (Nat.sub_lt hl hn), Nat.sub_add_cancel, mod_self, rotate_zero]
      exact (Nat.mod_lt _ hl).le

@[simp]
theorem rotate_eq_singleton_iff {l : List α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] := by
  rw [rotate_eq_iff, rotate_singleton]

@[simp]
theorem singleton_eq_rotate_iff {l : List α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l := by
  rw [eq_comm, rotate_eq_singleton_iff, eq_comm]

theorem reverse_rotate (l : List α) (n : ℕ) :
    (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) := by
  rw [← length_reverse, ← rotate_eq_iff]
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate_cons_succ, ← rotate_rotate, hn]
      simp

theorem rotate_reverse (l : List α) (n : ℕ) :
    l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse := by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse]
  let k := n % l.reverse.length
  rcases hk' : k with - | k'
  · simp_all! [k, length_reverse, ← rotate_rotate]
  · rcases l with - | ⟨x, l⟩
    · simp
    · rw [Nat.mod_eq_of_lt, Nat.sub_add_cancel, rotate_length]
      · exact Nat.sub_le _ _
      · exact Nat.sub_lt (by simp) (by simp_all! [k])

theorem map_rotate {β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    map f (l.rotate n) = (map f l).rotate n := by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [hn]

theorem Nodup.rotate_congr {l : List α} (hl : l.Nodup) (hn : l ≠ []) (i j : ℕ)
    (h : l.rotate i = l.rotate j) : i % l.length = j % l.length := by
  rw [← rotate_mod l i, ← rotate_mod l j] at h
  simpa only [head?_rotate, mod_lt, length_pos_of_ne_nil hn, getElem?_eq_getElem, Option.some_inj,
    hl.getElem_inj_iff, Fin.ext_iff] using congr_arg head? h

theorem Nodup.rotate_congr_iff {l : List α} (hl : l.Nodup) {i j : ℕ} :
    l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = [] := by
  rcases eq_or_ne l [] with rfl | hn
  · simp
  · simp only [hn, or_false]
    refine ⟨hl.rotate_congr hn _ _, fun h ↦ ?_⟩
    rw [← rotate_mod, h, rotate_mod]

theorem Nodup.rotate_eq_self_iff {l : List α} (hl : l.Nodup) {n : ℕ} :
    l.rotate n = l ↔ n % l.length = 0 ∨ l = [] := by
  rw [← zero_mod, ← hl.rotate_congr_iff, rotate_zero]

section IsRotated

variable (l l' : List α)

/-- `IsRotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
def IsRotated : Prop :=
  ∃ n, l.rotate n = l'

@[inherit_doc List.IsRotated]
-- This matches the precedence of the infix `~` for `List.Perm`, and of other relation infixes
infixr:50 " ~r " => IsRotated

variable {l l'}

@[refl]
theorem IsRotated.refl (l : List α) : l ~r l :=
  ⟨0, by simp⟩

@[symm]
theorem IsRotated.symm (h : l ~r l') : l' ~r l := by
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · exists 0
  · use (hd :: tl).length * n - n
    rw [rotate_rotate, Nat.add_sub_cancel', rotate_length_mul]
    exact Nat.le_mul_of_pos_left _ (by simp)

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
  refine ⟨fun h => ?_, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · simp
  · refine ⟨n % (hd :: tl).length, ?_, rotate_mod _ _⟩
    refine (Nat.mod_lt _ ?_).le
    simp

theorem isRotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (List.range (l.length + 1)).map l.rotate := by
  simp_rw [mem_map, mem_range, isRotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩,
      fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩

theorem IsRotated.map {β : Type*} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α → β) :
    map f l₁ ~r map f l₂ := by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n

theorem IsRotated.cons_getLast_dropLast
    (L : List α) (hL : L ≠ []) : L.getLast hL :: L.dropLast ~r L := by
  induction L using List.reverseRecOn with
  | nil => simp at hL
  | append_singleton a L _ =>
    simp only [getLast_append, dropLast_concat]
    apply IsRotated.symm
    apply isRotated_concat

theorem IsRotated.dropLast_tail {α}
    {L : List α} (hL : L ≠ []) (hL' : L.head hL = L.getLast hL) : L.dropLast ~r L.tail :=
  match L with
  | [] => by simp
  | [_] => by simp
  | a :: b :: L => by
    simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons] at hL'
    simp [hL', IsRotated.cons_getLast_dropLast]

/-- List of all cyclic permutations of `l`.
The `cyclicPermutations` of a nonempty list `l` will always contain `List.length l` elements.
This implies that under certain conditions, there are duplicates in `List.cyclicPermutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `List.get_cyclicPermutations`.
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

@[simp]
theorem cyclicPermutations_ne_nil : ∀ l : List α, cyclicPermutations l ≠ []
  | a::l, h => by simpa using congr_arg length h

@[simp]
theorem getElem_cyclicPermutations (l : List α) (n : Nat) (h : n < length (cyclicPermutations l)) :
    (cyclicPermutations l)[n] = l.rotate n := by
  cases l with
  | nil => simp
  | cons a l =>
    simp only [cyclicPermutations_cons, getElem_dropLast, getElem_zipWith, getElem_tails,
      getElem_inits]
    rw [rotate_eq_drop_append_take (by simpa using h.le)]

theorem get_cyclicPermutations (l : List α) (n : Fin (length (cyclicPermutations l))) :
    (cyclicPermutations l).get n = l.rotate n := by
  simp

@[simp]
theorem head_cyclicPermutations (l : List α) :
    (cyclicPermutations l).head (cyclicPermutations_ne_nil l) = l := by
  have h : 0 < length (cyclicPermutations l) := length_pos_of_ne_nil (cyclicPermutations_ne_nil _)
  rw [← get_mk_zero h, get_cyclicPermutations, Fin.val_mk, rotate_zero]

@[simp]
theorem head?_cyclicPermutations (l : List α) : (cyclicPermutations l).head? = l := by
  rw [head?_eq_some_head (cyclicPermutations_ne_nil l), head_cyclicPermutations]

theorem cyclicPermutations_injective : Function.Injective (@cyclicPermutations α) := fun l l' h ↦ by
  simpa using congr_arg head? h

@[simp]
theorem cyclicPermutations_inj {l l' : List α} :
    cyclicPermutations l = cyclicPermutations l' ↔ l = l' :=
  cyclicPermutations_injective.eq_iff

theorem length_mem_cyclicPermutations (l : List α) (h : l' ∈ cyclicPermutations l) :
    length l' = length l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem h
  simp

theorem mem_cyclicPermutations_self (l : List α) : l ∈ cyclicPermutations l := by
  simpa using head_mem (cyclicPermutations_ne_nil l)

@[simp]
theorem cyclicPermutations_rotate (l : List α) (k : ℕ) :
    (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k := by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclicPermutations.rotate k) := by
    cases l
    · simp
    · rw [length_cyclicPermutations_of_ne_nil] <;> simp
  refine ext_get this fun n hn hn' => ?_
  rw [get_rotate, get_cyclicPermutations, rotate_rotate, ← rotate_mod, Nat.add_comm]
  cases l <;> simp

@[simp]
theorem mem_cyclicPermutations_iff : l ∈ cyclicPermutations l' ↔ l ~r l' := by
  constructor
  · simp_rw [mem_iff_get, get_cyclicPermutations]
    rintro ⟨k, rfl⟩
    exact .forall _ _
  · rintro ⟨k, rfl⟩
    rw [cyclicPermutations_rotate, mem_rotate]
    apply mem_cyclicPermutations_self

@[simp]
theorem cyclicPermutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔ l = [] :=
  cyclicPermutations_injective.eq_iff' rfl

@[simp]
theorem cyclicPermutations_eq_singleton_iff {l : List α} {x : α} :
    cyclicPermutations l = [[x]] ↔ l = [x] :=
  cyclicPermutations_injective.eq_iff' rfl

/-- If a `l : List α` is `Nodup l`, then all of its cyclic permutants are distinct. -/
protected theorem Nodup.cyclicPermutations {l : List α} (hn : Nodup l) :
    Nodup (cyclicPermutations l) := by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · rw [nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [length_cyclicPermutations_of_ne_nil l hl] at hi hj
    simpa [hn.rotate_congr_iff, mod_eq_of_lt, *] using h

protected theorem IsRotated.cyclicPermutations {l l' : List α} (h : l ~r l') :
    l.cyclicPermutations ~r l'.cyclicPermutations := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

@[simp]
theorem isRotated_cyclicPermutations_iff {l l' : List α} :
    l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l' := by
  simp only [IsRotated, ← cyclicPermutations_rotate, cyclicPermutations_inj]

section Decidable

variable [DecidableEq α]

instance isRotatedDecidable (l l' : List α) : Decidable (l ~r l') :=
  decidable_of_iff' _ isRotated_iff_mem_map_range

instance {l l' : List α} : Decidable (IsRotated.setoid α l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List
