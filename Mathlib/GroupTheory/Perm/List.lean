/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.Rotate
import Mathlib.GroupTheory.Perm.Support

/-!
# Permutations from a list

A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element in the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `List.formPerm` is implemented as a product of `Equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `List.formPerm` definition is meant to primarily be used with `Nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `List.formPerm` to produce a
nontrivial permutation that is noncyclic.
-/


namespace List

variable {α β : Type*}

section FormPerm

variable [DecidableEq α] (l : List α)

open Equiv Equiv.Perm

/-- A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element in the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.
-/
def formPerm : Equiv.Perm α :=
  (zipWith Equiv.swap l l.tail).prod

@[simp]
theorem formPerm_nil : formPerm ([] : List α) = 1 :=
  rfl

@[simp]
theorem formPerm_singleton (x : α) : formPerm [x] = 1 :=
  rfl

@[simp]
theorem formPerm_cons_cons (x y : α) (l : List α) :
    formPerm (x :: y :: l) = swap x y * formPerm (y :: l) :=
  rfl

theorem formPerm_pair (x y : α) : formPerm [x, y] = swap x y :=
  rfl

theorem mem_or_mem_of_zipWith_swap_prod_ne : ∀ {l l' : List α} {x : α},
    (zipWith swap l l').prod x ≠ x → x ∈ l ∨ x ∈ l'
  | [], _, _ => by simp
  | _, [], _ => by simp
  | a::l, b::l', x => fun hx ↦
    if h : (zipWith swap l l').prod x = x then
      (eq_or_eq_of_swap_apply_ne_self (a := a) (b := b) (x := x) (by simpa [h] using hx)).imp
        (by rintro rfl; exact .head _) (by rintro rfl; exact .head _)
    else
     (mem_or_mem_of_zipWith_swap_prod_ne h).imp (.tail _) (.tail _)

theorem zipWith_swap_prod_support' (l l' : List α) :
    { x | (zipWith swap l l').prod x ≠ x } ≤ l.toFinset ⊔ l'.toFinset := fun _ h ↦ by
  simpa using mem_or_mem_of_zipWith_swap_prod_ne h

theorem zipWith_swap_prod_support [Fintype α] (l l' : List α) :
    (zipWith swap l l').prod.support ≤ l.toFinset ⊔ l'.toFinset := by
  intro x hx
  have hx' : x ∈ { x | (zipWith swap l l').prod x ≠ x } := by simpa using hx
  simpa using zipWith_swap_prod_support' _ _ hx'

theorem support_formPerm_le' : { x | formPerm l x ≠ x } ≤ l.toFinset := by
  refine (zipWith_swap_prod_support' l l.tail).trans ?_
  simpa [Finset.subset_iff] using tail_subset l

theorem support_formPerm_le [Fintype α] : support (formPerm l) ≤ l.toFinset := by
  intro x hx
  have hx' : x ∈ { x | formPerm l x ≠ x } := by simpa using hx
  simpa using support_formPerm_le' _ hx'

variable {l} {x : α}

theorem mem_of_formPerm_apply_ne (h : l.formPerm x ≠ x) : x ∈ l := by
  simpa [or_iff_left_of_imp mem_of_mem_tail] using mem_or_mem_of_zipWith_swap_prod_ne h

theorem formPerm_apply_of_notMem (h : x ∉ l) : formPerm l x = x :=
  not_imp_comm.1 mem_of_formPerm_apply_ne h

@[deprecated (since := "2025-05-23")] alias formPerm_apply_of_not_mem := formPerm_apply_of_notMem

theorem formPerm_apply_mem_of_mem (h : x ∈ l) : formPerm l x ∈ l := by
  rcases l with - | ⟨y, l⟩
  · simp at h
  induction l generalizing x y with
  | nil => simpa using h
  | cons z l IH =>
    by_cases hx : x ∈ z :: l
    · rw [formPerm_cons_cons, mul_apply, swap_apply_def]
      split_ifs
      · simp
      · simp
      · simp [*]
    · replace h : x = y := Or.resolve_right (mem_cons.1 h) hx
      simp [formPerm_apply_of_notMem hx, ← h]

theorem mem_of_formPerm_apply_mem (h : l.formPerm x ∈ l) : x ∈ l := by
  contrapose h
  rwa [formPerm_apply_of_notMem h]

@[simp]
theorem formPerm_mem_iff_mem : l.formPerm x ∈ l ↔ x ∈ l :=
  ⟨l.mem_of_formPerm_apply_mem, l.formPerm_apply_mem_of_mem⟩

@[simp]
theorem formPerm_cons_concat_apply_last (x y : α) (xs : List α) :
    formPerm (x :: (xs ++ [y])) y = x := by
  induction xs generalizing x y with
  | nil => simp
  | cons z xs IH => simp [IH]

@[simp]
theorem formPerm_apply_getLast (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x := by
  induction xs using List.reverseRecOn generalizing x <;> simp

@[simp]
theorem formPerm_apply_getElem_length (x : α) (xs : List α) :
    formPerm (x :: xs) (x :: xs)[xs.length] = x := by
  rw [getElem_cons_length rfl, formPerm_apply_getLast]

theorem formPerm_apply_head (x y : α) (xs : List α) (h : Nodup (x :: y :: xs)) :
    formPerm (x :: y :: xs) x = y := by simp [formPerm_apply_of_notMem h.notMem]

theorem formPerm_apply_getElem_zero (l : List α) (h : Nodup l) (hl : 1 < l.length) :
    formPerm l l[0] = l[1] := by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp at hl
  · simp at hl
  · rw [getElem_cons_zero, formPerm_apply_head _ _ _ h, getElem_cons_succ, getElem_cons_zero]

variable (l)

theorem formPerm_eq_head_iff_eq_getLast (x y : α) :
    formPerm (y :: l) x = y ↔ x = getLast (y :: l) (cons_ne_nil _ _) :=
  Iff.trans (by rw [formPerm_apply_getLast]) (formPerm (y :: l)).injective.eq_iff

theorem formPerm_apply_lt_getElem (xs : List α) (h : Nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
    formPerm xs xs[n] = xs[n+1] := by
  induction n generalizing xs with
  | zero => simpa using formPerm_apply_getElem_zero _ h _
  | succ n IH =>
    rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp at hn
    · rw [formPerm_singleton, getElem_singleton, getElem_singleton, one_apply]
    · specialize IH (y :: l) h.of_cons _
      · simpa [Nat.succ_lt_succ_iff] using hn
      simp only [swap_apply_eq_iff, coe_mul, formPerm_cons_cons, Function.comp]
      simp only [getElem_cons_succ] at *
      rw [← IH, swap_apply_of_ne_of_ne] <;>
      · intro hx
        rw [← hx, IH] at h
        simp [getElem_mem] at h

theorem formPerm_apply_getElem (xs : List α) (w : Nodup xs) (i : ℕ) (h : i < xs.length) :
    formPerm xs xs[i] =
      xs[(i + 1) % xs.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h)) := by
  rcases xs with - | ⟨x, xs⟩
  · simp at h
  · have : i ≤ xs.length := by
      refine Nat.le_of_lt_succ ?_
      simpa using h
    rcases this.eq_or_lt with (rfl | hn')
    · simp
    · rw [formPerm_apply_lt_getElem (x :: xs) w _ (Nat.succ_lt_succ hn')]
      congr
      rw [Nat.mod_eq_of_lt]; simpa [Nat.succ_eq_add_one]

theorem support_formPerm_of_nodup' (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    { x | formPerm l x ≠ x } = l.toFinset := by
  apply _root_.le_antisymm
  · exact support_formPerm_le' l
  · intro x hx
    simp only [Finset.mem_coe, mem_toFinset] at hx
    obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
    rw [Set.mem_setOf_eq, formPerm_apply_getElem _ h]
    intro H
    rw [nodup_iff_injective_get, Function.Injective] at h
    specialize h H
    rcases (Nat.succ_le_of_lt hn).eq_or_lt with hn' | hn'
    · simp only [← hn', Nat.mod_self] at h
      refine not_exists.mpr h' ?_
      rw [← length_eq_one_iff, ← hn', (Fin.mk.inj_iff.mp h).symm]
    · simp [Nat.mod_eq_of_lt hn'] at h

theorem support_formPerm_of_nodup [Fintype α] (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    support (formPerm l) = l.toFinset := by
  rw [← Finset.coe_inj]
  convert support_formPerm_of_nodup' _ h h'
  simp [Set.ext_iff]

theorem formPerm_rotate_one (l : List α) (h : Nodup l) : formPerm (l.rotate 1) = formPerm l := by
  have h' : Nodup (l.rotate 1) := by simpa using h
  ext x
  by_cases hx : x ∈ l.rotate 1
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    rw [formPerm_apply_getElem _ h', getElem_rotate l, getElem_rotate l, formPerm_apply_getElem _ h]
    simp
  · rw [formPerm_apply_of_notMem hx, formPerm_apply_of_notMem]
    simpa using hx

theorem formPerm_rotate (l : List α) (h : Nodup l) (n : ℕ) :
    formPerm (l.rotate n) = formPerm l := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [← rotate_rotate, formPerm_rotate_one, hn]
    rwa [IsRotated.nodup_iff]
    exact IsRotated.forall l n

theorem formPerm_eq_of_isRotated {l l' : List α} (hd : Nodup l) (h : l ~r l') :
    formPerm l = formPerm l' := by
  obtain ⟨n, rfl⟩ := h
  exact (formPerm_rotate l hd n).symm

theorem formPerm_append_pair : ∀ (l : List α) (a b : α),
    formPerm (l ++ [a, b]) = formPerm (l ++ [a]) * swap a b
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x::y::l, a, b => by
    simpa [mul_assoc] using formPerm_append_pair (y::l) a b

theorem formPerm_reverse : ∀ l : List α, formPerm l.reverse = (formPerm l)⁻¹
  | [] => rfl
  | [_] => rfl
  | a::b::l => by
    simp [formPerm_append_pair, swap_comm, ← formPerm_reverse (b::l)]

theorem formPerm_pow_apply_getElem (l : List α) (w : Nodup l) (n : ℕ) (i : ℕ) (h : i < l.length) :
    (formPerm l ^ n) l[i] =
      l[(i + n) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h)) := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt h]
  | succ n hn =>
    simp [pow_succ', mul_apply, hn, formPerm_apply_getElem _ w,
      ← Nat.add_assoc]

theorem formPerm_pow_apply_head (x : α) (l : List α) (h : Nodup (x :: l)) (n : ℕ) :
    (formPerm (x :: l) ^ n) x =
      (x :: l)[(n % (x :: l).length)]'(Nat.mod_lt _ (Nat.zero_lt_succ _)) := by
  convert formPerm_pow_apply_getElem _ h n 0 (Nat.succ_pos _)
  simp

theorem formPerm_ext_iff {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
    (hd' : Nodup (x' :: y' :: l')) :
    formPerm (x :: y :: l) = formPerm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') := by
  refine ⟨fun h => ?_, fun hr => formPerm_eq_of_isRotated hd hr⟩
  rw [Equiv.Perm.ext_iff] at h
  have hx : x' ∈ x :: y :: l := by
    have : x' ∈ { z | formPerm (x :: y :: l) z ≠ z } := by
      rw [Set.mem_setOf_eq, h x', formPerm_apply_head _ _ _ hd']
      simp only [mem_cons, nodup_cons] at hd'
      push_neg at hd'
      exact hd'.left.left.symm
    simpa using support_formPerm_le' _ this
  obtain ⟨⟨n, hn⟩, hx'⟩ := get_of_mem hx
  have hl : (x :: y :: l).length = (x' :: y' :: l').length := by
    rw [← dedup_eq_self.mpr hd, ← dedup_eq_self.mpr hd', ← card_toFinset, ← card_toFinset]
    refine congr_arg Finset.card ?_
    rw [← Finset.coe_inj, ← support_formPerm_of_nodup' _ hd (by simp), ←
      support_formPerm_of_nodup' _ hd' (by simp)]
    simp only [h]
  use n
  apply List.ext_getElem
  · rw [length_rotate, hl]
  · intro k hk hk'
    rw [getElem_rotate]
    induction k with
    | zero =>
      refine Eq.trans ?_ hx'
      congr
      simpa using hn
    | succ k IH =>
      conv => congr <;> · arg 2; (rw [← Nat.mod_eq_of_lt hk'])
      rw [← formPerm_apply_getElem _ hd' k (k.lt_succ_self.trans hk'),
        ← IH (k.lt_succ_self.trans hk), ← h, formPerm_apply_getElem _ hd]
      congr 1
      rw [hl, Nat.mod_eq_of_lt hk', add_right_comm]
      apply Nat.add_mod

theorem formPerm_apply_mem_eq_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = x ↔ length l ≤ 1 := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [formPerm_apply_getElem _ hl k hk, hl.getElem_inj_iff]
  cases hn : l.length
  · exact absurd k.zero_le (hk.trans_le hn.le).not_ge
  · rw [hn] at hk
    rcases (Nat.le_of_lt_succ hk).eq_or_lt with hk' | hk'
    · simp [← hk', eq_comm]
    · simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.succ_lt_succ_iff] using
        (k.zero_le.trans_lt hk').ne.symm

theorem formPerm_apply_mem_ne_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x ≠ x ↔ 2 ≤ l.length := by
  rw [Ne, formPerm_apply_mem_eq_self_iff _ hl x hx, not_le]
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩

@[deprecated (since := "2025-10-06")]
alias mem_of_formPerm_ne_self := mem_of_formPerm_apply_ne

@[deprecated (since := "2025-10-06")]
alias formPerm_eq_self_of_notMem := List.formPerm_apply_of_notMem

@[deprecated (since := "2025-05-23")]
alias formPerm_eq_self_of_not_mem := List.formPerm_apply_of_notMem

theorem formPerm_eq_one_iff (hl : Nodup l) : formPerm l = 1 ↔ l.length ≤ 1 := by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [← formPerm_apply_mem_eq_self_iff _ hl hd mem_cons_self]
    constructor
    · simp +contextual
    · intro h
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd mem_cons_self,
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, length_eq_zero_iff] at h
      simp [h]

theorem formPerm_eq_formPerm_iff {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 := by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length ≤ 1 ↔ l' = nil ∨ l'.length ≤ 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (rfl | h)
    · simp
    · exact h
  · suffices l'.length ≤ 1 ↔ [x] ~r l' ∨ l'.length ≤ 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff, le_rfl]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (h | h)
    · simp [← h.perm.length_eq]
    · exact h
  · rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩)
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
    · simp [-formPerm_cons_cons, formPerm_ext_iff hl hl']

theorem form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x ∈ l) (n : ℤ) :
    (formPerm l ^ n) x ∈ l := by
  by_cases h : (l.formPerm ^ n) x = x
  · simpa [h] using hx
  · have h : x ∈ { x | (l.formPerm ^ n) x ≠ x } := h
    rw [← set_support_apply_mem] at h
    replace h := set_support_zpow_subset _ _ h
    simpa using support_formPerm_le' _ h

theorem formPerm_pow_length_eq_one_of_nodup (hl : Nodup l) : formPerm l ^ length l = 1 := by
  ext x
  by_cases hx : x ∈ l
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    simp [formPerm_pow_apply_getElem _ hl, Nat.mod_eq_of_lt hk]
  · have : x ∉ { x | (l.formPerm ^ l.length) x ≠ x } := by
      intro H
      refine hx ?_
      replace H := set_support_zpow_subset l.formPerm l.length H
      simpa using support_formPerm_le' _ H
    simpa using this

end FormPerm

end List
