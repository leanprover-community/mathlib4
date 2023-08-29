/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.List.Rotate
import Mathlib.GroupTheory.Perm.Support

#align_import group_theory.perm.list from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

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
#align list.form_perm List.formPerm

@[simp]
theorem formPerm_nil : formPerm ([] : List α) = 1 :=
  rfl
#align list.form_perm_nil List.formPerm_nil

@[simp]
theorem formPerm_singleton (x : α) : formPerm [x] = 1 :=
  rfl
#align list.form_perm_singleton List.formPerm_singleton

@[simp]
theorem formPerm_cons_cons (x y : α) (l : List α) :
    formPerm (x :: y :: l) = swap x y * formPerm (y :: l) :=
  prod_cons
#align list.form_perm_cons_cons List.formPerm_cons_cons

theorem formPerm_pair (x y : α) : formPerm [x, y] = swap x y :=
  rfl
#align list.form_perm_pair List.formPerm_pair

variable {l} {x : α}

theorem formPerm_apply_of_not_mem (x : α) (l : List α) (h : x ∉ l) : formPerm l x = x := by
  cases' l with y l
  -- ⊢ ↑(formPerm []) x = x
  · simp
    -- 🎉 no goals
  induction' l with z l IH generalizing x y
  -- ⊢ ↑(formPerm [y]) x = x
  · simp
    -- 🎉 no goals
  · specialize IH x z (mt (mem_cons_of_mem y) h)
    -- ⊢ ↑(formPerm (y :: z :: l)) x = x
    simp only [not_or, mem_cons] at h
    -- ⊢ ↑(formPerm (y :: z :: l)) x = x
    simp [IH, swap_apply_of_ne_of_ne, h]
    -- 🎉 no goals
#align list.form_perm_apply_of_not_mem List.formPerm_apply_of_not_mem

theorem mem_of_formPerm_apply_ne (x : α) (l : List α) : l.formPerm x ≠ x → x ∈ l :=
  not_imp_comm.2 <| List.formPerm_apply_of_not_mem _ _
#align list.mem_of_form_perm_apply_ne List.mem_of_formPerm_apply_ne

theorem formPerm_apply_mem_of_mem (x : α) (l : List α) (h : x ∈ l) : formPerm l x ∈ l := by
  cases' l with y l
  -- ⊢ ↑(formPerm []) x ∈ []
  · simp at h
    -- 🎉 no goals
  induction' l with z l IH generalizing x y
  -- ⊢ ↑(formPerm [y]) x ∈ [y]
  · simpa using h
    -- 🎉 no goals
  · by_cases hx : x ∈ z :: l
    -- ⊢ ↑(formPerm (y :: z :: l)) x ∈ y :: z :: l
    · rw [formPerm_cons_cons, mul_apply, swap_apply_def]
      -- ⊢ (if ↑(formPerm (z :: l)) x = y then z else if ↑(formPerm (z :: l)) x = z the …
      split_ifs
      · simp [IH _ _ hx]
        -- 🎉 no goals
      · simp
        -- 🎉 no goals
      · simpa [*] using IH _ _ hx
        -- 🎉 no goals
    · replace h : x = y := Or.resolve_right (mem_cons.1 h) hx
      -- ⊢ ↑(formPerm (y :: z :: l)) x ∈ y :: z :: l
      simp [formPerm_apply_of_not_mem _ _ hx, ← h]
      -- 🎉 no goals
#align list.form_perm_apply_mem_of_mem List.formPerm_apply_mem_of_mem

set_option maxHeartbeats 220000 in
theorem mem_of_formPerm_apply_mem (x : α) (l : List α) (h : l.formPerm x ∈ l) : x ∈ l := by
  cases' l with y l
  -- ⊢ x ∈ []
  · simp at h
    -- 🎉 no goals
  induction' l with z l IH generalizing x y
  -- ⊢ x ∈ [y]
  · simpa using h
    -- 🎉 no goals
  · by_cases hx : (z :: l).formPerm x ∈ z :: l
    -- ⊢ x ∈ y :: z :: l
    · rw [List.formPerm_cons_cons, mul_apply, swap_apply_def] at h
      -- ⊢ x ∈ y :: z :: l
      split_ifs at h <;> aesop
                         -- 🎉 no goals
                         -- 🎉 no goals
                         -- 🎉 no goals
    · replace hx :=
        (Function.Injective.eq_iff (Equiv.injective _)).mp (List.formPerm_apply_of_not_mem _ _ hx)
      simp only [List.formPerm_cons_cons, hx, Equiv.Perm.coe_mul, Function.comp_apply,
        List.mem_cons, swap_apply_def, ite_eq_left_iff] at h
      simp only [List.mem_cons]
      -- ⊢ x = y ∨ x = z ∨ x ∈ l
      rcases h with h | h | h <;> split_ifs at h with h1 <;> try { aesop }
                                  -- ⊢ x = y ∨ x = z ∨ x ∈ l
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- ⊢ x = y ∨ x = z ∨ x ∈ l
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
      · simp [h1, imp_false] at h
        -- ⊢ x = y ∨ x = z ∨ x ∈ l
        simp [h]
        -- 🎉 no goals
#align list.mem_of_form_perm_apply_mem List.mem_of_formPerm_apply_mem

theorem formPerm_mem_iff_mem : l.formPerm x ∈ l ↔ x ∈ l :=
  ⟨l.mem_of_formPerm_apply_mem x, l.formPerm_apply_mem_of_mem x⟩
#align list.form_perm_mem_iff_mem List.formPerm_mem_iff_mem

@[simp]
theorem formPerm_cons_concat_apply_last (x y : α) (xs : List α) :
    formPerm (x :: (xs ++ [y])) y = x := by
  induction' xs with z xs IH generalizing x y
  -- ⊢ ↑(formPerm (x :: ([] ++ [y]))) y = x
  · simp
    -- 🎉 no goals
  · simp [IH]
    -- 🎉 no goals
#align list.form_perm_cons_concat_apply_last List.formPerm_cons_concat_apply_last

@[simp]
theorem formPerm_apply_getLast (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x := by
  induction' xs using List.reverseRecOn with xs y _ generalizing x <;> simp
  -- ⊢ ↑(formPerm [x]) (getLast [x] (_ : [x] ≠ [])) = x
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals
#align list.form_perm_apply_last List.formPerm_apply_getLast

set_option linter.deprecated false in
@[simp]
theorem formPerm_apply_nthLe_length (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).nthLe xs.length (by simp)) = x := by
                                                      -- 🎉 no goals
  rw [nthLe_cons_length, formPerm_apply_getLast]; rfl
  -- ⊢ length xs = length xs
                                                  -- 🎉 no goals
#align list.form_perm_apply_nth_le_length List.formPerm_apply_nthLe_length

theorem formPerm_apply_head (x y : α) (xs : List α) (h : Nodup (x :: y :: xs)) :
    formPerm (x :: y :: xs) x = y := by simp [formPerm_apply_of_not_mem _ _ h.not_mem]
                                        -- 🎉 no goals
#align list.form_perm_apply_head List.formPerm_apply_head

set_option linter.deprecated false in
theorem formPerm_apply_nthLe_zero (l : List α) (h : Nodup l) (hl : 1 < l.length) :
    formPerm l (l.nthLe 0 (zero_lt_one.trans hl)) = l.nthLe 1 hl := by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp at hl
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simpa using formPerm_apply_head _ _ _ h
    -- 🎉 no goals
#align list.form_perm_apply_nth_le_zero List.formPerm_apply_nthLe_zero

variable (l)

theorem formPerm_eq_head_iff_eq_getLast (x y : α) :
    formPerm (y :: l) x = y ↔ x = getLast (y :: l) (cons_ne_nil _ _) :=
  Iff.trans (by rw [formPerm_apply_getLast]) (formPerm (y :: l)).injective.eq_iff
                -- 🎉 no goals
#align list.form_perm_eq_head_iff_eq_last List.formPerm_eq_head_iff_eq_getLast

theorem zipWith_swap_prod_support' (l l' : List α) :
    { x | (zipWith swap l l').prod x ≠ x } ≤ l.toFinset ⊔ l'.toFinset := by
  simp only [Set.sup_eq_union, Set.le_eq_subset]
  -- ⊢ {x | ↑(prod (zipWith swap l l')) x ≠ x} ⊆ ↑(toFinset l ⊔ toFinset l')
  induction' l with y l hl generalizing l'
  -- ⊢ {x | ↑(prod (zipWith swap [] l')) x ≠ x} ⊆ ↑(toFinset [] ⊔ toFinset l')
  · simp
    -- 🎉 no goals
  · cases' l' with z l'
    -- ⊢ {x | ↑(prod (zipWith swap (y :: l) [])) x ≠ x} ⊆ ↑(toFinset (y :: l) ⊔ toFin …
    · simp
      -- 🎉 no goals
    · intro x
      -- ⊢ x ∈ {x | ↑(prod (zipWith swap (y :: l) (z :: l'))) x ≠ x} → x ∈ ↑(toFinset ( …
      simp only [Set.union_subset_iff, mem_cons, zipWith_cons_cons, foldr, prod_cons,
        mul_apply]
      intro hx
      -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
      by_cases h : x ∈ { x | (zipWith swap l l').prod x ≠ x }
      -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
      · specialize hl l' h
        -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
        simp only [ge_iff_le, Finset.le_eq_subset, Finset.sup_eq_union, Finset.coe_union,
          coe_toFinset, Set.mem_union, Set.mem_setOf_eq] at hl
        refine' Or.elim hl (fun hm => _) fun hm => _ <;>
        -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
          · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, toFinset_cons,
              mem_toFinset] at hm ⊢
            simp [hm]
            -- 🎉 no goals
            -- 🎉 no goals
      · simp only [not_not, Set.mem_setOf_eq] at h
        -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
        simp only [h, Set.mem_setOf_eq] at hx
        -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
        rw [swap_apply_ne_self_iff] at hx
        -- ⊢ x ∈ ↑(toFinset (y :: l) ⊔ toFinset (z :: l'))
        rcases hx with ⟨hyz, rfl | rfl⟩ <;> simp
        -- ⊢ x ∈ ↑(toFinset (x :: l) ⊔ toFinset (z :: l'))
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align list.zip_with_swap_prod_support' List.zipWith_swap_prod_support'

theorem zipWith_swap_prod_support [Fintype α] (l l' : List α) :
    (zipWith swap l l').prod.support ≤ l.toFinset ⊔ l'.toFinset := by
  intro x hx
  -- ⊢ x ∈ toFinset l ⊔ toFinset l'
  have hx' : x ∈ { x | (zipWith swap l l').prod x ≠ x } := by simpa using hx
  -- ⊢ x ∈ toFinset l ⊔ toFinset l'
  simpa using zipWith_swap_prod_support' _ _ hx'
  -- 🎉 no goals
#align list.zip_with_swap_prod_support List.zipWith_swap_prod_support

theorem support_formPerm_le' : { x | formPerm l x ≠ x } ≤ l.toFinset := by
  refine' (zipWith_swap_prod_support' l l.tail).trans _
  -- ⊢ ↑(toFinset l ⊔ toFinset (tail l)) ≤ ↑(toFinset l)
  simpa [Finset.subset_iff] using tail_subset l
  -- 🎉 no goals
#align list.support_form_perm_le' List.support_formPerm_le'

theorem support_formPerm_le [Fintype α] : support (formPerm l) ≤ l.toFinset := by
  intro x hx
  -- ⊢ x ∈ toFinset l
  have hx' : x ∈ { x | formPerm l x ≠ x } := by simpa using hx
  -- ⊢ x ∈ toFinset l
  simpa using support_formPerm_le' _ hx'
  -- 🎉 no goals
#align list.support_form_perm_le List.support_formPerm_le

set_option linter.deprecated false in
theorem formPerm_apply_lt (xs : List α) (h : Nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
    formPerm xs (xs.nthLe n ((Nat.lt_succ_self n).trans hn)) = xs.nthLe (n + 1) hn := by
  induction' n with n IH generalizing xs
  -- ⊢ ↑(formPerm xs) (nthLe xs Nat.zero (_ : Nat.zero < length xs)) = nthLe xs (Na …
  · simpa using formPerm_apply_nthLe_zero _ h _
    -- 🎉 no goals
  · rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp at hn
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
    · specialize IH (y :: l) h.of_cons _
      -- ⊢ n + 1 < length (y :: l)
      · simpa [Nat.succ_lt_succ_iff] using hn
        -- 🎉 no goals
      simp only [swap_apply_eq_iff, coe_mul, formPerm_cons_cons, Function.comp]
      -- ⊢ ↑(formPerm (y :: l)) (nthLe (x :: y :: l) (Nat.succ n) (_ : Nat.succ n < len …
      simp only [nthLe, get_cons_succ] at *
      -- ⊢ ↑(formPerm (y :: l)) (get (y :: l) { val := n, isLt := (_ : n < length (y :: …
      rw [← IH, swap_apply_of_ne_of_ne] <;>
      -- ⊢ ↑(formPerm (y :: l)) (get (y :: l) { val := n, isLt := (_ : n < length (y :: …
      · intro hx
        -- ⊢ False
        -- ⊢ False
        -- ⊢ False
        rw [← hx, IH] at h
        -- 🎉 no goals
        -- ⊢ False
        simp [get_mem] at h
        -- 🎉 no goals
#align list.form_perm_apply_lt List.formPerm_apply_lt

set_option linter.deprecated false in
theorem formPerm_apply_nthLe (xs : List α) (h : Nodup xs) (n : ℕ) (hn : n < xs.length) :
    formPerm xs (xs.nthLe n hn) =
      xs.nthLe ((n + 1) % xs.length) (Nat.mod_lt _ (n.zero_le.trans_lt hn)) := by
  cases' xs with x xs
  -- ⊢ ↑(formPerm []) (nthLe [] n hn) = nthLe [] ((n + 1) % length []) (_ : (n + 1) …
  · simp at hn
    -- 🎉 no goals
  · have : n ≤ xs.length := by
      refine' Nat.le_of_lt_succ _
      simpa using hn
    rcases this.eq_or_lt with (rfl | hn')
    -- ⊢ ↑(formPerm (x :: xs)) (nthLe (x :: xs) (length xs) hn) = nthLe (x :: xs) ((l …
    · simp; simp [nthLe]
      -- ⊢ x = nthLe (x :: xs) 0 (_ : 0 < length (x :: xs))
            -- 🎉 no goals
    · rw [formPerm_apply_lt _ h _ (Nat.succ_lt_succ hn')]
      -- ⊢ nthLe (x :: xs) (n + 1) (_ : Nat.succ n < Nat.succ (length xs)) = nthLe (x : …
      congr
      -- ⊢ n + 1 = (n + 1) % length (x :: xs)
      rw [Nat.mod_eq_of_lt]; simpa [Nat.succ_eq_add_one]
      -- ⊢ n + 1 < length (x :: xs)
                             -- 🎉 no goals
#align list.form_perm_apply_nth_le List.formPerm_apply_nthLe

set_option linter.deprecated false in
theorem support_formPerm_of_nodup' (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    { x | formPerm l x ≠ x } = l.toFinset := by
  apply _root_.le_antisymm
  -- ⊢ {x | ↑(formPerm l) x ≠ x} ≤ ↑(toFinset l)
  · exact support_formPerm_le' l
    -- 🎉 no goals
  · intro x hx
    -- ⊢ x ∈ {x | ↑(formPerm l) x ≠ x}
    simp only [Finset.mem_coe, mem_toFinset] at hx
    -- ⊢ x ∈ {x | ↑(formPerm l) x ≠ x}
    obtain ⟨n, hn, rfl⟩ := nthLe_of_mem hx
    -- ⊢ nthLe l n hn ∈ {x | ↑(formPerm l) x ≠ x}
    rw [Set.mem_setOf_eq, formPerm_apply_nthLe _ h]
    -- ⊢ nthLe l ((n + 1) % length l) (_ : (n + 1) % length l < length l) ≠ nthLe l n …
    intro H
    -- ⊢ False
    rw [nodup_iff_nthLe_inj] at h
    -- ⊢ False
    specialize h _ _ _ _ H
    -- ⊢ False
    cases' (Nat.succ_le_of_lt hn).eq_or_lt with hn' hn'
    -- ⊢ False
    · simp only [← hn', Nat.mod_self] at h
      -- ⊢ False
      refine' not_exists.mpr h' _
      -- ⊢ ∃ x, l = [x]
      rw [← length_eq_one]
      -- ⊢ length l = 1
      simpa [← h, eq_comm] using hn'
      -- 🎉 no goals
    · simp [Nat.mod_eq_of_lt hn'] at h
      -- 🎉 no goals
#align list.support_form_perm_of_nodup' List.support_formPerm_of_nodup'

theorem support_formPerm_of_nodup [Fintype α] (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    support (formPerm l) = l.toFinset := by
  rw [← Finset.coe_inj]
  -- ⊢ ↑(support (formPerm l)) = ↑(toFinset l)
  convert support_formPerm_of_nodup' _ h h'
  -- ⊢ ↑(support (formPerm l)) = {x | ↑(formPerm l) x ≠ x}
  simp [Set.ext_iff]
  -- 🎉 no goals
#align list.support_form_perm_of_nodup List.support_formPerm_of_nodup

set_option linter.deprecated false in
theorem formPerm_rotate_one (l : List α) (h : Nodup l) : formPerm (l.rotate 1) = formPerm l := by
  have h' : Nodup (l.rotate 1) := by simpa using h
  -- ⊢ formPerm (rotate l 1) = formPerm l
  ext x
  -- ⊢ ↑(formPerm (rotate l 1)) x = ↑(formPerm l) x
  by_cases hx : x ∈ l.rotate 1
  -- ⊢ ↑(formPerm (rotate l 1)) x = ↑(formPerm l) x
  · obtain ⟨k, hk, rfl⟩ := nthLe_of_mem hx
    -- ⊢ ↑(formPerm (rotate l 1)) (nthLe (rotate l 1) k hk) = ↑(formPerm l) (nthLe (r …
    rw [formPerm_apply_nthLe _ h', nthLe_rotate l, nthLe_rotate l, formPerm_apply_nthLe _ h]
    -- ⊢ nthLe l (((k + 1) % length (rotate l 1) + 1) % length l) (_ : ((k + 1) % len …
    simp
    -- 🎉 no goals
  · rw [formPerm_apply_of_not_mem _ _ hx, formPerm_apply_of_not_mem]
    -- ⊢ ¬x ∈ l
    simpa using hx
    -- 🎉 no goals
#align list.form_perm_rotate_one List.formPerm_rotate_one

theorem formPerm_rotate (l : List α) (h : Nodup l) (n : ℕ) :
    formPerm (l.rotate n) = formPerm l := by
  induction' n with n hn
  -- ⊢ formPerm (rotate l Nat.zero) = formPerm l
  · simp
    -- 🎉 no goals
  · rw [Nat.succ_eq_add_one, ← rotate_rotate, formPerm_rotate_one, hn]
    -- ⊢ Nodup (rotate l n)
    rwa [IsRotated.nodup_iff]
    -- ⊢ rotate l n ~r l
    exact IsRotated.forall l n
    -- 🎉 no goals
#align list.form_perm_rotate List.formPerm_rotate

theorem formPerm_eq_of_isRotated {l l' : List α} (hd : Nodup l) (h : l ~r l') :
    formPerm l = formPerm l' := by
  obtain ⟨n, rfl⟩ := h
  -- ⊢ formPerm l = formPerm (rotate l n)
  exact (formPerm_rotate l hd n).symm
  -- 🎉 no goals
#align list.form_perm_eq_of_is_rotated List.formPerm_eq_of_isRotated

set_option linter.deprecated false in
theorem formPerm_reverse (l : List α) (h : Nodup l) : formPerm l.reverse = (formPerm l)⁻¹ := by
  -- Let's show `formPerm l` is an inverse to `formPerm l.reverse`.
  rw [eq_comm, inv_eq_iff_mul_eq_one]
  -- ⊢ formPerm l * formPerm (reverse l) = 1
  ext x
  -- ⊢ ↑(formPerm l * formPerm (reverse l)) x = ↑1 x
  -- We only have to check for `x ∈ l` that `formPerm l (formPerm l.reverse x)`
  rw [mul_apply, one_apply]
  -- ⊢ ↑(formPerm l) (↑(formPerm (reverse l)) x) = x
  cases' Classical.em (x ∈ l) with hx hx
  -- ⊢ ↑(formPerm l) (↑(formPerm (reverse l)) x) = x
  · obtain ⟨k, hk, rfl⟩ := nthLe_of_mem (mem_reverse.mpr hx)
    -- ⊢ ↑(formPerm l) (↑(formPerm (reverse l)) (nthLe (reverse l) k hk)) = nthLe (re …
    have h1 : l.length - 1 - k < l.length := by
      rw [Nat.sub_sub, add_comm]
      exact Nat.sub_lt_self (Nat.succ_pos _) (Nat.succ_le_of_lt (by simpa using hk))
    have h2 : length l - 1 - (k + 1) % length (reverse l) < length l := by
      rw [Nat.sub_sub, length_reverse];
      exact Nat.sub_lt_self (by rw [add_comm]; exact Nat.succ_pos _)
        (by rw [add_comm]; exact Nat.succ_le_of_lt (Nat.mod_lt _ (length_pos_of_mem hx)))
    rw [formPerm_apply_nthLe l.reverse (nodup_reverse.mpr h), nthLe_reverse' _ _ _ h1,
      nthLe_reverse' _ _ _ h2, formPerm_apply_nthLe _ h]
    congr
    -- ⊢ (length l - 1 - (k + 1) % length (reverse l) + 1) % length l = length l - 1  …
    rw [length_reverse] at *
    -- ⊢ (length l - 1 - (k + 1) % length l + 1) % length l = length l - 1 - k
    cases' lt_or_eq_of_le (Nat.succ_le_of_lt hk) with h h
    -- ⊢ (length l - 1 - (k + 1) % length l + 1) % length l = length l - 1 - k
    · rw [Nat.mod_eq_of_lt h, ← Nat.sub_add_comm, Nat.succ_sub_succ_eq_sub,
        Nat.mod_eq_of_lt h1]
      exact (Nat.le_sub_iff_add_le (length_pos_of_mem hx)).2 (Nat.succ_le_of_lt h)
      -- 🎉 no goals
    · rw [← h]; simp
      -- ⊢ (Nat.succ k - 1 - (k + 1) % Nat.succ k + 1) % Nat.succ k = Nat.succ k - 1 - k
                -- 🎉 no goals
  · rw [formPerm_apply_of_not_mem x l.reverse, formPerm_apply_of_not_mem _ _ hx]
    -- ⊢ ¬x ∈ reverse l
    simpa using hx
    -- 🎉 no goals
#align list.form_perm_reverse List.formPerm_reverse

theorem formPerm_pow_apply_nthLe (l : List α) (h : Nodup l) (n k : ℕ) (hk : k < l.length) :
    (formPerm l ^ n) (l.nthLe k hk) =
      l.nthLe ((k + n) % l.length) (Nat.mod_lt _ (k.zero_le.trans_lt hk)) := by
  induction' n with n hn
  -- ⊢ ↑(formPerm l ^ Nat.zero) (nthLe l k hk) = nthLe l ((k + Nat.zero) % length l …
  · simp [Nat.mod_eq_of_lt hk]
    -- 🎉 no goals
  · simp [pow_succ, mul_apply, hn, formPerm_apply_nthLe _ h, Nat.succ_eq_add_one, ← Nat.add_assoc]
    -- 🎉 no goals
#align list.form_perm_pow_apply_nth_le List.formPerm_pow_apply_nthLe

theorem formPerm_pow_apply_head (x : α) (l : List α) (h : Nodup (x :: l)) (n : ℕ) :
    (formPerm (x :: l) ^ n) x =
      (x :: l).nthLe (n % (x :: l).length) (Nat.mod_lt _ (Nat.zero_lt_succ _)) := by
  convert formPerm_pow_apply_nthLe _ h n 0 (Nat.succ_pos _)
  -- ⊢ n = 0 + n
  simp
  -- 🎉 no goals
#align list.form_perm_pow_apply_head List.formPerm_pow_apply_head

set_option linter.deprecated false in
theorem formPerm_ext_iff {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
    (hd' : Nodup (x' :: y' :: l')) :
    formPerm (x :: y :: l) = formPerm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') := by
  refine' ⟨fun h => _, fun hr => formPerm_eq_of_isRotated hd hr⟩
  -- ⊢ (x :: y :: l) ~r (x' :: y' :: l')
  rw [Equiv.Perm.ext_iff] at h
  -- ⊢ (x :: y :: l) ~r (x' :: y' :: l')
  have hx : x' ∈ x :: y :: l := by
    have : x' ∈ { z | formPerm (x :: y :: l) z ≠ z } := by
      rw [Set.mem_setOf_eq, h x', formPerm_apply_head _ _ _ hd']
      simp only [mem_cons, nodup_cons] at hd'
      push_neg at hd'
      exact hd'.left.left.symm
    simpa using support_formPerm_le' _ this
  obtain ⟨n, hn, hx'⟩ := nthLe_of_mem hx
  -- ⊢ (x :: y :: l) ~r (x' :: y' :: l')
  have hl : (x :: y :: l).length = (x' :: y' :: l').length := by
    rw [← dedup_eq_self.mpr hd, ← dedup_eq_self.mpr hd', ← card_toFinset, ← card_toFinset]
    refine' congr_arg Finset.card _
    rw [← Finset.coe_inj, ← support_formPerm_of_nodup' _ hd (by simp), ←
      support_formPerm_of_nodup' _ hd' (by simp)]
    simp only [h]
  use n
  -- ⊢ rotate (x :: y :: l) n = x' :: y' :: l'
  apply List.ext_nthLe
  -- ⊢ length (rotate (x :: y :: l) n) = length (x' :: y' :: l')
  · rw [length_rotate, hl]
    -- 🎉 no goals
  · intro k hk hk'
    -- ⊢ nthLe (rotate (x :: y :: l) n) k hk = nthLe (x' :: y' :: l') k hk'
    rw [nthLe_rotate]
    -- ⊢ nthLe (x :: y :: l) ((k + n) % length (x :: y :: l)) (_ : (k + n) % length ( …
    induction' k with k IH
    -- ⊢ nthLe (x :: y :: l) ((Nat.zero + n) % length (x :: y :: l)) (_ : (Nat.zero + …
    · refine' Eq.trans _ hx'
      -- ⊢ nthLe (x :: y :: l) ((Nat.zero + n) % length (x :: y :: l)) (_ : (Nat.zero + …
      congr
      -- ⊢ (Nat.zero + n) % length (x :: y :: l) = n
      simpa using hn
      -- 🎉 no goals
    · have : k.succ = (k + 1) % (x' :: y' :: l').length := by
        rw [← Nat.succ_eq_add_one, Nat.mod_eq_of_lt hk']
      simp_rw [this]
      -- ⊢ nthLe (x :: y :: l) (((k + 1) % length (x' :: y' :: l') + n) % length (x ::  …
      rw [← formPerm_apply_nthLe _ hd' k (k.lt_succ_self.trans hk'), ←
        IH (k.lt_succ_self.trans hk), ← h, formPerm_apply_nthLe _ hd]
      congr 1
      -- ⊢ ((k + 1) % length (x' :: y' :: l') + n) % length (x :: y :: l) = ((k + n) %  …
      have h1 : 1 = 1 % (x' :: y' :: l').length := by simp
      -- ⊢ ((k + 1) % length (x' :: y' :: l') + n) % length (x :: y :: l) = ((k + n) %  …
      rw [hl, Nat.mod_eq_of_lt hk', h1, ← Nat.add_mod, Nat.succ_add, Nat.succ_eq_add_one]
      -- 🎉 no goals
#align list.form_perm_ext_iff List.formPerm_ext_iff

set_option linter.deprecated false in
theorem formPerm_apply_mem_eq_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = x ↔ length l ≤ 1 := by
  obtain ⟨k, hk, rfl⟩ := nthLe_of_mem hx
  -- ⊢ ↑(formPerm l) (nthLe l k hk) = nthLe l k hk ↔ length l ≤ 1
  rw [formPerm_apply_nthLe _ hl, hl.nthLe_inj_iff]
  -- ⊢ (k + 1) % length l = k ↔ length l ≤ 1
  cases hn : l.length
  -- ⊢ (k + 1) % Nat.zero = k ↔ Nat.zero ≤ 1
  · exact absurd k.zero_le (hk.trans_le hn.le).not_le
    -- 🎉 no goals
  · rw [hn] at hk
    -- ⊢ (k + 1) % Nat.succ n✝ = k ↔ Nat.succ n✝ ≤ 1
    cases' (Nat.le_of_lt_succ hk).eq_or_lt with hk' hk'
    -- ⊢ (k + 1) % Nat.succ n✝ = k ↔ Nat.succ n✝ ≤ 1
    · simp [← hk', Nat.succ_le_succ_iff, eq_comm]
      -- 🎉 no goals
    · simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.succ_lt_succ_iff] using
        k.zero_le.trans_lt hk'
#align list.form_perm_apply_mem_eq_self_iff List.formPerm_apply_mem_eq_self_iff

theorem formPerm_apply_mem_ne_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x ≠ x ↔ 2 ≤ l.length := by
  rw [Ne.def, formPerm_apply_mem_eq_self_iff _ hl x hx, not_le]
  -- ⊢ 1 < length l ↔ 2 ≤ length l
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩
  -- 🎉 no goals
#align list.form_perm_apply_mem_ne_self_iff List.formPerm_apply_mem_ne_self_iff

theorem mem_of_formPerm_ne_self (l : List α) (x : α) (h : formPerm l x ≠ x) : x ∈ l := by
  suffices x ∈ { y | formPerm l y ≠ y } by
    rw [← mem_toFinset]
    exact support_formPerm_le' _ this
  simpa using h
  -- 🎉 no goals
#align list.mem_of_form_perm_ne_self List.mem_of_formPerm_ne_self

theorem formPerm_eq_self_of_not_mem (l : List α) (x : α) (h : x ∉ l) : formPerm l x = x :=
  by_contra fun H => h <| mem_of_formPerm_ne_self _ _ H
#align list.form_perm_eq_self_of_not_mem List.formPerm_eq_self_of_not_mem

theorem formPerm_eq_one_iff (hl : Nodup l) : formPerm l = 1 ↔ l.length ≤ 1 := by
  cases' l with hd tl
  -- ⊢ formPerm [] = 1 ↔ length [] ≤ 1
  · simp
    -- 🎉 no goals
  · rw [← formPerm_apply_mem_eq_self_iff _ hl hd (mem_cons_self _ _)]
    -- ⊢ formPerm (hd :: tl) = 1 ↔ ↑(formPerm (hd :: tl)) hd = hd
    constructor
    -- ⊢ formPerm (hd :: tl) = 1 → ↑(formPerm (hd :: tl)) hd = hd
    · simp (config := { contextual := true })
      -- 🎉 no goals
    · intro h
      -- ⊢ formPerm (hd :: tl) = 1
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd (mem_cons_self hd tl),
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, length_eq_zero] at h
      simp [h]
      -- 🎉 no goals
#align list.form_perm_eq_one_iff List.formPerm_eq_one_iff

theorem formPerm_eq_formPerm_iff {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 := by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length ≤ 1 ↔ l' = nil ∨ l'.length ≤ 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero]
    refine' ⟨fun h => Or.inr h, _⟩
    -- ⊢ l' = [] ∨ length l' ≤ 1 → length l' ≤ 1
    rintro (rfl | h)
    -- ⊢ length [] ≤ 1
    · simp
      -- 🎉 no goals
    · exact h
      -- 🎉 no goals
  · suffices l'.length ≤ 1 ↔ [x] ~r l' ∨ l'.length ≤ 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero, le_rfl]
    refine' ⟨fun h => Or.inr h, _⟩
    -- ⊢ [x] ~r l' ∨ length l' ≤ 1 → length l' ≤ 1
    rintro (h | h)
    -- ⊢ length l' ≤ 1
    · simp [← h.perm.length_eq]
      -- 🎉 no goals
    · exact h
      -- 🎉 no goals
  · rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩)
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
      -- 🎉 no goals
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
      -- 🎉 no goals
    · simp [-formPerm_cons_cons, formPerm_ext_iff hl hl', Nat.succ_le_succ_iff]
      -- 🎉 no goals
#align list.form_perm_eq_form_perm_iff List.formPerm_eq_formPerm_iff

theorem form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x ∈ l) (n : ℤ) :
    (formPerm l ^ n) x ∈ l := by
  by_cases h : (l.formPerm ^ n) x = x
  -- ⊢ ↑(formPerm l ^ n) x ∈ l
  · simpa [h] using hx
    -- 🎉 no goals
  · have h : x ∈ { x | (l.formPerm ^ n) x ≠ x } := h
    -- ⊢ ↑(formPerm l ^ n) x ∈ l
    rw [← set_support_apply_mem] at h
    -- ⊢ ↑(formPerm l ^ n) x ∈ l
    replace h := set_support_zpow_subset _ _ h
    -- ⊢ ↑(formPerm l ^ n) x ∈ l
    simpa using support_formPerm_le' _ h
    -- 🎉 no goals
#align list.form_perm_zpow_apply_mem_imp_mem List.form_perm_zpow_apply_mem_imp_mem

set_option linter.deprecated false in
theorem formPerm_pow_length_eq_one_of_nodup (hl : Nodup l) : formPerm l ^ length l = 1 := by
  ext x
  -- ⊢ ↑(formPerm l ^ length l) x = ↑1 x
  by_cases hx : x ∈ l
  -- ⊢ ↑(formPerm l ^ length l) x = ↑1 x
  · obtain ⟨k, hk, rfl⟩ := nthLe_of_mem hx
    -- ⊢ ↑(formPerm l ^ length l) (nthLe l k hk) = ↑1 (nthLe l k hk)
    simp [formPerm_pow_apply_nthLe _ hl, Nat.mod_eq_of_lt hk]
    -- 🎉 no goals
  · have : x ∉ { x | (l.formPerm ^ l.length) x ≠ x } := by
      intro H
      refine' hx _
      replace H := set_support_zpow_subset l.formPerm l.length H
      simpa using support_formPerm_le' _ H
    simpa using this
    -- 🎉 no goals
#align list.form_perm_pow_length_eq_one_of_nodup List.formPerm_pow_length_eq_one_of_nodup

end FormPerm

end List
