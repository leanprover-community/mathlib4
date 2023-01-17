/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.of_fn
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.List.Basic
import Mathbin.Data.List.Join

/-!
# Lists from functions

Theorems and lemmas for dealing with `list.of_fn`, which converts a function on `fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `of_fn`

- `list.length_of_fn`, which tells us the length of such a list
- `list.nth_of_fn`, which tells us the nth element of such a list
- `list.array_eq_of_fn`, which interprets the list form of an array as such a list.
- `list.equiv_sigma_tuple`, which is an `equiv` between lists and the functions that generate them
  via `list.of_fn`.
-/


universe u

variable {α : Type u}

open Nat

namespace List

theorem length_of_fn_aux {n} (f : Fin n → α) : ∀ m h l, length (ofFnAux f m h l) = length l + m
  | 0, h, l => rfl
  | succ m, h, l => (length_of_fn_aux m _ _).trans (succ_add _ _)
#align list.length_of_fn_aux List.length_of_fn_aux

/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_of_fn {n} (f : Fin n → α) : length (ofFn f) = n :=
  (length_of_fn_aux f _ _ _).trans (zero_add _)
#align list.length_of_fn List.length_of_fn

theorem nth_of_fn_aux {n} (f : Fin n → α) (i) :
    ∀ m h l, (∀ i, get? l i = ofFnNthVal f (i + m)) → get? (ofFnAux f m h l) i = ofFnNthVal f i
  | 0, h, l, H => H i
  | succ m, h, l, H =>
    nth_of_fn_aux m _ _
      (by
        intro j; cases' j with j
        · simp only [nth, of_fn_nth_val, zero_add, dif_pos (show m < n from h)]
        · simp only [nth, H, add_succ, succ_add])
#align list.nth_of_fn_aux List.nth_of_fn_aux

/-- The `n`th element of a list -/
@[simp]
theorem nth_of_fn {n} (f : Fin n → α) (i) : get? (ofFn f) i = ofFnNthVal f i :=
  (nth_of_fn_aux f _ _ _ _) fun i => by
    simp only [of_fn_nth_val, dif_neg (not_lt.2 (Nat.le_add_left n i))] <;> rfl
#align list.nth_of_fn List.nth_of_fn

theorem nth_le_of_fn {n} (f : Fin n → α) (i : Fin n) :
    nthLe (ofFn f) i ((length_of_fn f).symm ▸ i.2) = f i :=
  Option.some.inj <| by
    rw [← nth_le_nth] <;> simp only [List.nth_of_fn, of_fn_nth_val, Fin.eta, dif_pos i.is_lt]
#align list.nth_le_of_fn List.nth_le_of_fn

@[simp]
theorem nth_le_of_fn' {n} (f : Fin n → α) {i : ℕ} (h : i < (ofFn f).length) :
    nthLe (ofFn f) i h = f ⟨i, length_of_fn f ▸ h⟩ :=
  nth_le_of_fn f ⟨i, length_of_fn f ▸ h⟩
#align list.nth_le_of_fn' List.nth_le_of_fn'

@[simp]
theorem map_of_fn {β : Type _} {n : ℕ} (f : Fin n → α) (g : α → β) :
    map g (ofFn f) = ofFn (g ∘ f) :=
  ext_nthLe (by simp) fun i h h' => by simp
#align list.map_of_fn List.map_of_fn

/-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
theorem array_eq_of_fn {n} (a : Array' n α) : a.toList = ofFn a.read :=
  by
  suffices ∀ {m h l}, DArray.revIterateAux a (fun i => cons) m h l = ofFnAux (DArray.read a) m h l
    from this
  intros ; induction' m with m IH generalizing l; · rfl
  simp only [DArray.revIterateAux, of_fn_aux, IH]
#align list.array_eq_of_fn List.array_eq_of_fn

@[congr]
theorem of_fn_congr {m n : ℕ} (h : m = n) (f : Fin m → α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i) :=
  by
  subst h
  simp_rw [Fin.cast_refl, OrderIso.refl_apply]
#align list.of_fn_congr List.of_fn_congr

/-- `of_fn` on an empty domain is the empty list. -/
@[simp]
theorem of_fn_zero (f : Fin 0 → α) : ofFn f = [] :=
  rfl
#align list.of_fn_zero List.of_fn_zero

@[simp]
theorem of_fn_succ {n} (f : Fin (succ n) → α) : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  by
  suffices
    ∀ {m h l}, ofFnAux f (succ m) (succ_le_succ h) l = f 0 :: ofFnAux (fun i => f i.succ) m h l from
    this
  intros ; induction' m with m IH generalizing l; · rfl
  rw [of_fn_aux, IH]; rfl
#align list.of_fn_succ List.of_fn_succ

theorem of_fn_succ' {n} (f : Fin (succ n) → α) :
    ofFn f = (ofFn fun i => f i.cast_succ).concat (f (Fin.last _)) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, concat_nil, of_fn_succ, of_fn_zero]
    rfl
  · rw [of_fn_succ, IH, of_fn_succ, concat_cons, Fin.castSucc_zero]
    congr 3
    simp_rw [Fin.castSucc_fin_succ]
#align list.of_fn_succ' List.of_fn_succ'

@[simp]
theorem of_fn_eq_nil_iff {n : ℕ} {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [of_fn_zero, of_fn_succ, eq_self_iff_true, Nat.succ_ne_zero]
#align list.of_fn_eq_nil_iff List.of_fn_eq_nil_iff

theorem last_of_fn {n : ℕ} (f : Fin n → α) (h : ofFn f ≠ [])
    (hn : n - 1 < n := Nat.pred_lt <| of_fn_eq_nil_iff.Not.mp h) :
    getLast (ofFn f) h = f ⟨n - 1, hn⟩ := by simp [last_eq_nth_le]
#align list.last_of_fn List.last_of_fn

theorem last_of_fn_succ {n : ℕ} (f : Fin n.succ → α)
    (h : ofFn f ≠ [] := mt of_fn_eq_nil_iff.mp (Nat.succ_ne_zero _)) :
    getLast (ofFn f) h = f (Fin.last _) :=
  last_of_fn f h
#align list.last_of_fn_succ List.last_of_fn_succ

/-- Note this matches the convention of `list.of_fn_succ'`, putting the `fin m` elements first. -/
theorem of_fn_add {m n} (f : Fin (m + n) → α) :
    List.ofFn f =
      (List.ofFn fun i => f (Fin.castAdd n i)) ++ List.ofFn fun j => f (Fin.natAdd m j) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, append_nil, Fin.castAdd_zero, Fin.cast_refl]
    rfl
  · rw [of_fn_succ', of_fn_succ', IH, append_concat]
    rfl
#align list.of_fn_add List.of_fn_add

/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem of_fn_mul {m n} (f : Fin (m * n) → α) :
    List.ofFn f =
      List.join
        (List.ofFn fun i : Fin m =>
          List.ofFn fun j : Fin n =>
            f
              ⟨i * n + j,
                calc
                  ↑i * n + j < (i + 1) * n :=
                    (add_lt_add_left j.Prop _).trans_eq (add_one_mul _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_right _ i.Prop
                  ⟩) :=
  by
  induction' m with m IH
  · simp_rw [of_fn_zero, zero_mul, of_fn_zero, join]
  · simp_rw [of_fn_succ', succ_mul, join_concat, of_fn_add, IH]
    rfl
#align list.of_fn_mul List.of_fn_mul

/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem of_fn_mul' {m n} (f : Fin (m * n) → α) :
    List.ofFn f =
      List.join
        (List.ofFn fun i : Fin n =>
          List.ofFn fun j : Fin m =>
            f
              ⟨m * i + j,
                calc
                  m * i + j < m * (i + 1) :=
                    (add_lt_add_left j.Prop _).trans_eq (mul_add_one _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_left _ i.Prop
                  ⟩) :=
  by simp_rw [mul_comm m n, mul_comm m, of_fn_mul, Fin.cast_mk]
#align list.of_fn_mul' List.of_fn_mul'

theorem of_fn_nth_le : ∀ l : List α, (ofFn fun i => nthLe l i i.2) = l
  | [] => rfl
  | a :: l => by
    rw [of_fn_succ]
    congr
    simp only [Fin.val_succ]
    exact of_fn_nth_le l
#align list.of_fn_nth_le List.of_fn_nth_le

-- not registered as a simp lemma, as otherwise it fires before `forall_mem_of_fn_iff` which
-- is much more useful
theorem mem_of_fn {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ a ∈ Set.range f :=
  by
  simp only [mem_iff_nth_le, Set.mem_range, nth_le_of_fn']
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨_, h⟩, fun ⟨i, hi⟩ => ⟨i.1, (length_of_fn f).symm ▸ i.2, by simpa using hi⟩⟩
#align list.mem_of_fn List.mem_of_fn

@[simp]
theorem forall_mem_of_fn_iff {n : ℕ} {f : Fin n → α} {P : α → Prop} :
    (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j) := by simp only [mem_of_fn, Set.forall_range_iff]
#align list.forall_mem_of_fn_iff List.forall_mem_of_fn_iff

@[simp]
theorem of_fn_const (n : ℕ) (c : α) : (ofFn fun i : Fin n => c) = repeat c n :=
  (Nat.recOn n (by simp)) fun n ihn => by simp [ihn]
#align list.of_fn_const List.of_fn_const

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equivSigmaTuple : List α ≃ Σn, Fin n → α
    where
  toFun l := ⟨l.length, fun i => l.nthLe (↑i) i.2⟩
  invFun f := List.ofFn f.2
  left_inv := List.of_fn_nth_le
  right_inv := fun ⟨n, f⟩ =>
    Fin.sigma_eq_of_eq_comp_cast (length_of_fn _) <| funext fun i => nth_le_of_fn' f i.Prop
#align list.equiv_sigma_tuple List.equivSigmaTuple

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using list.of_fn_rec`. -/
@[elab_as_elim]
def ofFnRec {C : List α → Sort _} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) (l : List α) : C l :=
  cast (congr_arg _ l.of_fn_nth_le) <| h l.length fun i => l.nthLe (↑i) i.2
#align list.of_fn_rec List.ofFnRec

@[simp]
theorem of_fn_rec_of_fn {C : List α → Sort _} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) {n : ℕ}
    (f : Fin n → α) : @ofFnRec _ C h (List.ofFn f) = h _ f :=
  equivSigmaTuple.right_inverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩
#align list.of_fn_rec_of_fn List.of_fn_rec_of_fn

theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _)(f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.Surjective.exists.trans Sigma.exists
#align list.exists_iff_exists_tuple List.exists_iff_exists_tuple

theorem forall_iff_forall_tuple {P : List α → Prop} :
    (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.Surjective.forall.trans Sigma.forall
#align list.forall_iff_forall_tuple List.forall_iff_forall_tuple

/-- `fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
theorem of_fn_inj' {m n : ℕ} {f : Fin m → α} {g : Fin n → α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σn, Fin n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.Injective.eq_iff.symm
#align list.of_fn_inj' List.of_fn_inj'

/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
theorem of_fn_injective {n : ℕ} : Function.Injective (ofFn : (Fin n → α) → List α) := fun f g h =>
  eq_of_heq <| by injection of_fn_inj'.mp h
#align list.of_fn_injective List.of_fn_injective

/-- A special case of `list.of_fn_inj'` for when the two functions are indexed by defeq `n`. -/
@[simp]
theorem of_fn_inj {n : ℕ} {f g : Fin n → α} : ofFn f = ofFn g ↔ f = g :=
  of_fn_injective.eq_iff
#align list.of_fn_inj List.of_fn_inj

end List

