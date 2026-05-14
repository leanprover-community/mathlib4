/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Take operations on tuples

We define the `take` operation on `n`-tuples, which restricts a tuple to its first `m` elements.

* `Fin.take`: Given `h : m ≤ n`, `Fin.take m h v` for an `n`-tuple `v = (v 0, ..., v (n - 1))` is
  the `m`-tuple `(v 0, ..., v (m - 1))`.
-/

@[expose] public section

namespace Fin

open Function

variable {n : ℕ} {α : Fin n → Sort*}

section Take

/-- Take the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `m`-tuple. -/
def take (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) : (i : Fin m) → α (castLE h i) :=
  fun i ↦ v (castLE h i)

@[simp]
theorem take_apply (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin m) :
    (take m h v) i = v (castLE h i) := rfl

@[simp]
theorem take_zero (v : (i : Fin n) → α i) : take 0 n.zero_le v = fun i ↦ elim0 i := by
  ext i; exact elim0 i

@[simp]
theorem take_one {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    take 1 (Nat.le_add_left 1 n) v = (fun i => v (castLE (Nat.le_add_left 1 n) i)) := by
  ext i
  simp only [take]

@[simp]
theorem take_eq_init {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    take n n.le_succ v = init v := rfl

@[simp]
theorem take_eq_self (v : (i : Fin n) → α i) : take n (le_refl n) v = v := by
  ext i
  simp [take]

@[simp]
theorem take_take {m n' : ℕ} (h : m ≤ n') (h' : n' ≤ n) (v : (i : Fin n) → α i) :
    take m h (take n' h' v) = take m (Nat.le_trans h h') v := rfl

@[simp]
theorem take_init {α : Fin (n + 1) → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin (n + 1)) → α i) :
    take m h (init v) = take m (Nat.le_succ_of_le h) v := rfl

theorem take_repeat {α : Type*} {n' : ℕ} (m : ℕ) (h : m ≤ n) (a : Fin n' → α) :
    take (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a) = Fin.repeat m a := by
  ext i
  simp only [take, repeat_apply, modNat, val_castLE]

/-- Taking `m + 1` elements is equal to taking `m` elements and adding the `(m + 1)`th one. -/
theorem take_succ_eq_snoc (m : ℕ) (h : m < n) (v : (i : Fin n) → α i) :
    take m.succ h v = snoc (take m h.le v) (v ⟨m, h⟩) := by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by ext; simp
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc]; congr
    | cast i _ => simp

/-- `take` commutes with `update` for indices in the range of `take`. -/
@[simp]
theorem take_update_of_lt (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin m)
    (x : α (castLE h i)) : take m h (update v (castLE h i) x) = update (take m h v) i x := by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_self]
  · have : castLE h j ≠ castLE h i := by simp [h']
    simp only [take, update_of_ne h', update_of_ne this]

/-- `take` is the same after `update` for indices outside the range of `take`. -/
@[simp]
theorem take_update_of_ge (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin n) (hi : i ≥ m)
    (x : α i) : take m h (update v i x) = take m h v := by
  ext j
  have : castLE h j ≠ i := by
    refine ne_of_val_ne ?_
    simp only [val_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_of_ne this]

/-- Taking the first `m ≤ n` elements of an `addCases u v`, where `u` is an `n`-tuple, is the same
as taking the first `m` elements of `u`. -/
theorem take_addCases_left {n' : ℕ} {motive : Fin (n + n') → Sort*} (m : ℕ) (h : m ≤ n)
    (u : (i : Fin n) → motive (castAdd n' i)) (v : (i : Fin n') → motive (natAdd n i)) :
      take m (Nat.le_add_right_of_le h) (addCases u v) = take m h u := by
  ext i
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp only [take, addCases, this, val_castLE, ↓reduceDIte]
  congr

/-- Version of `take_addCases_left` that specializes `addCases` to `append`. -/
theorem take_append_left {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n) (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) : take m (Nat.le_add_right_of_le h) (append u v) = take m h u :=
  take_addCases_left m h _ _

set_option backward.isDefEq.respectTransparency false in
/-- Taking the first `n + m` elements of an `addCases u v`, where `v` is a `n'`-tuple and `m ≤ n'`,
is the same as appending `u` with the first `m` elements of `v`. -/
theorem take_addCases_right {n' : ℕ} {motive : Fin (n + n') → Sort*} (m : ℕ) (h : m ≤ n')
    (u : (i : Fin n) → motive (castAdd n' i)) (v : (i : Fin n') → motive (natAdd n i)) :
      take (n + m) (Nat.add_le_add_left h n) (addCases u v) = addCases u (take m h v) := by
  ext i
  simp only [take, addCases, val_castLE]
  by_cases h' : i < n
  · simp only [h', ↓reduceDIte]
    congr
  · simp only [h', ↓reduceDIte, subNat, castLE, Fin.cast, eqRec_eq_cast]

/-- Version of `take_addCases_right` that specializes `addCases` to `append`. -/
theorem take_append_right {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n') (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) : take (n + m) (Nat.add_le_add_left h n) (append u v)
        = append u (take m h v) :=
  take_addCases_right m h _ _

/-- `Fin.take` intertwines with `List.take` via `List.ofFn`. -/
theorem ofFn_take_eq_take_ofFn {α : Type*} {m : ℕ} (h : m ≤ n) (v : Fin n → α) :
    List.ofFn (take m h v) = (List.ofFn v).take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/-- Alternative version of `take_eq_take_list_ofFn` with `l : List α` instead of `v : Fin n → α`. -/
theorem ofFn_take_get {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    List.ofFn (take m h l.get) = l.take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/-- `Fin.take` intertwines with `List.take` via `List.get`. -/
theorem get_take_eq_take_get_comp_cast {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    (l.take m).get = take m h l.get ∘ Fin.cast (List.length_take_of_le h) := by
  ext i
  simp only [List.get_eq_getElem, List.getElem_take, comp_apply, take_apply, val_castLE, val_cast]

/-- Alternative version of `take_eq_take_list_get` with `v : Fin n → α` instead of `l : List α`. -/
theorem get_take_ofFn_eq_take_comp_cast {α : Type*} {m : ℕ} (v : Fin n → α) (h : m ≤ n) :
    ((List.ofFn v).take m).get = take m h v ∘ Fin.cast (by simp [h]) := by
  ext i
  simp [castLE]

end Take

end Fin
