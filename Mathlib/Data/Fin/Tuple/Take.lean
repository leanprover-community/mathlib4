/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Batteries.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Take operations on tuples

We define the `take` operation on `n`-tuples, which restricts a tuple to its first `m` elements.

* `Fin.take`: Given `h : m ≤ n`, `Fin.take m h v` for a `n`-tuple `v = (v 0, ..., v (n - 1))` is the
  `m`-tuple `(v 0, ..., v (m - 1))`.
-/

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
theorem take_of_succ {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    take n n.le_succ v = init v := by
  ext i
  simp only [Nat.succ_eq_add_one, take, init]
  congr

@[simp]
theorem take_all (v : (i : Fin n) → α i) : take n (le_refl n) v = v := by
  ext i
  simp [take]

@[simp]
theorem take_init {α : Fin (n + 1) → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin (n + 1)) → α i) :
    take m h (init v) = take m (Nat.le_succ_of_le h) v := by
  ext i
  simp only [take, init]
  congr

@[simp]
theorem take_repeat {α : Type*} {n' : ℕ} (m : ℕ) (h : m ≤ n) (a : Fin n' → α) :
    take (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a) = Fin.repeat m a := by
  ext i
  simp only [take, repeat_apply, modNat, coe_castLE]

/-- Taking `m + 1` elements is equal to taking `m` elements and adding the `(m + 1)`th one. -/
theorem take_succ_eq_snoc (m : ℕ) (h : m < n) (v : (i : Fin n) → α i) :
    take m.succ h v = snoc (take m (le_of_lt h) v) (v ⟨m, h⟩) := by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by ext; simp
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc, castLT]; congr
    | cast i _ => simp [snoc_cast_add]

/-- `take` commutes with `update` for indices in the range of `take`. -/
@[simp]
theorem take_update_of_lt (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin m)
    (x : α (castLE h i)) : take m h (update v (castLE h i) x) = update (take m h v) i x := by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_same]
  · have : castLE h j ≠ castLE h i := by simp [h']
    simp only [take, update_noteq h', update_noteq this]

/-- `take` is the same after `update` for indices outside the range of `take`. -/
@[simp]
theorem take_update_of_ge (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin n) (hi : i ≥ m)
    (x : α i) : take m h (update v i x) = take m h v := by
  ext j
  have : castLE h j ≠ i := by
    refine ne_of_val_ne ?_
    simp only [coe_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_noteq this]

/-- Taking the first `m ≤ n` elements of an `append u v`, where `u` is a `n`-tuple, is the same as
taking the first `m` elements of `u`. -/
theorem take_append_left {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n) (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) : take m (Nat.le_add_right_of_le h) (append u v) = take m h u := by
  ext i
  have : castLE (Nat.le_add_right_of_le h) i = castAdd n' (castLE h i) := rfl
  simp only [take, append_left, this]

/-- Taking the first `n + m` elements of an `append u v`, where `v` is a `n'`-tuple and `m ≤ n'`,
is the same as appending `u` with the first `m` elements of `v`. -/
theorem take_append_right {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n') (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) : take (n + m) (Nat.add_le_add_left h n) (append u v)
        = append u (take m h v) := by
  ext i
  by_cases h' : i < n
  · have : castLE (Nat.add_le_add_left h n) i = castAdd n' ⟨i.val, h'⟩ := by
      simp only [castAdd_mk]
      rfl
    rw [take, this, append_left]
    have : i = castAdd m ⟨i.val, h'⟩ := by simp only [castAdd_mk]
    conv_rhs => rw [this, append_left]
  · simp only [not_lt] at h'
    let j := subNat n (cast (Nat.add_comm _ _) i) h'
    have : i = natAdd n j := by simp [j]
    conv_rhs => rw [this, append_right, take]
    have : castLE (Nat.add_le_add_left h n) i = natAdd n (castLE h j) := by
      simp_all only [natAdd_subNat_cast, j]
      ext : 1
      simp_all only [coe_castLE, coe_natAdd, coe_subNat, coe_cast, Nat.add_sub_cancel']
    rw [take, this, append_right]

/-- `Fin.take` intertwines with `List.take` via `List.ofFn`. -/
theorem list_ofFn_take {α : Type*} {m : ℕ} (h : m ≤ n) (v : Fin n → α) :
    List.ofFn (take m h v) = (List.ofFn v).take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/-- Alternative version of `list_ofFn_take` with `l : List α` instead of `v : Fin n → α`. -/
theorem list_ofFn_take_get {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    List.ofFn (take m h l.get) = l.take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/-- `Fin.take` intertwines with `List.take` via `List.get`. -/
theorem list_take_get_heq {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    HEq (l.take m).get (take m h l.get) :=
  (Fin.heq_fun_iff (List.length_take_of_le h)).mpr (by simp)

/-- Alternative version of `list_take_get_heq` with `v : Fin n → α` instead of `l : List α`. -/
theorem list_ofFn_take_get_heq {α : Type*} {m : ℕ} (v : Fin n → α) (h : m ≤ n) :
    HEq ((List.ofFn v).take m).get (take m h v) :=
  (Fin.heq_fun_iff (by simp [h])).mpr (by simp)

end Take

end Fin
