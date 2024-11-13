/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
import Mathlib.Tactic.Common
import Mathlib.Algebra.Order.Group.Nat

/-!
# Lists and sequences

This file defines operations relating `List A` and `ℕ → A`, in particular append, take, tail, and
proves basic properties
-/
variable {A B : Type*} (f : A → B) (a₀ : A) (x y : List A) (a b : ℕ → A) (m n : ℕ)

namespace InfList
/-- append an element to the front of an infinite sequence -/
def cons : ℕ → A := fun n => match n with
  | 0 => a₀
  | n + 1 => a n
@[simp] lemma cons_zero : cons a₀ a 0 = a₀ := rfl
@[simp] lemma cons_succ : cons a₀ a (n + 1) = a n := rfl

/-- append a finite list to the front of an infinite sequence -/
instance : HAppend (List A) (ℕ → A) (ℕ → A) where hAppend x as := x.foldr cons as
@[simp] lemma nil_append : ([] : List A) ++ a = a := rfl
@[simp] lemma cons_append : (a₀ :: x) ++ a = cons a₀ (x ++ a) := rfl
@[simp] lemma append_assoc : x ++ y ++ a = x ++ (y ++ a) := x.foldr_append cons a y
lemma append_eq_cons : [a₀] ++ a = cons a₀ a := by dsimp
lemma append_cons : x ++ cons a₀ a = x ++ [a₀] ++ a := by simp

/-- drop the first element of an infinite sequence -/
def tail : ℕ → A := (a ∘ (· + 1))
@[simp] lemma eval_tail : (tail a) n = a (n + 1) := rfl
@[simp] lemma eval_drop : (tail^[m] a) n = a (m + n) := by
  induction' m with m ih generalizing a
  · simp
  · rw [Function.iterate_succ, Function.comp_apply, ih (tail a), Nat.succ_add]; rfl
@[simp] lemma tail_cons : tail (cons a₀ a) = a := rfl
@[simp] lemma cons_tail : cons (a 0) (tail a) = a := by ext n; cases n <;> rfl

variable {x a n} in
lemma eval_append_left (h : n < x.length) : (x ++ a) n = x[n] := by
  induction' x with b x ih generalizing n
  · simp at h
  · rcases n with (_ | n)
    · simp
    · simp [ih (by simpa using h)]
@[simp] lemma eval_append_right : (x ++ a) (x.length + n) = a n := by
  induction' x <;> simp [Nat.succ_add, *]
@[simp] lemma eval_append_zero : (x ++ a) x.length = a 0 := eval_append_right x a 0
lemma append_left_injective (h : x ++ a = x ++ b) : a = b := by
  ext n; simpa using congr_fun h (x.length + n)
@[simp] lemma append_left_inj : x ++ a = x ++ b ↔ a = b :=
  ⟨append_left_injective x a b, by simp (config := {contextual := true})⟩
lemma append_right_injective (h : x ++ a = y ++ b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← eval_append_left, ← eval_append_left, h]
@[simp] lemma map_append : f ∘ (x ++ a) = x.map f ++ f ∘ a := by
  ext n; rcases lt_or_ge n x.length with h | h
  · simp [eval_append_left h, eval_append_left (x := x.map f) (by simpa)]
  · obtain ⟨n, rfl⟩ := le_iff_exists_add.mp h
    nth_rw 2 [← x.length_map f]; simp only [Function.comp_apply, eval_append_right]

/-- `x.take n` is the list of the first n entries of x -/
def _root_.Function.take : ℕ → (ℕ → A) → List A
  | 0, _ => []
  | n + 1, a => a 0 :: take n (tail a)
@[simp] lemma take_zero : a.take 0 = [] := rfl
lemma take_succ : a.take (n + 1) = a 0 :: (tail a).take n := rfl
@[simp] lemma take_length : (a.take n).length = n := by
  induction' n generalizing a <;> simp [Function.take, *]
@[simp] lemma take_append : a.take n ++ tail^[n] a = a := by
  induction' n with n ih generalizing a <;> simp [take_succ, *]
lemma append_take (x : List A) (a : ℕ →  A) (n : ℕ) :
    x ++ (a.take n) = (x ++ a).take (x.length + n) := by
  induction' x <;> simp [Function.take, add_comm, *]
@[simp] lemma take_eval {a : ℕ → A} n m (h : m < (a.take n).length) : (a.take n)[m] = a m := by
  nth_rw 2 [← take_append a n]; rw [eval_append_left]

lemma take_append_of_le_length (x : List A) (a : ℕ → A) {n : ℕ} (h : n ≤ x.length) :
    (x ++ a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intros
  simp_rw [take_eval, List.getElem_take]; rw [eval_append_left]
lemma take_add : a.take (m + n) = a.take m ++ ((tail^[m] a).take n) := by
  apply append_right_injective _ _ (tail^[m + n] a) (tail^[n] (tail^[m] a)) <;> simp [take_append]
lemma take_succ_eq_append : a.take (n + 1) = a.take n ++ [a n] := by
  rw [take_add, take_succ, eval_drop, add_zero, take_zero]
@[simp] lemma take_take : (a.take n).take m = a.take (min m n) := by
  rcases le_total m n with h | h
  · apply List.ext_getElem <;> simp [h, List.getElem_take']
  · simp [h, List.take_of_length_le]
@[gcongr] lemma take_prefix_take_left (h : m ≤ n) : a.take m <+: a.take n := by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix
@[simp] lemma take_prefix : a.take m <+: a.take n ↔ m ≤ n :=
  ⟨fun h ↦ by simpa using h.length_le, take_prefix_take_left a m n⟩
lemma map_take : (a.take n).map f = (f ∘ a).take n := by
  apply List.ext_getElem <;> simp

lemma take_drop : (tail^[m] a).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp
lemma drop_append_of_le_length (x : List A) (a : ℕ → A) {n : ℕ} (h : n ≤ x.length) :
    tail^[n] (x ++ a) = x.drop n ++ a := by
  obtain ⟨m, hm⟩ := le_iff_exists_add.mp h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [eval_drop, eval_append_left, eval_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := le_iff_exists_add.mp hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [eval_drop, ← add_assoc, ← hm, eval_append_right, hm', eval_append_right]

end InfList
