/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Order.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Defs

/-!
# `Take` and `Drop` lemmas for lists

This file provides lemmas about `List.take` and `List.drop` and related functions.
-/

assert_not_exists GroupWithZero
assert_not_exists Lattice
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Ring
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-! ### take, drop -/

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_getElem_cons h, take, take]
  simp

@[simp] lemma take_eq_self_iff (x : List α) {n : ℕ} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp; omega, take_of_length_le⟩

@[simp] lemma take_self_eq_iff (x : List α) {n : ℕ} : x = x.take n ↔ x.length ≤ n := by
  rw [Eq.comm, take_eq_self_iff]

@[simp] lemma take_eq_left_iff {x y : List α} {n : ℕ} :
    (x ++ y).take n = x.take n ↔ y = [] ∨ n ≤ x.length := by
  simp [take_append_eq_append_take, Nat.sub_eq_zero_iff_le, Or.comm]

@[simp] lemma left_eq_take_iff {x y : List α} {n : ℕ} :
    x.take n = (x ++ y).take n ↔ y = [] ∨ n ≤ x.length := by
  rw [Eq.comm]; apply take_eq_left_iff

@[simp] lemma drop_take_append_drop (x : List α) (m n : ℕ) :
    (x.drop m).take n ++ x.drop (m + n) = x.drop m := by rw [← drop_drop, take_append_drop]

/-- Compared to `drop_take_append_drop`, the order of summands is swapped. -/
@[simp] lemma drop_take_append_drop' (x : List α) (m n : ℕ) :
    (x.drop m).take n ++ x.drop (n + m) = x.drop m := by rw [Nat.add_comm, drop_take_append_drop]

/-- `take_concat_get` in simp normal form -/
lemma take_concat_get' (l : List α) (i : ℕ) (h : i < l.length) :
  l.take i ++ [l[i]] = l.take (i + 1) := by simp

theorem cons_getElem_drop_succ {l : List α} {n : Nat} {h : n < l.length} :
    l[n] :: l.drop (n + 1) = l.drop n :=
  (drop_eq_getElem_cons h).symm

theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 :=
  (drop_eq_getElem_cons n.2).symm

lemma drop_length_sub_one {l : List α} (h : l ≠ []) : l.drop (l.length - 1) = [l.getLast h] := by
  induction l with
  | nil => aesop
  | cons a l ih =>
    by_cases hl : l = []
    · aesop
    rw [length_cons, Nat.add_one_sub_one, List.drop_length_cons hl a]
    aesop

section TakeI

variable [Inhabited α]

@[simp]
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)

@[simp]
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)

theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, _, _ => rfl
  | _ + 1, _ :: _, h => congr_arg (cons _) <| takeI_eq_take <| le_of_succ_le_succ h

@[simp]
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)

theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left

end TakeI

/- Porting note: in mathlib3 we just had `take` and `take'`. Now we have `take`, `takeI`, and
  `takeD`. The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
theorem takeD_length : ∀ n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- `takeD_nil` is already in batteries

theorem takeD_eq_take : ∀ {n} {l : List α} a, n ≤ length l → takeD n l a = take n l
  | 0, _, _, _ => rfl
  | _ + 1, _ :: _, a, h => congr_arg (cons _) <| takeD_eq_take a <| le_of_succ_le_succ h

@[simp]
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)

theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ := by
  rw [← h]; apply takeD_left

end TakeD

/-! ### splitAt and splitOn -/

section SplitAtOn

@[deprecated (since := "2024-08-17")] alias splitAt_eq_take_drop := splitAt_eq

end SplitAtOn

/-! ### filter -/

section Filter

variable (p)

/- Porting note: need a helper theorem for span.loop. -/
theorem span.loop_eq_take_drop :
    ∀ l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]

@[simp]
theorem span_eq_take_drop (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using span.loop_eq_take_drop p l []

theorem dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).get ⟨0, hl⟩) := by
  induction' l with hd tl IH
  · cases hl
  · simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

@[deprecated (since := "2024-08-19")] alias dropWhile_nthLe_zero_not := dropWhile_get_zero_not

variable {p} {l : List α}

@[simp]
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [dropWhile]
  · by_cases hp : p x <;> simp [hp, IH]

@[simp]
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp
  · by_cases hp : p x <;> simp [hp, IH]

@[simp]
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩) := by
  induction' l with x xs IH
  · simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  · by_cases hp : p x <;> simp [hp, IH]

theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx

theorem takeWhile_takeWhile (p q : α → Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction' l with hd tl IH
  · simp
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]

theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

variable (p) (l)

lemma find?_eq_head?_dropWhile_not :
    l.find? p = (l.dropWhile (fun x ↦ ! (p x))).head? := by
  induction l
  case nil => simp
  case cons head tail hi =>
    set ph := p head with phh
    rcases ph with rfl | rfl
    · have phh' : ¬(p head = true) := by simp [phh.symm]
      rw [find?_cons_of_neg _ phh', dropWhile_cons_of_pos]
      · exact hi
      · simpa using phh
    · rw [find?_cons_of_pos _ phh.symm, dropWhile_cons_of_neg]
      · simp
      · simpa using phh

lemma find?_not_eq_head?_dropWhile :
    l.find? (fun x ↦ ! (p x)) = (l.dropWhile p).head? := by
  convert l.find?_eq_head?_dropWhile_not ?_
  simp

variable {p} {l}

lemma find?_eq_head_dropWhile_not (h : ∃ x ∈ l, p x) :
    l.find? p = some ((l.dropWhile (fun x ↦ ! (p x))).head (by simpa using h)) := by
  rw [l.find?_eq_head?_dropWhile_not p, ← head_eq_iff_head?_eq_some]

lemma find?_not_eq_head_dropWhile (h : ∃ x ∈ l, ¬p x) :
    l.find? (fun x ↦ ! (p x)) = some ((l.dropWhile p).head (by simpa using h)) := by
  convert l.find?_eq_head_dropWhile_not ?_
  · simp
  · simpa using h

end Filter

/-! ### Miscellaneous lemmas -/

theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs
  · cases xs <;> simp [dropSlice]
  · cases xs <;> simp [dropSlice, *, Nat.succ_add]

@[simp]
theorem length_dropSlice (i j : ℕ) (xs : List α) :
    (List.dropSlice i j xs).length = xs.length - min j (xs.length - i) := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => simp
      | succ n => simp_all [xs_ih]; omega
    · simp [xs_ih]; omega

theorem length_dropSlice_lt (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    (List.dropSlice i j xs).length < xs.length := by
  simp; omega

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-07-25")]
theorem sizeOf_dropSlice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    SizeOf.sizeOf (List.dropSlice i j xs) < SizeOf.sizeOf xs := by
  induction xs generalizing i j hj with
  | nil => cases hi
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => contradiction
      | succ n =>
        dsimp only [drop]; apply lt_of_le_of_lt (drop_sizeOf_le xs n)
        simp only [cons.sizeOf_spec]; omega
    · simp only [cons.sizeOf_spec, Nat.add_lt_add_iff_left]
      apply xs_ih _ j hj
      apply lt_of_succ_lt_succ hi

end List
