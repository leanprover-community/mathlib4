/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Nodup

/-!
# Dyck words

A Dyck word is a sequence consisting of an equal number `n` of symbols of two types such that
for all prefixes one symbol occurs at least as many times as the other.
If the symbols are `(` and `)` the latter restriction is equivalent to balanced brackets;
if they are `U = (1, 1)` and `D = (1, -1)` the sequence is a lattice path from `(0, 0)` to `(0, 2n)`
and the restriction requires the path to never go below the x-axis.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s.
* `DyckWord.semilength`: semilength (half the length) of a Dyck word.

## Implementation notes

While any two-valued type could have been used for `DyckStep`, a new enumerated type is used here
to emphasise that the definition of a Dyck word does not depend on that underlying type.

## TODO

* Prove the bijection between Dyck words and rooted binary trees
(https://github.com/leanprover-community/mathlib4/pull/9781).
-/

open List

/-- A `DyckStep` is either `U` or `D`, corresponding to `(` and `)` respectively. -/
inductive DyckStep
  | U : DyckStep
  | D : DyckStep
  deriving Inhabited, DecidableEq

/-- Named in analogy to `Bool.dichotomy`. -/
lemma DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D := by cases s <;> tauto

open DyckStep

/-- A Dyck word is a list of `DyckStep`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s. -/
@[ext]
structure DyckWord where
  /-- The underlying list -/
  toList : List DyckStep
  /-- There are as many `U`s as `D`s -/
  count_U_eq_count_D : toList.count U = toList.count D
  /-- Each prefix has as least as many `U`s as `D`s -/
  count_D_le_count_U i : (toList.take i).count D ≤ (toList.take i).count U
  deriving DecidableEq

attribute [coe] DyckWord.toList
instance : Coe DyckWord (List DyckStep) := ⟨DyckWord.toList⟩

instance : Add DyckWord where
  add p q := ⟨p ++ q, by
    simp only [count_append, p.count_U_eq_count_D, q.count_U_eq_count_D], by
    simp only [take_append_eq_append_take, count_append]
    exact fun _ ↦ add_le_add (p.count_D_le_count_U _) (q.count_D_le_count_U _)⟩

instance : Zero DyckWord := ⟨[], by simp, by simp⟩

/-- Dyck words form an additive monoid under concatenation, with the empty word as 0. -/
instance : AddMonoid DyckWord where
  add_zero p := by ext1; exact append_nil _
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec

namespace DyckWord

variable (p q : DyckWord)

lemma toList_eq_nil : p.toList = [] ↔ p = 0 := by rw [DyckWord.ext_iff]; rfl

/-- The first element of a nonempty Dyck word is `U`. -/
lemma head_eq_U (h : p.toList ≠ []) : p.toList.head h = U := by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [s.dichotomy.resolve_left f] using nonneg 1

/-- The last element of a nonempty Dyck word is `D`. -/
lemma getLast_eq_D (h : p.toList ≠ []) : p.toList.getLast h = D := by
  by_contra f; have s := p.count_U_eq_count_D
  rw [← dropLast_append_getLast h, (dichotomy _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); omega

lemma cons_tail_dropLast_concat (h : p.toList ≠ []) :
    U :: p.toList.dropLast.tail ++ [D] = p := by
  have : p.toList.dropLast.take 1 = [p.toList.head h] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.toList.dropLast_append_getLast h, ← p.toList.dropLast.take_append_drop 1]
  rw [p.getLast_eq_D, drop_one, this, p.head_eq_U]
  rfl

/-- Prefix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in it are equal. -/
def take (i : ℕ) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.take i
  count_U_eq_count_D := hi
  count_D_le_count_U k := by rw [take_take]; exact p.count_D_le_count_U (min k i)

/-- Suffix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in the prefix
are equal. -/
def drop (i : ℕ) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.drop i
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← take_append_drop i p.toList, count_append, count_append] at this
    omega
  count_D_le_count_U k := by
    rw [show i = min i (i + k) by omega, ← take_take] at hi
    rw [take_drop, ← add_le_add_iff_left (((p.toList.take (i + k)).take i).count U),
      ← count_append, hi, ← count_append, take_append_drop]
    exact p.count_D_le_count_U _

/-- Nest `p` in one pair of brackets, i.e. `x` becomes `(x)`. -/
def nest : DyckWord where
  toList := [U] ++ p ++ [D]
  count_U_eq_count_D := by simp [p.count_U_eq_count_D]
  count_D_le_count_U i := by
    simp only [take_append_eq_append_take, count_append]
    rw [← add_rotate (count D _), ← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · simp [hi]
    rw [take_of_length_le (show [U].length ≤ i by rwa [length_singleton]), count_singleton']
    simp only [ite_true, ite_false]
    rw [add_comm]
    exact add_le_add (zero_le _) ((count_le_length _ _).trans (by simp))

/-- Denest `p`, i.e. `(x)` becomes `x`, given that `p` is strictly positive in its interior
(this ensures that `x` is a Dyck word). -/
def denest (h : p.toList ≠ []) (pos : ∀ i, 0 < i → i < p.toList.length →
    (p.toList.take i).count D < (p.toList.take i).count U) : DyckWord where
  toList := p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← p.cons_tail_dropLast_concat h, count_append, count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    have l1 : p.toList.take 1 = [p.toList.head h] := by rcases p with - | - <;> tauto
    have l3 : p.toList.length - 1 = p.toList.length - 1 - 1 + 1 := by
      rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
      · tauto
      · rename_i bal _
        cases s <;> simp at bal
      · tauto
    rw [← drop_one, take_drop, dropLast_eq_take, take_take]
    have ub : min (1 + i) (p.toList.length - 1) < p.toList.length :=
      (min_le_right _ p.toList.length.pred).trans_lt (Nat.pred_lt ((length_pos.mpr h).ne'))
    have lb : 0 < min (1 + i) (p.toList.length - 1) := by
      rw [l3, add_comm, min_add_add_right]; omega
    have eq := pos _ lb ub
    set j := min (1 + i) (p.toList.length - 1)
    rw [← (p.toList.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by omega), l1, p.head_eq_U] at eq
    simp only [count_singleton', ite_true, ite_false] at eq
    omega

lemma denest_nest (h : p.toList ≠ []) (pos : ∀ i, 0 < i → i < p.toList.length →
    (p.toList.take i).count D < (p.toList.take i).count U) : (p.denest h pos).nest = p := by
  simpa [DyckWord.ext_iff] using p.cons_tail_dropLast_concat h

section Semilength

/-- The semilength of a Dyck word is half of the number of `DyckStep`s in it, or equivalently
its number of `U`s. -/
def semilength : ℕ := p.toList.count U

@[simp] lemma semilength_zero : semilength 0 = 0 := rfl
@[simp] lemma semilength_add : (p + q).semilength = p.semilength + q.semilength := count_append ..
@[simp] lemma semilength_nest : p.nest.semilength = p.semilength + 1 := by simp [semilength, nest]

lemma semilength_eq_count_D : p.semilength = p.toList.count D := by
  rw [← count_U_eq_count_D]; rfl

@[simp]
lemma two_mul_semilength_eq_length : 2 * p.semilength = p.toList.length := by
  nth_rw 1 [two_mul, semilength, p.count_U_eq_count_D, semilength]
  convert (p.toList.length_eq_countP_add_countP (· == D)).symm
  rw [count]; congr!; rename_i s; cases s <;> tauto

end Semilength

end DyckWord
