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

* Prove the bijection between Dyck words and rooted binary trees.
-/

open List

/-- A `DyckStep` is either `U` or `D`, corresponding to `(` and `)` respectively. -/
inductive DyckStep
  | U : DyckStep
  | D : DyckStep
  deriving Inhabited, DecidableEq

open DyckStep

lemma dyckStep_cases (s : DyckStep) : s = U ∨ s = D := by cases' s <;> tauto

/-- A Dyck word is a list of `DyckStep`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s. -/
@[ext]
structure DyckWord where
  /-- The underlying list -/
  l : List DyckStep
  /-- There are as many `U`s as `D`s -/
  bal : l.count U = l.count D
  /-- Each prefix has as least as many `U`s as `D`s -/
  nonneg i : (l.take i).count D ≤ (l.take i).count U
  deriving DecidableEq

instance : Add DyckWord where
  add p q := ⟨p.l ++ q.l, by simp only [count_append, p.bal, q.bal], by
    simp only [take_append_eq_append_take, count_append]
    exact fun _ ↦ add_le_add (p.nonneg _) (q.nonneg _)⟩

instance : Zero DyckWord := ⟨[], by simp, by simp⟩

/-- Dyck words form an additive monoid under concatenation, with the empty word as 0. -/
instance : AddMonoid DyckWord where
  add_zero p := by ext1; exact append_right_eq_self.mpr rfl
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec

namespace DyckWord

variable (p q : DyckWord)

lemma eq_zero_iff : p = 0 ↔ p.l = [] := by rw [DyckWord.ext_iff]; rfl

/-- The first element of a nonempty Dyck word is `U`. -/
lemma head_eq_U (h : p.l ≠ []) : p.l.head h = U := by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [(dyckStep_cases _).resolve_left f] using nonneg 1

/-- The last element of a nonempty Dyck word is `D`. -/
lemma getLast_eq_D (h : p.l ≠ []) : p.l.getLast h = D := by
  by_contra f; have s := p.bal
  rw [← dropLast_append_getLast h, (dyckStep_cases _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, ite_false] at s
  have := p.nonneg p.l.length.pred; omega

lemma cons_tail_dropLast_concat (h : p.l ≠ []) : U :: p.l.dropLast.tail ++ [D] = p.l := by
  have : p.l.dropLast.take 1 = [p.l.head h] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.l.dropLast_append_getLast h, ← p.l.dropLast.take_append_drop 1]
  rw [p.getLast_eq_D, drop_one, this, p.head_eq_U]
  rfl

/-- Prefix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in it are equal. -/
def take (i : ℕ) (hi : (p.l.take i).count U = (p.l.take i).count D) : DyckWord where
  l := p.l.take i
  bal := hi
  nonneg k := by rw [take_take]; exact p.nonneg (min k i)

/-- Suffix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in the prefix
are equal. -/
def drop (i : ℕ) (hi : (p.l.take i).count U = (p.l.take i).count D) : DyckWord where
  l := p.l.drop i
  bal := by
    have := p.bal
    rw [← take_append_drop i p.l, count_append, count_append] at this
    omega
  nonneg k := by
    rw [show i = min i (i + k) by omega, ← take_take] at hi
    rw [take_drop, ← add_le_add_iff_left (((p.l.take (i + k)).take i).count U),
      ← count_append, hi, ← count_append, take_append_drop]
    exact p.nonneg _

/-- Nest `p` in one pair of brackets, i.e. `x` becomes `(x)`. -/
def nest : DyckWord where
  l := [U] ++ p.l ++ [D]
  bal := by simp [p.bal]
  nonneg i := by
    simp only [take_append_eq_append_take, count_append]
    rw [← add_rotate (count D _), ← add_rotate (count U _)]
    apply add_le_add _ (p.nonneg _)
    cases' i.eq_zero_or_pos with hi hi; · simp [hi]
    rw [take_all_of_le (show [U].length ≤ i by rwa [length_singleton]), count_singleton']
    simp only [ite_true, ite_false]
    rw [add_comm]
    exact add_le_add (zero_le _) ((count_le_length _ _).trans (by simp))

/-- Denest `p`, i.e. `(x)` becomes `x`, given that `p` is strictly positive in its interior
(this ensures that `x` is a Dyck word). -/
def denest (h : p.l ≠ []) (pos : ∀ i, 0 < i → i < p.l.length →
    (p.l.take i).count D < (p.l.take i).count U) : DyckWord where
  l := p.l.dropLast.tail
  bal := by
    have := p.bal
    rw [← p.cons_tail_dropLast_concat h, count_append, count_cons] at this
    simpa using this
  nonneg i := by
    have l1 : p.l.take 1 = [p.l.head h] := by rcases p with - | - <;> tauto
    have l3 : p.l.length.pred = p.l.length.pred.pred + 1 := by
      rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
      · tauto
      · rename_i bal _
        cases s <;> simp at bal
      · tauto
    rw [← drop_one, take_drop, dropLast_eq_take, take_take]
    have ub : min (1 + i) p.l.length.pred < p.l.length :=
      (min_le_right _ p.l.length.pred).trans_lt (Nat.pred_lt ((length_pos.mpr h).ne'))
    have lb : 0 < min (1 + i) p.l.length.pred := by
      rw [l3, add_comm, min_add_add_right]; omega
    have eq := pos _ lb ub
    set j := min (1 + i) p.l.length.pred
    rw [← (p.l.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by omega), l1, p.head_eq_U] at eq
    simp only [count_singleton', ite_true, ite_false] at eq
    omega

lemma denest_nest (h : p.l ≠ []) (pos : ∀ i, 0 < i → i < p.l.length →
    (p.l.take i).count D < (p.l.take i).count U) : (p.denest h pos).nest = p := by
  simpa [DyckWord.ext_iff] using p.cons_tail_dropLast_concat h

section Semilength

/-- The semilength of a Dyck word is half of the number of `DyckStep`s in it, or equivalently
its number of `U`s. -/
def semilength : ℕ := p.l.count U

@[simp] lemma semilength_zero : semilength 0 = 0 := by rfl
@[simp] lemma semilength_add : (p + q).semilength = p.semilength + q.semilength := count_append ..
@[simp] lemma semilength_nest : p.nest.semilength = p.semilength + 1 := by simp [semilength, nest]

@[simp]
lemma two_mul_semilength_eq_length : 2 * p.semilength = p.l.length := by
  nth_rw 1 [two_mul, semilength, p.bal, semilength]
  convert (p.l.length_eq_countP_add_countP (· == D)).symm
  rw [count]; congr!; rename_i s; cases' s <;> tauto

end Semilength
