/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.List.Indexes

/-!
# Dyck words

A Dyck word is a sequence consisting of an equal number `n` of symbols of two types such that
for all prefixes one symbol occurs at least as many times as the other.
If the symbols are `(` and `)` the latter restriction is equivalent to balanced brackets;
if they are `U = (1, 1)` and `D = (1, -1)` the sequence is a lattice path from `(0, 0)` to `(0, 2n)`
and the restriction requires the path to never go below the x-axis.

This file defines Dyck words and constructs their bijection with rooted binary trees,
one consequence being that the number of Dyck words with length `2n` is `catalan n`.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s.

## Main results

* `DyckPath.treeEquiv`: equivalence between Dyck words and rooted binary trees.
* `DyckPath.finiteTreeEquiv`: equivalence between Dyck words of length `2 * n` and
  rooted binary trees with `n` internal nodes.
* `DyckPath.card_isBalanced_eq_catalan `: there are `catalan n` Dyck words of length `2 * n`.

## Implementation notes

While any two-valued type could have been used for `DyckStep`, a new enumerated type is used here
to emphasise that the definition of a Dyck word does not depend on that underlying type.
-/

open List

section

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

variable (p : DyckWord) (h : p.l ≠ [])

lemma eq_zero_iff : p = 0 ↔ p.l = [] := by rw [DyckWord.ext_iff]; rfl

/-- The first element of a nonempty Dyck word is `U`. -/
lemma head_eq_U : p.l.head h = U := by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [(dyckStep_cases _).resolve_left f] using nonneg 1

/-- The last element of a nonempty Dyck word is `D`. -/
lemma getLast_eq_D : p.l.getLast h = D := by
  by_contra f; have s := p.bal
  rw [← dropLast_append_getLast h, (dyckStep_cases _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, ite_false] at s
  have := p.nonneg p.l.length.pred; omega

lemma cons_tail_dropLast_concat : U :: p.l.dropLast.tail ++ [D] = p.l := by
  have : p.l.dropLast.take 1 = [p.l.head h] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.l.dropLast_append_getLast h, ← p.l.dropLast.take_append_drop 1]
  rw [p.getLast_eq_D, drop_one, this, p.head_eq_U]
  rfl

lemma two_le_length : 2 ≤ p.l.length := by
  rw [← p.cons_tail_dropLast_concat h, length_append, length_cons, length_singleton]
  simp only [le_add_iff_nonneg_left, zero_le]

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
def denest (pos : ∀ i, 0 < i → i < p.l.length →
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

lemma denest_nest (pos : ∀ i, 0 < i → i < p.l.length →
    (p.l.take i).count D < (p.l.take i).count U) : (p.denest h pos).nest = p := by
  simpa [DyckWord.ext_iff] using p.cons_tail_dropLast_concat h

section FirstReturn

/-- `p.firstReturn` is 0 for `p = 0` and otherwise the smallest index for which `p`'s prefix
up to and including that index is also a Dyck word. -/
def firstReturn : ℕ :=
  (range p.l.length).findIdx (fun i ↦ (p.l.take (i + 1)).count U = (p.l.take (i + 1)).count D)

lemma firstReturn_pos : 0 < p.firstReturn := by
  by_contra f
  replace f : p.firstReturn = 0 := by omega
  rw [firstReturn, findIdx_eq (by simp [h])] at f
  simp only [get_range, zero_add, decide_eq_true_eq, not_lt_zero', false_implies, implies_true,
    and_true] at f
  rw [← p.cons_tail_dropLast_concat h] at f
  simp at f

lemma firstReturn_lt_length : p.firstReturn < p.l.length := by
  have lp := length_pos_of_ne_nil h
  rw [← length_range p.l.length]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.l.length - 1
  exact ⟨by omega, by rw [Nat.sub_add_cancel lp, take_all_of_le (le_refl _), p.bal]⟩

lemma count_eq_count_of_take_firstReturn_add_one :
    (p.l.take (p.firstReturn + 1)).count U = (p.l.take (p.firstReturn + 1)).count D := by
  have := findIdx_get (w := (length_range p.l.length).symm ▸ p.firstReturn_lt_length h)
  simpa [get_range, decide_eq_true_eq] using this

lemma count_lt_count_of_lt_firstReturn (i : ℕ) (hi : i < p.firstReturn) :
    (p.l.take (i + 1)).count D < (p.l.take (i + 1)).count U := by
  have ne := not_of_lt_findIdx hi
  rw [get_range, decide_eq_true_eq, ← ne_eq] at ne
  exact lt_of_le_of_ne (p.nonneg (i + 1)) ne.symm

/-- The right part of the Dyck word decomposition. -/
def rightPart : DyckWord :=
  p.drop (p.firstReturn + 1) (p.count_eq_count_of_take_firstReturn_add_one h)

/-- The left part of the Dyck word decomposition. -/
def leftPart : DyckWord :=
  (p.take (p.firstReturn + 1) (p.count_eq_count_of_take_firstReturn_add_one h)).denest
    (by simp [take, h]) (fun i lb ub ↦ by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take, min_eq_left ub.le]
      rw [show i = i - 1 + 1 by omega] at ub ⊢
      rw [Nat.add_lt_add_iff_right] at ub
      exact p.count_lt_count_of_lt_firstReturn _ ub)

@[simp]
theorem leftPart_nest_add_rightPart : (p.leftPart h).nest + p.rightPart h = p := by
  rw [DyckWord.ext_iff, leftPart, denest_nest]
  apply take_append_drop

end FirstReturn

end DyckWord

end

namespace DyckPath

/-- A `Step` is either `U` or `D`, corresponding to `(` and `)` respectively. -/
inductive Step
  | U : Step
  | D : Step
  deriving Inhabited, DecidableEq

/-- A Dyck path is a list of `Step`s. -/
abbrev _root_.DyckPath := List Step

open Step

section Defs

variable (p : DyckPath)

lemma step_cases (s : Step) : s = U ∨ s = D := by cases' s <;> tauto

lemma count_U_add_count_D_eq_length : p.count U + p.count D = p.length := by
  symm; convert p.length_eq_countP_add_countP (· == U)
  rw [count]; congr!; rename_i s
  cases' s <;> simp

/-- A Dyck path is a Dyck word if its running `D`-count never exceeds its running `U`-count
and both counts are equal at the end. -/
def IsDyckWord : Prop :=
  p.count U = p.count D ∧ ∀ i, (p.take i).count D ≤ (p.take i).count U

instance : DecidablePred IsDyckWord := fun q ↦
  decidable_of_iff
    (q.count U = q.count D ∧ ∀ i < q.length, (q.take i).count D ≤ (q.take i).count U) <| by
    constructor <;> (intro ⟨h1, h2⟩; refine' ⟨h1, _⟩)
    · intro i
      cases' lt_or_ge i q.length with hi hi
      · exact h2 i hi
      · rw [take_all_of_le hi]; exact h1.symm.le
    · intro i _; exact h2 i

end Defs

section Lemmas

variable {p : DyckPath} (bp : p.IsDyckWord)

lemma IsDyckWord.length_even : Even p.length := by
  use p.count U
  rw [← count_U_add_count_D_eq_length, bp.1]

/-- If `x` and `y` are balanced Dyck paths then so is `xy`. -/
lemma IsDyckWord.append {q : DyckPath} (bq : q.IsDyckWord) : (p ++ q).IsDyckWord := by
  simp only [IsDyckWord, take_append_eq_append_take, count_append]
  exact ⟨by rw [bp.1, bq.1], fun _ ↦ add_le_add (bp.2 _) (bq.2 _)⟩

/-- If `x` is a balanced Dyck path then so is `(x)`. -/
lemma IsDyckWord.nest : (↑[U] ++ p ++ ↑[D]).IsDyckWord := by
  simp only [IsDyckWord, take_append_eq_append_take, count_append]
  refine' ⟨by rw [bp.1]; simp [add_comm], fun i ↦ _⟩
  rw [← add_rotate (count D _), ← add_rotate (count U _)]
  apply add_le_add _ (bp.2 _)
  cases' i.eq_zero_or_pos with hi hi; · simp [hi]
  simp_rw [take_all_of_le (show [U].length ≤ i by rwa [length_singleton]),
    count_singleton', ite_true, ite_false]
  rw [add_comm _ 0]
  exact add_le_add (zero_le _) ((count_le_length _ _).trans (by simp))

/-- A balanced Dyck path is split into two parts. If one part is balanced, so is the other. -/
lemma IsDyckWord.split (i : ℕ) : IsDyckWord (p.take i) ↔ IsDyckWord (p.drop i) := by
  rw [IsDyckWord, ← p.take_append_drop i] at bp
  simp_rw [take_append_eq_append_take, count_append] at bp
  obtain ⟨b1, b2⟩ := bp
  constructor <;> intro bh
  · refine' ⟨by rw [bh.1] at b1; omega, fun j ↦ _⟩
    replace b2 := b2 (j + (p.take i).length)
    rwa [take_all_of_le (by omega), bh.1, add_le_add_iff_left, Nat.add_sub_cancel] at b2
  · refine' ⟨by rw [bh.1] at b1; omega, fun j ↦ _⟩
    cases' le_or_gt (p.take i).length j with hj hj
    · rw [take_all_of_le hj]; rw [bh.1] at b1; omega
    · replace b2 := b2 j
      simp_rw [show j - (p.take i).length = 0 by omega, take_zero, count_nil, add_zero] at b2
      exact b2

/-- If `p.take i` satisfies the equality part of `IsDyckWord`, it also satisfies the other part
and is balanced itself. -/
lemma IsDyckWord.take {i : ℕ} (h : (p.take i).count U = (p.take i).count D) :
    IsDyckWord (p.take i) := ⟨h, fun j ↦ by rw [take_take]; apply bp.2⟩

variable (np : p ≠ [])

/-- The first element of a nonempty balanced Dyck path is `U`. -/
lemma IsDyckWord.head_eq_U : p.head np = U := by
  cases' p with h _; · tauto
  by_contra f; simpa [(step_cases h).resolve_left f] using bp.2 1

/-- The last element of a nonempty balanced Dyck path is `D`. -/
lemma IsDyckWord.getLast_eq_D : p.getLast np = D := by
  by_contra f; have s := bp.1
  rw [← dropLast_append_getLast np, (step_cases _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, ite_false] at s
  have t := bp.2 p.length.pred; omega

private lemma denest_aux : p.take 1 = [p.head np] ∧ p.dropLast.take 1 = [p.head np] ∧
    p.length.pred = p.length.pred.pred + 1 := by
  cases' p with _ q; · tauto
  cases' q
  · replace bp := bp.length_even; norm_num [even_iff_two_dvd] at bp
  · refine' ⟨_, _, _⟩
    · rw [take_cons, take_zero, head_cons]
    · rw [dropLast_cons₂, take_cons, take_zero, head_cons]
    · rfl

lemma cons_tail_dropLast_concat : U :: tail (dropLast p) ++ [D] = p := by
  conv_rhs => rw [← p.dropLast_append_getLast np, ← p.dropLast.take_append_drop 1]
  rw [bp.getLast_eq_D, drop_one, (denest_aux bp np).2.1, bp.head_eq_U]
  rfl

/-- If the inequality part of `IsDyckWord` is strict in the interior of a nonempty
balanced Dyck path, the interior is itself balanced. -/
lemma IsDyckWord.denest
    (h : ∀ i (_ : 0 < i ∧ i < p.length), (p.take i).count D < (p.take i).count U) :
    IsDyckWord p.dropLast.tail := by
  obtain ⟨l1, _, l3⟩ := denest_aux bp np
  constructor
  · replace bp := (cons_tail_dropLast_concat bp np).symm ▸ bp.1
    simp_rw [count_append, count_cons, count_nil, ite_true, ite_false] at bp; omega
  · intro i
    rw [← drop_one, take_drop, dropLast_eq_take, take_take]
    have ub : min (1 + i) p.length.pred < p.length :=
      (min_le_right _ p.length.pred).trans_lt (Nat.pred_lt ((length_pos.mpr np).ne'))
    have lb : 0 < min (1 + i) p.length.pred := by
      rw [l3, add_comm, min_add_add_right]; omega
    have eq := h _ ⟨lb, ub⟩
    set j := min (1 + i) p.length.pred
    rw [← (p.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by omega), l1, bp.head_eq_U] at eq
    simp only [count_singleton', ite_true, ite_false] at eq; omega

end Lemmas

section FirstReturn

/-- Index of the first return of a Dyck path to zero. -/
def firstReturn (p : DyckPath) : ℕ :=
  (range p.length).findIdx (fun i ↦ (p.take (i + 1)).count U = (p.take (i + 1)).count D)

variable {p : DyckPath} (bp : p.IsDyckWord) (np : p ≠ [])

lemma firstReturn_lt_length : p.firstReturn < p.length := by
  have lp := length_pos_of_ne_nil np
  rw [← length_range p.length]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.length - 1
  exact ⟨by omega, by rw [Nat.sub_add_cancel lp, take_all_of_le (le_refl _), bp.1]⟩

lemma take_firstReturn_isBalanced : IsDyckWord (p.take (p.firstReturn + 1)) := by
  have := findIdx_get (w := (length_range p.length).symm ▸ firstReturn_lt_length bp np)
  simp only [get_range, decide_eq_true_eq] at this
  exact bp.take this

lemma firstReturn_pos : 0 < p.firstReturn := by
  have lp := length_pos_of_ne_nil np
  by_contra f
  replace f : p.firstReturn = 0 := by omega
  have := (take_firstReturn_isBalanced bp np).length_even
  rw [length_take, min_eq_left (by omega), f] at this
  norm_num [even_iff_two_dvd] at this

lemma take_firstReturn_ne_nil : p.take (p.firstReturn + 1) ≠ [] := by
  rw [← length_pos, length_take]; exact lt_min (by omega) (length_pos.mpr np)

theorem take_firstReturn_eq_dropLast :
    p.take p.firstReturn = (p.take (p.firstReturn + 1)).dropLast := by
  rw [dropLast_eq_take, take_take, length_take, take_eq_take]
  nth_rw 2 [← Nat.succ_pred_eq_of_pos (length_pos_of_ne_nil np)]
  rw [min_add_add_right, Nat.pred_succ, min_eq_left (Nat.le_pred_of_lt
    (firstReturn_lt_length bp np)), min_eq_left_of_lt (Nat.lt_succ_self _)]

end FirstReturn

section Decomp

/-- The left part of the Dyck word decomposition. -/
def leftPart (p : DyckPath) : DyckPath := (p.take p.firstReturn).tail
/-- The right part of the Dyck word decomposition. -/
def rightPart (p : DyckPath) : DyckPath := p.drop (p.firstReturn + 1)

variable {p : DyckPath} (bp : p.IsDyckWord) (np : p ≠ [])

lemma count_U_eq_count_D_of_firstReturn :
    (p.take (p.firstReturn + 1)).count U = (p.take (p.firstReturn + 1)).count D := by
  have := findIdx_get (w := (length_range p.length).symm ▸ firstReturn_lt_length bp np)
  simpa only [get_range, decide_eq_true_eq]

theorem leftPart_isBalanced : p.leftPart.IsDyckWord := by
  have := firstReturn_lt_length bp np
  rw [leftPart, take_firstReturn_eq_dropLast bp np]
  apply (bp.take (count_U_eq_count_D_of_firstReturn bp np)).denest
    (take_firstReturn_ne_nil np)
  intro i hi
  rw [length_take, min_eq_left (by omega)] at hi
  rw [take_take, min_eq_left_of_lt hi.2]
  have ne := not_of_lt_findIdx (show i - 1 < p.firstReturn by omega)
  rw [get_range, decide_eq_true_eq, ← ne_eq, Nat.sub_add_cancel hi.1] at ne
  exact lt_of_le_of_ne (bp.2 i) ne.symm

theorem rightPart_isBalanced : p.rightPart.IsDyckWord :=
  (bp.split _).mp <| bp.take (count_U_eq_count_D_of_firstReturn bp np)

theorem eq_U_leftPart_D_rightPart : p = ↑[U] ++ p.leftPart ++ ↑[D] ++ p.rightPart := by
  nth_rw 1 [← p.take_append_drop (p.firstReturn + 1)]; congr
  rw [leftPart, take_firstReturn_eq_dropLast bp np]
  exact (cons_tail_dropLast_concat
    (take_firstReturn_isBalanced bp np) (take_firstReturn_ne_nil np)).symm

theorem leftPart_length_lt : p.leftPart.length < p.length := by
  conv_rhs => rw [eq_U_leftPart_D_rightPart bp np]
  simp_rw [length_append, length_singleton]; omega

theorem rightPart_length_lt : p.rightPart.length < p.length := by
  conv_rhs => rw [eq_U_leftPart_D_rightPart bp np]
  simp_rw [length_append, length_singleton]; omega

variable {q : DyckPath}

theorem compose_firstReturn : (↑[U] ++ p ++ ↑[D] ++ q).firstReturn = p.length + 1 := by
  rw [firstReturn, findIdx_eq]
  swap; · simp_rw [length_range, length_append, length_singleton]; omega
  simp only [get_range, decide_eq_true_eq]
  constructor
  · simp_rw [take_append_eq_append_take (l₂ := q), length_append, length_singleton,
      show p.length + 1 + 1 - (1 + p.length + 1) = 0 by omega, take_zero, append_nil]
    rw [take_all_of_le, bp.nest.1]; simp_rw [length_append, length_singleton]; omega
  · intro j hji
    simp_rw [append_assoc _ _ [D], singleton_append, take_append_eq_append_take, length_cons,
      length_append, show j + 1 - (p.length + [D].length).succ = 0 by omega, take_zero,
      append_nil, take_cons, count_cons, ite_true, ite_false, take_append_eq_append_take,
      show j - p.length = 0 by omega, take_zero, append_nil]
    have := bp.2 j; omega

theorem compose_leftPart_eq_leftPart : (↑[U] ++ p ++ ↑[D] ++ q).leftPart = p := by
  rw [leftPart, compose_firstReturn bp, append_assoc, take_append_eq_append_take,
    length_append, length_singleton, show p.length + 1 - (1 + p.length) = 0 by omega, take_zero,
    append_nil, take_append_eq_append_take, length_singleton, Nat.add_sub_cancel,
    take_all_of_le (by rw [length_singleton]; omega), take_all_of_le (le_refl _), singleton_append,
    tail_cons]

theorem compose_rightPart_eq_rightPart : (↑[U] ++ p ++ ↑[D] ++ q).rightPart = q := by
  rw [rightPart, compose_firstReturn bp, drop_append_eq_append_drop, length_append, length_append,
    length_singleton, length_singleton, show p.length + 1 + 1 - (1 + p.length + 1) = 0 by omega,
    drop_zero, drop_eq_nil_of_le, nil_append]
  simp_rw [length_append, length_singleton]; omega

end Decomp

section Tree

open Tree

/-- Convert a balanced Dyck path to a binary rooted tree. -/
def treeEquivToFun (st : { p : DyckPath // p.IsDyckWord }) : Tree Unit :=
  if e : st.1 = [] then nil else by
    obtain ⟨p, bp⟩ := st
    have := leftPart_length_lt bp e
    have := rightPart_length_lt bp e
    exact treeEquivToFun ⟨_, leftPart_isBalanced bp e⟩ △
      treeEquivToFun ⟨_, rightPart_isBalanced bp e⟩
termination_by st.1.length

/-- Convert a binary rooted tree to a Dyck path (that it is balanced is shown in
`isBalanced_treeEquivInvFun'`). -/
def treeEquivInvFun' (tr : Tree Unit) : DyckPath :=
  match tr with
  | Tree.nil => []
  | Tree.node _ l r => ↑[U] ++ treeEquivInvFun' l ++ ↑[D] ++ treeEquivInvFun' r

theorem isBalanced_treeEquivInvFun' (tr : Tree Unit) : (treeEquivInvFun' tr).IsDyckWord := by
  induction' tr with _ l r bl br
  · rw [treeEquivInvFun']; decide
  · rw [treeEquivInvFun']; exact bl.nest.append br

/-- Convert a binary rooted tree to a balanced Dyck path. -/
def treeEquivInvFun (tr : Tree Unit) : { p : DyckPath // p.IsDyckWord } :=
  ⟨treeEquivInvFun' tr, isBalanced_treeEquivInvFun' tr⟩

@[nolint unusedHavesSuffices]
theorem treeEquiv_left_inv (st) {n : ℕ} (hl : st.1.length = n) :
    treeEquivInvFun (treeEquivToFun st) = st := by
  induction' n using Nat.strongInductionOn with n ih generalizing st
  cases' eq_or_ne st.1 [] with j j
  · rw [treeEquivToFun, Subtype.mk.injEq]
    simp_rw [j, dite_true, treeEquivInvFun, treeEquivInvFun']
  rw [treeEquivToFun, Subtype.mk.injEq]
  simp_rw [j, dite_false, treeEquivInvFun, treeEquivInvFun']
  let p := st.1
  let bp := st.2
  change _ = p; rw [p.eq_U_leftPart_D_rightPart bp j]
  have tl := ih _ (hl ▸ leftPart_length_lt bp j) ⟨_, leftPart_isBalanced bp j⟩ rfl
  have tr := ih _ (hl ▸ rightPart_length_lt bp j) ⟨_, rightPart_isBalanced bp j⟩ rfl
  rw [treeEquivInvFun, Subtype.mk.injEq] at tl tr
  congr

@[nolint unusedHavesSuffices]
theorem treeEquiv_right_inv (tr) : treeEquivToFun (treeEquivInvFun tr) = tr := by
  induction' tr with _ l r ttl ttr
  · simp_rw [treeEquivInvFun, treeEquivInvFun']
    rw [treeEquivToFun]; simp
  simp_rw [treeEquivInvFun, treeEquivInvFun']
  rw [treeEquivToFun]
  have pp : (↑[U] ++ treeEquivInvFun' l ++ ↑[D] ++ treeEquivInvFun' r) ≠ [] := by simp
  simp_rw [pp, dite_false, node.injEq, true_and]
  rw [treeEquivInvFun] at ttl ttr
  simp_rw [compose_leftPart_eq_leftPart (isBalanced_treeEquivInvFun' _),
    compose_rightPart_eq_rightPart (isBalanced_treeEquivInvFun' _)]
  exact ⟨ttl, ttr⟩

/-- Equivalence between Dyck words and rooted binary trees. -/
def treeEquiv : { p : DyckPath // p.IsDyckWord } ≃ Tree Unit where
  toFun := treeEquivToFun
  invFun := treeEquivInvFun
  left_inv st := treeEquiv_left_inv st rfl
  right_inv := treeEquiv_right_inv

@[nolint unusedHavesSuffices]
theorem length_eq_two_mul_iff_numNodes_eq {n : ℕ} (st : { p : DyckPath // p.IsDyckWord }) :
    st.1.length = 2 * n ↔ (treeEquiv st).numNodes = n := by
  induction' n using Nat.strongInductionOn with n ih generalizing st
  cases' eq_or_ne st.1 [] with j j
  · rw [j, length_nil, zero_eq_mul, treeEquiv, Equiv.coe_fn_mk, treeEquivToFun]
    simp_rw [j, dite_true, numNodes]; tauto
  rw [treeEquiv, Equiv.coe_fn_mk, treeEquivToFun]
  simp_rw [j, dite_false, numNodes]
  obtain ⟨p, bp⟩ := st
  dsimp only at j ⊢
  have bl := leftPart_isBalanced bp j
  have br := rightPart_isBalanced bp j
  obtain ⟨sl, le⟩ := bl.length_even
  obtain ⟨sr, re⟩ := br.length_even
  rw [← two_mul] at le re
  conv_lhs =>
    rw [eq_U_leftPart_D_rightPart bp j, length_append, length_append, length_append,
      length_singleton, length_singleton, le, re,
      show 1 + 2 * sl + 1 + 2 * sr = 2 * (sl + sr + 1) by omega]
  constructor <;> intro h
  · have tl := (ih sl (by omega) ⟨_, bl⟩).mp le
    have tr := (ih sr (by omega) ⟨_, br⟩).mp re
    dsimp only [treeEquiv, Equiv.coe_fn_mk] at tl tr
    rw [tl, tr]; exact mul_left_cancel₀ two_ne_zero h
  · set wl := Subtype.mk _ bl
    set wr := Subtype.mk _ br
    have ntwl_lt : (treeEquivToFun wl).numNodes < n := by omega
    have ntwr_lt : (treeEquivToFun wr).numNodes < n := by omega
    have el := ih _ ntwl_lt ⟨_, bl⟩
    have er := ih _ ntwr_lt ⟨_, br⟩
    simp only [treeEquiv, Equiv.coe_fn_mk, iff_true] at el er
    rw [le, Nat.mul_left_cancel_iff zero_lt_two] at el
    rw [re, Nat.mul_left_cancel_iff zero_lt_two] at er
    rw [← el, ← er] at h; omega

/-- Equivalence between Dyck words of length `2 * n` and
rooted binary trees with `n` internal nodes. -/
def finiteTreeEquiv (n : ℕ) :
    { p : DyckPath // p.IsDyckWord ∧ p.length = 2 * n } ≃ treesOfNumNodesEq n where
  toFun := fun ⟨p, ⟨bp, len⟩⟩ ↦
    ⟨treeEquiv ⟨p, bp⟩, by rw [mem_treesOfNumNodesEq, ← length_eq_two_mul_iff_numNodes_eq, len]⟩
  invFun := fun ⟨tr, sz⟩ ↦
    ⟨(treeEquiv.symm tr).1, ⟨(treeEquiv.symm tr).2, by rwa [length_eq_two_mul_iff_numNodes_eq,
      ← mem_treesOfNumNodesEq, Equiv.apply_symm_apply]⟩⟩
  left_inv := fun ⟨p, ⟨bp, len⟩⟩ ↦ by simp only [Equiv.symm_apply_apply]
  right_inv := fun ⟨tr, sz⟩ ↦ by simp only [Subtype.coe_eta, Equiv.apply_symm_apply]

instance instFintypeDyckWords {n : ℕ} :
    Fintype { p : DyckPath // p.IsDyckWord ∧ p.length = 2 * n } :=
  Fintype.ofEquiv _ (finiteTreeEquiv n).symm

/-- There are `catalan n` Dyck words of length `2 * n`. -/
theorem card_isBalanced_eq_catalan (n : ℕ) :
    Fintype.card { p : DyckPath // p.IsDyckWord ∧ p.length = 2 * n } = catalan n := by
  rw [← Fintype.ofEquiv_card (finiteTreeEquiv n), ← treesOfNumNodesEq_card_eq_catalan]
  convert Fintype.card_coe _

end Tree

end DyckPath
