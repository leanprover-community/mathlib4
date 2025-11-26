/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Batteries.Data.List.Count
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Tactic.Positivity

/-!
# Dyck words

A Dyck word is a sequence consisting of an equal number `n` of symbols of two types such that
for all prefixes one symbol occurs at least as many times as the other.
If the symbols are `(` and `)` the latter restriction is equivalent to balanced brackets;
if they are `U = (1, 1)` and `D = (1, -1)` the sequence is a lattice path from `(0, 0)` to `(0, 2n)`
and the restriction requires the path to never go below the x-axis.

This file defines Dyck words and constructs their bijection with rooted binary trees,
one consequence being that the number of Dyck words with length `2 * n` is `catalan n`.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
  at least as many `U`s as `D`s.
* `DyckWord.semilength`: semilength (half the length) of a Dyck word.
* `DyckWord.firstReturn`: for a nonempty word, the index of the `D` matching the initial `U`.

## Main results

* `DyckWord.equivTree`: equivalence between Dyck words and rooted binary trees.
  See the docstrings of `DyckWord.equivTreeToFun` and `DyckWord.equivTreeInvFun` for details.
* `DyckWord.equivTreesOfNumNodesEq`: equivalence between Dyck words of length `2 * n` and
  rooted binary trees with `n` internal nodes.
* `DyckWord.card_dyckWord_semilength_eq_catalan`:
  there are `catalan n` Dyck words of length `2 * n` or semilength `n`.

## Implementation notes

While any two-valued type could have been used for `DyckStep`, a new enumerated type is used here
to emphasise that the definition of a Dyck word does not depend on that underlying type.
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
  /-- Each prefix has at least as many `U`s as `D`s -/
  count_D_le_count_U i : (toList.take i).count D ≤ (toList.take i).count U
  deriving DecidableEq

attribute [coe] DyckWord.toList
instance : Coe DyckWord (List DyckStep) := ⟨DyckWord.toList⟩

instance : Add DyckWord where
  add p q := ⟨p ++ q, by
    simp only [count_append, p.count_U_eq_count_D, q.count_U_eq_count_D], by
    simp only [take_append, count_append]
    exact fun _ ↦ add_le_add (p.count_D_le_count_U _) (q.count_D_le_count_U _)⟩

instance : Zero DyckWord := ⟨[], by simp, by simp⟩

/-- Dyck words form an additive cancellative monoid under concatenation,
with the empty word as 0. -/
instance : AddCancelMonoid DyckWord where
  add_zero p := by ext1; exact append_nil _
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec
  add_left_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_left h
  add_right_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_right h

namespace DyckWord

variable {p q : DyckWord}

lemma toList_eq_nil : p.toList = [] ↔ p = 0 := by rw [DyckWord.ext_iff]; rfl
lemma toList_ne_nil : p.toList ≠ [] ↔ p ≠ 0 := toList_eq_nil.ne

/-- The only Dyck word that is an additive unit is the empty word. -/
instance : Unique (AddUnits DyckWord) where
  uniq p := by
    obtain ⟨a, b, h, -⟩ := p
    obtain ⟨ha, hb⟩ := append_eq_nil_iff.mp (toList_eq_nil.mpr h)
    congr
    · exact toList_eq_nil.mp ha
    · exact toList_eq_nil.mp hb

variable (h : p ≠ 0)

/-- The first element of a nonempty Dyck word is `U`. -/
lemma head_eq_U (p : DyckWord) (h) : p.toList.head h = U := by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [s.dichotomy.resolve_left f] using nonneg 1

/-- The last element of a nonempty Dyck word is `D`. -/
lemma getLast_eq_D (p : DyckWord) (h) : p.toList.getLast h = D := by
  by_contra f; have s := p.count_U_eq_count_D
  rw [← dropLast_append_getLast h, (dichotomy _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, reduceCtorEq, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); cutsat

include h in
lemma cons_tail_dropLast_concat : U :: p.toList.dropLast.tail ++ [D] = p := by
  have h' := toList_ne_nil.mpr h
  have : p.toList.dropLast.take 1 = [p.toList.head h'] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.toList.dropLast_append_getLast h', ← p.toList.dropLast.take_append_drop 1]
  rw [getLast_eq_D, drop_one, this, head_eq_U]
  rfl

variable (p) in
/-- Prefix of a Dyck word as a Dyck word, given that the count of `U`s and `D`s in it are equal. -/
def take (i : ℕ) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.take i
  count_U_eq_count_D := hi
  count_D_le_count_U k := by rw [take_take]; exact p.count_D_le_count_U (min k i)

variable (p) in
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

variable (p) in
/-- Nest `p` in one pair of brackets, i.e. `x` becomes `(x)`. -/
def nest : DyckWord where
  toList := [U] ++ p ++ [D]
  count_U_eq_count_D := by simp [p.count_U_eq_count_D]
  count_D_le_count_U i := by
    simp only [take_append, count_append]
    rw [← add_rotate (count D _), ← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · simp [hi]
    rw [take_of_length_le (show [U].length ≤ i by rwa [length_singleton]), count_singleton']
    simp only [reduceCtorEq, ite_false]
    rw [add_comm]
    exact add_le_add (zero_le _) (count_le_length.trans (by simp))

@[simp] lemma nest_ne_zero : p.nest ≠ 0 := by simp [← toList_ne_nil, nest]

variable (p) in
/-- A property stating that `p` is nonempty and strictly positive in its interior,
i.e. is of the form `(x)` with `x` a Dyck word. -/
def IsNested : Prop :=
  p ≠ 0 ∧ ∀ ⦃i⦄, 0 < i → i < p.toList.length → (p.toList.take i).count D < (p.toList.take i).count U

protected lemma IsNested.nest : p.nest.IsNested := ⟨nest_ne_zero, fun i lb ub ↦ by
  simp_rw [nest, length_append, length_singleton] at ub ⊢
  rw [take_append_of_le_length (by rw [singleton_append, length_cons]; cutsat),
    take_append, take_of_length_le (by rw [length_singleton]; cutsat),
    length_singleton, singleton_append, count_cons_of_ne (by simp), count_cons_self,
    Nat.lt_add_one_iff]
  exact p.count_D_le_count_U _⟩

variable (p) in
/-- Denest `p`, i.e. `(x)` becomes `x`, given that `p.IsNested`. -/
def denest (hn : p.IsNested) : DyckWord where
  toList := p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← cons_tail_dropLast_concat hn.1, count_append, count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    replace h := toList_ne_nil.mpr hn.1
    have l1 : p.toList.take 1 = [p.toList.head h] := by rcases p with - | - <;> tauto
    have l3 : p.toList.length - 1 = p.toList.length - 1 - 1 + 1 := by
      rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
      · tauto
      · rename_i bal _
        cases s <;> simp at bal
      · tauto
    rw [← drop_one, take_drop, dropLast_eq_take, take_take]
    have ub : min (1 + i) (p.toList.length - 1) < p.toList.length :=
      (min_le_right _ p.toList.length.pred).trans_lt (Nat.pred_lt ((length_pos_iff.mpr h).ne'))
    have lb : 0 < min (1 + i) (p.toList.length - 1) := by omega
    have eq := hn.2 lb ub
    set j := min (1 + i) (p.toList.length - 1)
    rw [← (p.toList.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by omega), l1, head_eq_U] at eq
    simp only [count_singleton', ite_true] at eq
    omega

variable (p) in
lemma nest_denest (hn) : (p.denest hn).nest = p := by
  simpa [DyckWord.ext_iff] using p.cons_tail_dropLast_concat hn.1

variable (p) in
lemma denest_nest : p.nest.denest .nest = p := by
  simp_rw [nest, denest, DyckWord.ext_iff, dropLast_concat]; rfl

section Semilength

variable (p) in
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

section FirstReturn

variable (p) in
/-- `p.firstReturn` is 0 if `p = 0` and the index of the `D` matching the initial `U` otherwise. -/
def firstReturn : ℕ :=
  (range p.toList.length).findIdx fun i ↦
    (p.toList.take (i + 1)).count U = (p.toList.take (i + 1)).count D

@[simp] lemma firstReturn_zero : firstReturn 0 = 0 := rfl

include h in
lemma firstReturn_pos : 0 < p.firstReturn := by
  rw [← not_le, Nat.le_zero, firstReturn, findIdx_eq, getElem_range]
  · simp only [not_lt_zero', IsEmpty.forall_iff]
    rw [← p.cons_tail_dropLast_concat h]
    simp
  · rw [length_range, length_pos_iff]
    exact toList_ne_nil.mpr h

include h in
lemma firstReturn_lt_length : p.firstReturn < p.toList.length := by
  have lp := length_pos_of_ne_nil (toList_ne_nil.mpr h)
  rw [← length_range (n := p.toList.length)]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.toList.length - 1
  exact ⟨by cutsat, by rw [Nat.sub_add_cancel lp, take_of_length_le (le_refl _),
    p.count_U_eq_count_D]⟩

include h in
lemma count_take_firstReturn_add_one :
    (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 1)).count D := by
  have := findIdx_getElem
    (w := (length_range (n := p.toList.length)).symm ▸ firstReturn_lt_length h)
  simpa using this

lemma count_D_lt_count_U_of_lt_firstReturn {i : ℕ} (hi : i < p.firstReturn) :
    (p.toList.take (i + 1)).count D < (p.toList.take (i + 1)).count U := by
  have ne := not_of_lt_findIdx hi
  rw [decide_eq_false_iff_not, ← ne_eq, getElem_range] at ne
  exact lt_of_le_of_ne (p.count_D_le_count_U (i + 1)) ne.symm

@[simp]
lemma firstReturn_add : (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn := by
  split_ifs with h; · simp [h]
  have u : (p + q).toList = p.toList ++ q.toList := rfl
  rw [firstReturn, findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    have v := firstReturn_lt_length h
    constructor
    · rw [take_append, show p.firstReturn + 1 - p.toList.length = 0 by cutsat,
        take_zero, append_nil, count_take_firstReturn_add_one h]
    · intro j hj
      rw [take_append, show j + 1 - p.toList.length = 0 by cutsat,
        take_zero, append_nil]
      simpa using (count_D_lt_count_U_of_lt_firstReturn hj).ne'
  · rw [length_range, u, length_append]
    exact Nat.lt_add_right _ (firstReturn_lt_length h)

@[simp]
lemma firstReturn_nest : p.nest.firstReturn = p.toList.length + 1 := by
  have u : p.nest.toList = U :: p.toList ++ [D] := rfl
  rw [firstReturn, findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    constructor
    · rw [take_of_length_le (by simp), ← u, p.nest.count_U_eq_count_D]
    · intro j hj
      simp_rw [cons_append, take_succ_cons, count_cons, beq_self_eq_true, ite_true,
        beq_iff_eq, reduceCtorEq, ite_false, take_append,
        show j - p.toList.length = 0 by cutsat, take_zero, append_nil]
      have := p.count_D_le_count_U j
      simp only [add_zero, decide_eq_false_iff_not, ne_eq]
      cutsat
  · simp_rw [length_range, u, length_append, length_cons]
    exact Nat.lt_add_one _

variable (p) in
/-- The left part of the Dyck word decomposition,
inside the `U, D` pair that `firstReturn` refers to. `insidePart 0 = 0`. -/
def insidePart : DyckWord :=
  if h : p = 0 then 0 else
  (p.take (p.firstReturn + 1) (count_take_firstReturn_add_one h)).denest
    ⟨by rw [← toList_ne_nil, take]; simpa using toList_ne_nil.mpr h, fun i lb ub ↦ by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take, min_eq_left ub.le]
      rw [show i = i - 1 + 1 by cutsat] at ub ⊢
      rw [Nat.add_lt_add_iff_right] at ub
      exact count_D_lt_count_U_of_lt_firstReturn ub⟩

variable (p) in
/-- The right part of the Dyck word decomposition,
outside the `U, D` pair that `firstReturn` refers to. `outsidePart 0 = 0`. -/
def outsidePart : DyckWord :=
  if h : p = 0 then 0 else p.drop (p.firstReturn + 1) (count_take_firstReturn_add_one h)

@[simp] lemma insidePart_zero : insidePart 0 = 0 := by simp [insidePart]
@[simp] lemma outsidePart_zero : outsidePart 0 = 0 := by simp [outsidePart]

include h in
@[simp]
lemma insidePart_add : (p + q).insidePart = p.insidePart := by
  simp_rw [insidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, take]
  congr 3
  exact take_append_of_le_length (firstReturn_lt_length h)

include h in
@[simp]
lemma outsidePart_add : (p + q).outsidePart = p.outsidePart + q := by
  simp_rw [outsidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, drop]
  exact drop_append_of_le_length (firstReturn_lt_length h)

@[simp]
lemma insidePart_nest : p.nest.insidePart = p := by
  simp_rw [insidePart, nest_ne_zero, dite_false, firstReturn_nest]
  convert p.denest_nest; rw [DyckWord.ext_iff]; apply take_of_length_le
  simp_rw [nest, length_append, length_singleton]; cutsat

@[simp]
lemma outsidePart_nest : p.nest.outsidePart = 0 := by
  simp_rw [outsidePart, nest_ne_zero, dite_false, firstReturn_nest]
  rw [DyckWord.ext_iff]; apply drop_of_length_le
  simp_rw [nest, length_append, length_singleton]; cutsat

include h in
@[simp]
theorem nest_insidePart_add_outsidePart : p.insidePart.nest + p.outsidePart = p := by
  simp_rw [insidePart, outsidePart, h, dite_false, nest_denest, DyckWord.ext_iff]
  apply take_append_drop

include h in
lemma semilength_insidePart_add_semilength_outsidePart_add_one :
    p.insidePart.semilength + p.outsidePart.semilength + 1 = p.semilength := by
  rw [← congrArg semilength (nest_insidePart_add_outsidePart h), semilength_add, semilength_nest,
    add_right_comm]

include h in
theorem semilength_insidePart_lt : p.insidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  cutsat

include h in
theorem semilength_outsidePart_lt : p.outsidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  cutsat

end FirstReturn

section Order

instance : Preorder DyckWord where
  le := Relation.ReflTransGen (fun p q ↦ p = q.insidePart ∨ p = q.outsidePart)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

lemma le_add_self (p q : DyckWord) : q ≤ p + q := by
  by_cases h : p = 0
  · simp [h]
  · have := semilength_outsidePart_lt h
    exact (le_add_self p.outsidePart q).trans
      (Relation.ReflTransGen.single (Or.inr (outsidePart_add h).symm))
termination_by p.semilength

variable (p) in protected lemma zero_le : 0 ≤ p := add_zero p ▸ le_add_self p 0

lemma infix_of_le (h : p ≤ q) : p.toList <:+: q.toList := by
  induction h with
  | refl => exact infix_refl _
  | tail _pm mq ih =>
    rename_i m r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · have : [U] ++ r.insidePart ++ [D] ++ r.outsidePart = r :=
        DyckWord.ext_iff.mp (nest_insidePart_add_outsidePart hr)
      grind

lemma le_of_suffix (h : p.toList <:+ q.toList) : p ≤ q := by
  obtain ⟨r', h⟩ := h
  have hc : (q.toList.take (q.toList.length - p.toList.length)).count U =
      (q.toList.take (q.toList.length - p.toList.length)).count D := by
    have hq := q.count_U_eq_count_D
    rw [← h] at hq ⊢
    rw [count_append, count_append, p.count_U_eq_count_D, Nat.add_right_cancel_iff] at hq
    simp [hq]
  let r : DyckWord := q.take _ hc
  have e : r' = r := by
    simp_rw [r, take, ← h, length_append, add_tsub_cancel_right, take_left']
  rw [e] at h; replace h : r + p = q := DyckWord.ext h; rw [← h]; exact le_add_self ..

/-- Partial order on Dyck words: `p ≤ q` if a (possibly empty) sequence of
`insidePart` and `outsidePart` operations can turn `q` into `p`. -/
instance : PartialOrder DyckWord where
  le_antisymm p q pq qp := by
    have h₁ := infix_of_le pq
    have h₂ := infix_of_le qp
    exact DyckWord.ext <| h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le

protected lemma pos_iff_ne_zero : 0 < p ↔ p ≠ 0 := by
  rw [ne_comm, iff_comm, ne_iff_lt_iff_le]
  exact DyckWord.zero_le p

lemma monotone_semilength : Monotone semilength := fun p q pq ↦ by
  induction pq with
  | refl => rfl
  | tail _ mq ih =>
    rename_i m r _
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · rcases mq with hm | hm
      · exact ih.trans (hm ▸ semilength_insidePart_lt hr).le
      · exact ih.trans (hm ▸ semilength_outsidePart_lt hr).le

lemma strictMono_semilength : StrictMono semilength := fun p q pq ↦ by
  obtain ⟨plq, pnq⟩ := lt_iff_le_and_ne.mp pq
  apply lt_of_le_of_ne (monotone_semilength plq)
  contrapose! pnq
  replace pnq := congr(2 * $(pnq))
  simp_rw [two_mul_semilength_eq_length] at pnq
  exact DyckWord.ext ((infix_of_le plq).eq_of_length pnq)

end Order

section Tree

open Tree

/-- Convert a Dyck word to a binary rooted tree.

`f(0) = nil`. For a nonzero word find the `D` that matches the initial `U`,
which has index `p.firstReturn`, then let `x` be everything strictly between said `U` and `D`,
and `y` be everything strictly after said `D`. `p = x.nest + y` with `x, y` (possibly empty)
Dyck words. `f(p) = f(x) △ f(y)`, where △ (defined in `Mathlib/Data/Tree.lean`) joins two subtrees
to a new root node. -/
private def equivTreeToFun (p : DyckWord) : Tree Unit :=
  if h : p = 0 then nil else
    have := semilength_insidePart_lt h
    have := semilength_outsidePart_lt h
    equivTreeToFun p.insidePart △ equivTreeToFun p.outsidePart
termination_by p.semilength

/-- Convert a binary rooted tree to a Dyck word.

`g(nil) = 0`. A nonempty tree with left subtree `l` and right subtree `r`
is sent to `g(l).nest + g(r)`. -/
private def equivTreeInvFun : Tree Unit → DyckWord
  | Tree.nil => 0
  | Tree.node _ l r => (equivTreeInvFun l).nest + equivTreeInvFun r

@[nolint unusedHavesSuffices]
private lemma equivTree_left_inv (p) : equivTreeInvFun (equivTreeToFun p) = p := by
  by_cases h : p = 0
  · simp [h, equivTreeToFun, equivTreeInvFun]
  · rw [equivTreeToFun]
    simp_rw [h, dite_false, equivTreeInvFun]
    have := semilength_insidePart_lt h
    have := semilength_outsidePart_lt h
    rw [equivTree_left_inv p.insidePart, equivTree_left_inv p.outsidePart]
    exact nest_insidePart_add_outsidePart h
termination_by p.semilength

@[nolint unusedHavesSuffices]
private lemma equivTree_right_inv : ∀ t, equivTreeToFun (equivTreeInvFun t) = t
  | Tree.nil => by simp [equivTreeInvFun, equivTreeToFun]
  | Tree.node _ _ _ => by simp [equivTreeInvFun, equivTreeToFun, equivTree_right_inv]

/-- Equivalence between Dyck words and rooted binary trees. -/
def equivTree : DyckWord ≃ Tree Unit where
  toFun := equivTreeToFun
  invFun := equivTreeInvFun
  left_inv := equivTree_left_inv
  right_inv := equivTree_right_inv

@[nolint unusedHavesSuffices]
lemma semilength_eq_numNodes_equivTree (p) : p.semilength = (equivTree p).numNodes := by
  by_cases h : p = 0
  · simp [h, equivTree, equivTreeToFun]
  · rw [equivTree, Equiv.coe_fn_mk, equivTreeToFun]
    simp_rw [h, dite_false, numNodes]
    have := semilength_insidePart_lt h
    have := semilength_outsidePart_lt h
    rw [← semilength_insidePart_add_semilength_outsidePart_add_one h,
      semilength_eq_numNodes_equivTree p.insidePart,
      semilength_eq_numNodes_equivTree p.outsidePart]; rfl
termination_by p.semilength

/-- Equivalence between Dyck words of semilength `n` and rooted binary trees with
`n` internal nodes. -/
def equivTreesOfNumNodesEq (n : ℕ) :
    { p : DyckWord // p.semilength = n } ≃ treesOfNumNodesEq n where
  toFun := fun ⟨p, _⟩ ↦ ⟨equivTree p, by
    rwa [mem_treesOfNumNodesEq, ← semilength_eq_numNodes_equivTree]⟩
  invFun := fun ⟨tr, _⟩ ↦ ⟨equivTree.symm tr, by
    rwa [semilength_eq_numNodes_equivTree, ← mem_treesOfNumNodesEq, Equiv.apply_symm_apply]⟩
  left_inv _ := by simp only [Equiv.symm_apply_apply]
  right_inv _ := by simp only [Equiv.apply_symm_apply]

instance {n : ℕ} : Fintype { p : DyckWord // p.semilength = n } :=
  Fintype.ofEquiv _ (equivTreesOfNumNodesEq n).symm

/-- There are `catalan n` Dyck words of semilength `n` (or length `2 * n`). -/
theorem card_dyckWord_semilength_eq_catalan (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n := by
  rw [← Fintype.ofEquiv_card (equivTreesOfNumNodesEq n), ← treesOfNumNodesEq_card_eq_catalan]
  convert Fintype.card_coe _

end Tree

end DyckWord

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `p.firstReturn` is positive if `p` is nonzero. -/
@[positivity DyckWord.firstReturn _]
def evalDyckWordFirstReturn : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(DyckWord.firstReturn $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(DyckWord.firstReturn_pos ($pa).ne'))
    | .nonzero pa => pure (.positive q(DyckWord.firstReturn_pos $pa))
    | _ => pure .none
  | _, _, _ => throwError "not DyckWord.firstReturn"

end Mathlib.Meta.Positivity
