/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.List.Indexes
import Mathlib.Logic.Relation
import Mathlib.Tactic.Positivity.Core

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
* `DyckWord.firstReturn`: for a nonempty word, the index of the `D` matching the initial `U`.

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
    obtain ⟨ha, hb⟩ := append_eq_nil.mp (toList_eq_nil.mpr h)
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
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); omega

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
    simp only [take_append_eq_append_take, count_append]
    rw [← add_rotate (count D _), ← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · simp [hi]
    rw [take_of_length_le (show [U].length ≤ i by rwa [length_singleton]), count_singleton']
    simp only [ite_true, ite_false]
    rw [add_comm]
    exact add_le_add (zero_le _) ((count_le_length _ _).trans (by simp))

@[simp] lemma nest_ne_zero : p.nest ≠ 0 := by simp [← toList_ne_nil, nest]

variable (p) in
/-- Denest `p`, i.e. `(x)` becomes `x`, given that `p` is strictly positive in its interior
(this ensures that `x` is a Dyck word). -/
def denest (pos : ∀ i, 0 < i → i < p.toList.length →
    (p.toList.take i).count D < (p.toList.take i).count U) : DyckWord where
  toList := p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← cons_tail_dropLast_concat h, count_append, count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    have h' := toList_ne_nil.mpr h
    have l1 : p.toList.take 1 = [p.toList.head h'] := by rcases p with - | - <;> tauto
    have l3 : p.toList.length - 1 = p.toList.length - 1 - 1 + 1 := by
      rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
      · tauto
      · rename_i bal _
        cases s <;> simp at bal
      · tauto
    rw [← drop_one, take_drop, dropLast_eq_take, take_take]
    have ub : min (1 + i) (p.toList.length - 1) < p.toList.length :=
      (min_le_right _ p.toList.length.pred).trans_lt (Nat.pred_lt ((length_pos.mpr h').ne'))
    have lb : 0 < min (1 + i) (p.toList.length - 1) := by
      rw [l3, add_comm, min_add_add_right]; omega
    have eq := pos _ lb ub
    set j := min (1 + i) (p.toList.length - 1)
    rw [← (p.toList.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by omega), l1, head_eq_U] at eq
    simp only [count_singleton', ite_true, ite_false] at eq
    omega

lemma denest_nest (pos : ∀ i, 0 < i → i < p.toList.length →
    (p.toList.take i).count D < (p.toList.take i).count U) : (p.denest h pos).nest = p := by
  simpa [DyckWord.ext_iff] using p.cons_tail_dropLast_concat h

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
  by_contra! f
  rw [Nat.le_zero, firstReturn, findIdx_eq] at f
  · simp only [get_eq_getElem, getElem_range] at f
    rw [← p.cons_tail_dropLast_concat h] at f
    simp at f
  · rw [length_range, length_pos]
    exact toList_ne_nil.mpr h

include h in
lemma firstReturn_lt_length : p.firstReturn < p.toList.length := by
  have lp := length_pos_of_ne_nil (toList_ne_nil.mpr h)
  rw [← length_range p.toList.length]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.toList.length - 1
  exact ⟨by omega, by rw [Nat.sub_add_cancel lp, take_of_length_le (le_refl _),
    p.count_U_eq_count_D]⟩

include h in
lemma count_take_firstReturn_add_one :
    (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 1)).count D := by
  have := findIdx_get (w := (length_range p.toList.length).symm ▸ firstReturn_lt_length h)
  simpa using this

lemma count_D_lt_count_U_of_lt_firstReturn {i : ℕ} (hi : i < p.firstReturn) :
    (p.toList.take (i + 1)).count D < (p.toList.take (i + 1)).count U := by
  have ne := not_of_lt_findIdx hi
  rw [decide_eq_true_eq, ← ne_eq, get_eq_getElem, getElem_range] at ne
  exact lt_of_le_of_ne (p.count_D_le_count_U (i + 1)) ne.symm

@[simp]
lemma firstReturn_add : (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn := by
  split_ifs with h; · simp [h]
  have u : (p + q).toList = p.toList ++ q.toList := rfl
  rw [firstReturn, findIdx_eq]
  · simp_rw [get_eq_getElem, getElem_range, u, decide_eq_true_eq]
    have v := firstReturn_lt_length h
    constructor
    · rw [take_append_eq_append_take, show p.firstReturn + 1 - p.toList.length = 0 by omega,
        take_zero, append_nil, count_take_firstReturn_add_one h]
    · intro j hj
      rw [take_append_eq_append_take, show j + 1 - p.toList.length = 0 by omega,
        take_zero, append_nil]
      exact (count_D_lt_count_U_of_lt_firstReturn hj).ne'
  · rw [length_range, u, length_append]
    exact Nat.lt_add_right _ (firstReturn_lt_length h)

@[simp]
lemma firstReturn_nest : p.nest.firstReturn = p.toList.length + 1 := by
  have u : p.nest.toList = U :: p.toList ++ [D] := rfl
  rw [firstReturn, findIdx_eq]
  · simp_rw [get_eq_getElem, getElem_range, u, decide_eq_true_eq]
    constructor
    · rw [take_of_length_le (by simp), ← u, p.nest.count_U_eq_count_D]
    · intro j hj
      simp_rw [cons_append, take_cons, count_cons, beq_self_eq_true, ite_true,
        beq_iff_eq, ite_false, take_append_eq_append_take,
        show j - p.toList.length = 0 by omega, take_zero, append_nil]
      have := p.count_D_le_count_U j
      omega
  · simp_rw [length_range, u, length_append, length_cons]
    exact Nat.lt_add_one _

lemma firstReturn_nest_add : (p.nest + q).firstReturn = p.toList.length + 1 := by simp

variable (p) in
/-- The left part of the Dyck word decomposition,
inside the `U, D` pair that `firstReturn` refers to. `insidePart 0 = 0`. -/
def insidePart : DyckWord :=
  if h : p = 0 then 0 else
  (p.take (p.firstReturn + 1) (count_take_firstReturn_add_one h)).denest
    (by rw [← toList_ne_nil, take]; simpa using toList_ne_nil.mpr h)
    (fun i lb ub ↦ by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take, min_eq_left ub.le]
      rw [show i = i - 1 + 1 by omega] at ub ⊢
      rw [Nat.add_lt_add_iff_right] at ub
      exact count_D_lt_count_U_of_lt_firstReturn ub)

variable (p) in
/-- The right part of the Dyck word decomposition,
outside the `U, D` pair that `firstReturn` refers to. `outsidePart 0 = 0`. -/
def outsidePart : DyckWord :=
  if h : p = 0 then 0 else p.drop (p.firstReturn + 1) (count_take_firstReturn_add_one h)

@[simp] lemma insidePart_zero : insidePart 0 = 0 := by simp [insidePart]
@[simp] lemma outsidePart_zero : outsidePart 0 = 0 := by simp [outsidePart]

include h in
@[simp]
theorem nest_insidePart_add_outsidePart : p.insidePart.nest + p.outsidePart = p := by
  simp_rw [insidePart, outsidePart, h, dite_false, denest_nest, DyckWord.ext_iff]
  apply take_append_drop

include h in
lemma semilength_insidePart_add_semilength_outsidePart_add_one :
    p.insidePart.semilength + p.outsidePart.semilength + 1 = p.semilength := by
  rw [← congrArg semilength (nest_insidePart_add_outsidePart h), semilength_add, semilength_nest,
    add_right_comm]

include h in
theorem semilength_insidePart_lt : p.insidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  omega

include h in
theorem semilength_outsidePart_lt : p.outsidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  omega

theorem insidePart_nest_add : (p.nest + q).insidePart = p := by
  have : p.toList.length + 1 + 1 = p.nest.toList.length := by simp [nest]
  simp_rw [insidePart, firstReturn_nest_add, take,
    show (p.nest + q).toList = p.nest.toList ++ q.toList by rfl, take_append_eq_append_take,
    this, take_length, tsub_self, take_zero, append_nil, denest, nest, dropLast_concat]
  rfl

theorem outsidePart_nest_add : (p.nest + q).outsidePart = q := by
  have : p.toList.length + 1 + 1 = p.nest.toList.length := by simp [nest]
  simp_rw [outsidePart, add_eq_zero', nest_ne_zero, false_and, dite_false,
    firstReturn_nest_add, drop, show (p.nest + q).toList = p.nest.toList ++ q.toList by rfl,
    drop_append_eq_append_drop, this, drop_length, nil_append, tsub_self, drop_zero]

end FirstReturn

section Order

instance : Preorder DyckWord where
  le := Relation.ReflTransGen (fun p q ↦ p = q.insidePart ∨ p = q.outsidePart)
  le_refl p := Relation.ReflTransGen.refl
  le_trans p q r := Relation.ReflTransGen.trans

lemma zero_le (p : DyckWord) : 0 ≤ p := by
  by_cases h : p = 0
  · simp [h]
  · have := semilength_insidePart_lt h
    exact (zero_le _).trans (Relation.ReflTransGen.single (Or.inl rfl))
termination_by p.semilength

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
      rcases mq with hm | hm
      · have : r.insidePart <:+: r.toList := by
          use [U], [D] ++ r.outsidePart; rwa [← append_assoc]
        exact ih.trans (hm ▸ this)
      · have : r.outsidePart <:+: r.toList := by
          use [U] ++ r.insidePart ++ [D], []; rwa [append_nil]
        exact ih.trans (hm ▸ this)

/-- Partial order on Dyck words: `p ≤ q` if a (possibly empty) sequence of
`insidePart` and `outsidePart` operations can turn `q` into `p`. -/
instance : PartialOrder DyckWord where
  le_antisymm p q pq qp := by
    have h₁ := infix_of_le pq
    have h₂ := infix_of_le qp
    exact DyckWord.ext <| h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le

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
