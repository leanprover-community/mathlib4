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
one consequence being that the number of Dyck words with length `2 * n` is `catalan n`.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s.
* `DyckWord.semilength`: semilength (half the length) of a Dyck word.
* `DyckWord.firstReturn`: for a nonempty word, the index of the `D` matching the initial `U`.

## Main results

* `DyckWord.treeEquiv`: equivalence between Dyck words and rooted binary trees.
  See the docstrings of `DyckWord.treeEquivToFun` and `DyckWord.treeEquivInvFun` for details.
* `DyckWord.finiteTreeEquiv`: equivalence between Dyck words of length `2 * n` and
  rooted binary trees with `n` internal nodes.
* `DyckWord.card_dyckWord_of_semilength_eq_catalan`:
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

section FirstReturn

/-- `p.firstReturn` is 0 if `p = 0` and the index of the `D` matching the initial `U` otherwise. -/
def firstReturn : ℕ :=
  (range p.l.length).findIdx (fun i ↦ (p.l.take (i + 1)).count U = (p.l.take (i + 1)).count D)

@[simp] lemma firstReturn_zero : firstReturn 0 = 0 := rfl

lemma firstReturn_pos (h : p.l ≠ []) : 0 < p.firstReturn := by
  by_contra f
  replace f : p.firstReturn = 0 := by omega
  rw [firstReturn, findIdx_eq (by simp [h])] at f
  simp only [get_range, zero_add, decide_eq_true_eq, not_lt_zero', false_implies, implies_true,
    and_true] at f
  rw [← p.cons_tail_dropLast_concat h] at f
  simp at f

lemma firstReturn_lt_length (h : p.l ≠ []) : p.firstReturn < p.l.length := by
  have lp := length_pos_of_ne_nil h
  rw [← length_range p.l.length]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.l.length - 1
  exact ⟨by omega, by rw [Nat.sub_add_cancel lp, take_all_of_le (le_refl _), p.bal]⟩

lemma count_eq_count_of_take_firstReturn_add_one (h : p.l ≠ []) :
    (p.l.take (p.firstReturn + 1)).count U = (p.l.take (p.firstReturn + 1)).count D := by
  have := findIdx_get (w := (length_range p.l.length).symm ▸ p.firstReturn_lt_length h)
  simpa [get_range, decide_eq_true_eq] using this

lemma count_lt_count_of_lt_firstReturn (i : ℕ) (hi : i < p.firstReturn) :
    (p.l.take (i + 1)).count D < (p.l.take (i + 1)).count U := by
  have ne := not_of_lt_findIdx hi
  rw [get_range, decide_eq_true_eq, ← ne_eq] at ne
  exact lt_of_le_of_ne (p.nonneg (i + 1)) ne.symm

@[simp, nolint unusedHavesSuffices]
lemma firstReturn_add : (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn := by
  split_ifs with h; · simp [h]
  rw [eq_zero_iff, ← ne_eq] at h
  have u : (p + q).l = p.l ++ q.l := rfl
  have v := p.firstReturn_lt_length h
  rw [firstReturn, findIdx_eq]
  swap
  · rw [length_range, u, length_append]
    exact Nat.lt_add_right _ (p.firstReturn_lt_length h)
  · simp_rw [get_range, u, decide_eq_true_eq]
    constructor
    · rw [take_append_eq_append_take (l₂ := q.l), show p.firstReturn + 1 - p.l.length = 0 by omega,
        take_zero, append_nil, p.count_eq_count_of_take_firstReturn_add_one h]
    · intro j hj
      rw [take_append_eq_append_take, show j + 1 - p.l.length = 0 by omega, take_zero, append_nil]
      have := p.count_lt_count_of_lt_firstReturn j hj
      have := p.nonneg j
      omega

@[simp]
lemma firstReturn_nest : p.nest.firstReturn = p.l.length + 1 := by
  have u : p.nest.l = U :: p.l ++ [D] := rfl
  rw [firstReturn, findIdx_eq]
  swap
  · simp_rw [length_range, u, length_append, length_cons]
    apply Nat.lt.base
  · simp_rw [get_range, u, decide_eq_true_eq]
    constructor
    · rw [take_all_of_le (by simp), ← u, p.nest.bal]
    · intro j hj
      simp_rw [cons_append, take_cons, count_cons, ite_true, ite_false, take_append_eq_append_take,
        show j - p.l.length = 0 by omega, take_zero, append_nil]
      have := p.nonneg j
      omega

/-- The right part of the Dyck word decomposition. -/
def rightPart (h : p.l ≠ []) : DyckWord :=
  p.drop (p.firstReturn + 1) (p.count_eq_count_of_take_firstReturn_add_one h)

/-- The left part of the Dyck word decomposition. -/
def leftPart (h : p.l ≠ []) : DyckWord :=
  (p.take (p.firstReturn + 1) (p.count_eq_count_of_take_firstReturn_add_one h)).denest
    (by simp [take, h]) (fun i lb ub ↦ by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take, min_eq_left ub.le]
      rw [show i = i - 1 + 1 by omega] at ub ⊢
      rw [Nat.add_lt_add_iff_right] at ub
      exact p.count_lt_count_of_lt_firstReturn _ ub)

@[simp]
theorem leftPart_nest_add_rightPart (h : p.l ≠ []) : (p.leftPart h).nest + p.rightPart h = p := by
  rw [DyckWord.ext_iff, leftPart, denest_nest]
  apply take_append_drop

lemma leftPart_length_lt (h : p.l ≠ []) : (p.leftPart h).l.length < p.l.length := by
  nth_rw 2 [← p.leftPart_nest_add_rightPart h]
  change _ < (U :: (p.leftPart h).l ++ [D] ++ (p.rightPart h).l).length
  simp_rw [length_append, length_singleton, length_cons]; omega

theorem leftPart_semilength_lt (h : p.l ≠ []) : (p.leftPart h).semilength < p.semilength := by
  rw [← Nat.mul_lt_mul_left zero_lt_two]
  simp_rw [two_mul_semilength_eq_length]
  exact p.leftPart_length_lt h

lemma rightPart_length_lt (h : p.l ≠ []) : (p.rightPart h).l.length < p.l.length := by
  nth_rw 2 [← p.leftPart_nest_add_rightPart h]
  change _ < (U :: (p.leftPart h).l ++ [D] ++ (p.rightPart h).l).length
  simp_rw [length_append, length_singleton, length_cons]; omega

theorem rightPart_semilength_lt (h : p.l ≠ []) : (p.rightPart h).semilength < p.semilength := by
  rw [← Nat.mul_lt_mul_left zero_lt_two]
  simp_rw [two_mul_semilength_eq_length]
  exact p.rightPart_length_lt h

lemma nest_add_ne_empty : (p.nest + q).l ≠ [] := by change U :: _ ++ _ ≠ []; simp

lemma nest_add_firstReturn : (p.nest + q).firstReturn = p.l.length + 1 := by
  rw [firstReturn_add, firstReturn_nest, ite_eq_right_iff, eq_zero_iff]; intro; contradiction

theorem nest_add_leftPart_eq : (p.nest + q).leftPart (nest_add_ne_empty _ _) = p := by
  have : p.l.length + 1 + 1 = p.nest.l.length := by simp [nest]
  simp_rw [leftPart, nest_add_firstReturn, take, DyckWord.ext_iff,
    show (p.nest + q).l = p.nest.l ++ q.l by rfl, take_append_eq_append_take,
    this, take_length, tsub_self, take_zero, append_nil, denest, nest, dropLast_concat]
  rfl

theorem nest_add_rightPart_eq : (p.nest + q).rightPart (nest_add_ne_empty _ _) = q := by
  have : p.l.length + 1 + 1 = p.nest.l.length := by simp [nest]
  simp_rw [rightPart, nest_add_firstReturn, drop, DyckWord.ext_iff,
    show (p.nest + q).l = p.nest.l ++ q.l by rfl, drop_append_eq_append_drop,
    this, drop_length, nil_append, tsub_self, drop_zero]

end FirstReturn

section Tree

open Tree

/-- Convert a Dyck word to a binary rooted tree.

`f(empty word) = empty tree`. For a nonempty word find the `D` that matches the initial `U` –
which has index `w.firstReturn` – then let `x` be everything strictly between said `U` and `D`,
and `y` be everything strictly after said `D`. `w = U x D y` and `x` and `y` are (possibly empty)
Dyck words. `f(w) = f(x) △ f(y)`, where △ (defined in `Mathlib.Data.Tree`) joins two subtrees
to a new root node. -/
def treeEquivToFun (w : DyckWord) : Tree Unit :=
  if e : w = 0 then nil else by
    rw [eq_zero_iff, ← ne_eq] at e
    have := w.leftPart_semilength_lt e
    have := w.rightPart_semilength_lt e
    exact treeEquivToFun (w.leftPart e) △ treeEquivToFun (w.rightPart e)
termination_by w.semilength

/-- Convert a binary rooted tree to a Dyck word.

`g(empty tree) = empty word`. A nonempty tree with left subtree `x` and right subtree `y`
is sent to `U g(x) D g(y)`. -/
def treeEquivInvFun (tr : Tree Unit) : DyckWord :=
  match tr with
  | Tree.nil => 0
  | Tree.node _ l r => (treeEquivInvFun l).nest + treeEquivInvFun r

@[nolint unusedHavesSuffices]
theorem treeEquiv_left_inv {n : ℕ} (hs : p.semilength = n) :
    treeEquivInvFun (treeEquivToFun p) = p := by
  induction' n using Nat.strongInductionOn with n ih generalizing p
  by_cases h : p = 0
  · simp [h, treeEquivToFun, treeEquivInvFun]
  · rw [treeEquivToFun]
    simp_rw [h, dite_false, treeEquivInvFun]
    rw [eq_zero_iff, ← ne_eq] at h
    convert p.leftPart_nest_add_rightPart h
    · exact ih _ (hs ▸ p.leftPart_semilength_lt h) _ rfl
    · exact ih _ (hs ▸ p.rightPart_semilength_lt h) _ rfl

@[nolint unusedHavesSuffices]
theorem treeEquiv_right_inv (tr : Tree Unit) : treeEquivToFun (treeEquivInvFun tr) = tr := by
  induction' tr with _ l r ttl ttr
  · simp [treeEquivInvFun, treeEquivToFun]
  rw [treeEquivInvFun, treeEquivToFun]
  have pp : (treeEquivInvFun l).nest + treeEquivInvFun r ≠ 0 := by
    rw [ne_eq, eq_zero_iff, ← ne_eq]
    apply nest_add_ne_empty
  simp_rw [pp, dite_false, node.injEq, true_and]
  constructor
  · convert ttl; apply nest_add_leftPart_eq
  · convert ttr; apply nest_add_rightPart_eq

/-- Equivalence between Dyck words and rooted binary trees. -/
def treeEquiv : DyckWord ≃ Tree Unit where
  toFun := treeEquivToFun
  invFun := treeEquivInvFun
  left_inv w := treeEquiv_left_inv w rfl
  right_inv := treeEquiv_right_inv

@[nolint unusedHavesSuffices]
theorem semilength_eq_iff_numNodes_eq {n : ℕ} : p.semilength = n ↔ (treeEquiv p).numNodes = n := by
  induction' n using Nat.strongInductionOn with n ih generalizing p
  by_cases hn : p = 0; · simp [hn]
  rw [treeEquiv, Equiv.coe_fn_mk, treeEquivToFun]
  simp_rw [hn, dite_false, numNodes]
  rw [eq_zero_iff, ← ne_eq] at hn
  constructor <;> intro h
  · have tl := ih _ (h ▸ p.leftPart_semilength_lt hn) (p.leftPart hn)
    have tr := ih _ (h ▸ p.rightPart_semilength_lt hn) (p.rightPart hn)
    simp_rw [treeEquiv, true_iff, Equiv.coe_fn_mk] at tl tr
    rw [tl, tr, ← h]
    nth_rw 3 [← p.leftPart_nest_add_rightPart hn]
    rw [semilength_add, semilength_nest]
    omega
  · have ln : (p.leftPart hn).treeEquiv.numNodes < n := by
      dsimp only [treeEquiv, Equiv.coe_fn_mk]; omega
    have rn : (p.rightPart hn).treeEquiv.numNodes < n := by
      dsimp only [treeEquiv, Equiv.coe_fn_mk]; omega
    have el := ih _ ln (p.leftPart hn)
    have er := ih _ rn (p.rightPart hn)
    simp only [treeEquiv, Equiv.coe_fn_mk, iff_true] at el er
    rw [← h, ← el, ← er]
    nth_rw 1 [← p.leftPart_nest_add_rightPart hn]
    rw [semilength_add, semilength_nest]
    omega

/-- Equivalence between Dyck words of semilength `n` and rooted binary trees with
`n` internal nodes. -/
def finiteTreeEquiv (n : ℕ) : { p : DyckWord // p.semilength = n } ≃ treesOfNumNodesEq n where
  toFun := fun ⟨p, _⟩ ↦ ⟨treeEquiv p, by
    rwa [mem_treesOfNumNodesEq, ← semilength_eq_iff_numNodes_eq]⟩
  invFun := fun ⟨tr, _⟩ ↦ ⟨treeEquiv.symm tr, by
    rwa [semilength_eq_iff_numNodes_eq, ← mem_treesOfNumNodesEq, Equiv.apply_symm_apply]⟩
  left_inv _ := by simp only [Equiv.symm_apply_apply]
  right_inv _ := by simp only [Equiv.apply_symm_apply]

instance {n : ℕ} : Fintype { p : DyckWord // p.semilength = n } :=
  Fintype.ofEquiv _ (finiteTreeEquiv n).symm

/-- There are `catalan n` Dyck words of semilength `n` (or length `2 * n`). -/
theorem card_dyckWord_of_semilength_eq_catalan (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n := by
  rw [← Fintype.ofEquiv_card (finiteTreeEquiv n), ← treesOfNumNodesEq_card_eq_catalan]
  convert Fintype.card_coe _

end Tree

end DyckWord
