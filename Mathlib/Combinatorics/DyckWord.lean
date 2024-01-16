/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.Catalan
import Mathlib.Data.List.Indexes

/-!
# Dyck words

## Main definitions

* `DyckPath`: a list of `Step`s, each of which may only be `U`p or `D`own.
* `IsBalanced`: the property defining Dyck words. Translating `U` and `D` to `(` and `)`,
  the resulting brackets are balanced.

## Main results

* `treeEquiv`: equivalence between Dyck words and rooted binary trees.
* `finiteTreeEquiv`: equivalence between Dyck words of length `2 * n` and rooted binary trees
  with `n` internal nodes.
* `treesOfNodesEq_card_eq_catalan`: there are `catalan n` Dyck words of length `2 * n`.
-/


namespace DyckPath

/-- A `Step` is either `U` or `D`, corresponding to `(` and `)` respectively. -/
inductive Step
  | U : Step
  | D : Step
  deriving Inhabited, DecidableEq

/-- A `DyckPath` is a `List` of `Step`s. -/
abbrev _root_.DyckPath := List Step

open Step List

lemma step_cases (s : Step) : s = U ∨ s = D := by cases' s <;> tauto

variable {p : DyckPath}

lemma count_U_add_count_D_eq_length : p.count U + p.count D = p.length := by
  symm; convert p.length_eq_countP_add_countP (· == U)
  rw [count]; congr!; rename_i s
  cases' s <;> simp

/-- A `DyckPath` is balanced if its running `U`-count always exceeds its running `D`-count
and both counts are equal at the end. -/
def IsBalanced (p : DyckPath) : Prop :=
  p.count U = p.count D ∧ ∀ i, (p.take i).count D ≤ (p.take i).count U

/-- Computable version of `IsBalanced`. -/
def IsBalanced' (p : DyckPath) : Prop :=
  p.count U = p.count D ∧ ∀ i < p.length, (p.take i).count D ≤ (p.take i).count U

theorem isBalanced_iff_isBalanced' : p.IsBalanced ↔ p.IsBalanced' := by
  constructor <;> (intro ⟨h1, h2⟩; refine' ⟨h1, _⟩)
  · intro i _; exact h2 i
  · intro i
    cases' lt_or_ge i p.length with hi hi
    · exact h2 i hi
    · rw [take_all_of_le hi]; exact h1.symm.le

instance : DecidablePred IsBalanced := fun _ ↦
  decidable_of_iff (_ ∧ _) isBalanced_iff_isBalanced'.symm

section Decomp

variable (p) (bal : p.IsBalanced) (hl : p ≠ [])

lemma head_U : p.head hl = U := by
  cases' p with ph pt; · contradiction
  by_contra f
  replace f := (step_cases ph).resolve_left f
  have := bal.2 1
  rw [take_cons, take_zero, f, count_singleton', count_singleton'] at this
  simp only [ite_true, ite_false] at this
  contradiction

lemma length_even : ∃ k, p.length = 2 * k := by
  use p.count U
  rw [← count_U_add_count_D_eq_length, bal.1, two_mul]

/-- Index of the first return of a `DyckPath` to zero. -/
def firstReturn : ℕ :=
  (range p.length).findIdx (fun i ↦ (p.take (i + 1)).count U = (p.take (i + 1)).count D)
/-- The left part of the Dyck word decomposition. -/
def leftPart : DyckPath := (p.take p.firstReturn).tail
/-- The right part of the Dyck word decomposition. -/
def rightPart : DyckPath := p.drop (p.firstReturn + 1)

lemma firstReturn_lt_length : p.firstReturn < p.length := by
  rw [← length_range p.length]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.length - 1
  have := length_pos_of_ne_nil hl
  refine' ⟨by omega, _⟩
  rw [show p.length - 1 + 1 = p.length by omega, take_all_of_le (le_refl _)]
  exact bal.1

lemma count_U_eq_count_D_of_firstReturn :
    (p.take (p.firstReturn + 1)).count U = (p.take (p.firstReturn + 1)).count D := by
  have := findIdx_get (w := (length_range p.length).symm ▸ p.firstReturn_lt_length bal hl)
  simpa only [get_range, decide_eq_true_eq]

lemma count_D_lt_count_U_of_lt_firstReturn : ∀ i < p.firstReturn,
    (p.take (i + 1)).count D < (p.take (i + 1)).count U := fun i hi ↦ by
  have ne := not_of_lt_findIdx hi
  simp only [get_range, decide_eq_true_eq, ← ne_eq] at ne
  have lt := bal.2 (i + 1)
  exact lt_of_le_of_ne lt ne.symm

/-- The `p.firstReturn`-th element of a balanced `DyckPath` is `D`. -/
lemma get_firstReturn_eq_D : p.get ⟨p.firstReturn, p.firstReturn_lt_length bal hl⟩ = D := by
  have eq := p.count_U_eq_count_D_of_firstReturn bal hl
  have le := bal.2 p.firstReturn
  have frl := p.firstReturn_lt_length bal hl
  simp_rw [take_succ, get?_eq_get frl, Option.to_list_some, count_append, count_singleton'] at eq
  by_contra f
  replace f := (step_cases (p.get ⟨_, frl⟩)).resolve_right f
  simp_rw [f, ite_true, ite_false] at eq
  omega

lemma firstReturn_pos : 0 < p.firstReturn := by
  by_contra f
  rw [not_lt, nonpos_iff_eq_zero] at f
  have eqD := p.get_firstReturn_eq_D bal hl
  have eqU := p.head_U bal hl
  cases' p with hd tl; · tauto
  simp_rw [f, List.get] at eqD
  rw [head_cons, eqD] at eqU
  contradiction

lemma take_eq_U_cons_tail {i : ℕ} (hi : 0 < i) : p.take i = U :: (p.take i).tail := by
  have tip := (@take_eq_nil_iff _ p i).not.symm
  simp_rw [not_or, ← ne_eq] at tip
  replace tip := tip.mp ⟨hl, hi.ne'⟩
  convert (cons_head!_tail tip).symm
  have := head!_append (p.drop i) tip
  rw [take_append_drop] at this
  rw [← this, ← p.head_U bal hl]
  cases' p with hd tl; · tauto
  rw [head_cons, head!_cons]

lemma take_tail_comm {i : ℕ} : (p.take (i + 1)).tail = p.tail.take i := by
  cases' p; · contradiction
  rw [take_cons_succ, tail_cons, tail_cons]

lemma take_tail_take_of_lt {i j : ℕ} (hij : i < j) : (p.take j).tail.take i = p.tail.take i := by
  cases' p with hd tl; · simp only [take_nil, tail_nil]
  induction' j, hij using Nat.le_induction with j hij _
  · rw [take_cons, tail_cons, take_take, min_self, tail_cons]
  · rw [take_cons, tail_cons, take_take, tail_cons, min_eq_left (by omega)]

theorem leftPart_isBalanced : p.leftPart.IsBalanced := by
  have eq := p.count_U_eq_count_D_of_firstReturn bal hl
  have frl := p.firstReturn_lt_length bal hl
  rw [take_succ, get?_eq_get frl, Option.to_list_some, count_append, count_append,
    p.get_firstReturn_eq_D bal hl, p.take_eq_U_cons_tail bal hl (p.firstReturn_pos bal hl)] at eq
  simp only [count_cons, count_nil, ite_true, ite_false, zero_add, add_zero, add_left_inj] at eq
  refine' ⟨eq, fun i ↦ _⟩
  have lt := p.count_D_lt_count_U_of_lt_firstReturn bal
  unfold leftPart
  cases' lt_or_ge i p.firstReturn with e e
  · replace lt := lt i e
    rw [p.take_eq_U_cons_tail bal hl (by omega)] at lt
    simp only [count_cons, ite_true, ite_false, add_zero, Nat.lt_add_one_iff,
      p.take_tail_comm bal hl] at lt
    rw [p.take_tail_take_of_lt bal hl e]
    exact lt
  · rw [take_all_of_le, eq]
    rw [length_tail, length_take, min_eq_left (p.firstReturn_lt_length bal hl).le]
    omega

theorem eq_U_leftPart_D_rightPart : p = ↑[U] ++ p.leftPart ++ ↑[D] ++ p.rightPart := by
  nth_rw 1 [← p.take_append_drop (p.firstReturn + 1)]; congr
  rw [take_succ, get?_eq_get (p.firstReturn_lt_length bal hl), Option.to_list_some,
    p.get_firstReturn_eq_D bal hl]; congr
  rw [p.take_eq_U_cons_tail bal hl (p.firstReturn_pos bal hl), singleton_append]; rfl

theorem leftPart_length_lt : p.leftPart.length < p.length := by
  conv_rhs => rw [p.eq_U_leftPart_D_rightPart bal hl]
  rw [length_append, length_append, length_append, length_singleton, length_singleton]
  omega

theorem rightPart_length_lt : p.rightPart.length < p.length := by
  conv_rhs => rw [p.eq_U_leftPart_D_rightPart bal hl]
  rw [length_append, length_append, length_append, length_singleton, length_singleton]
  omega

theorem rightPart_isBalanced : p.rightPart.IsBalanced := by
  have h1 := bal.1
  have h2 := bal.2
  have ceq : (↑[U] ++ p.leftPart ++ ↑[D]).count U = (↑[U] ++ p.leftPart ++ ↑[D]).count D := by
    iterate 4 rw [count_append]
    simp only [(p.leftPart_isBalanced bal hl).1, count_singleton', ite_true, ite_false]
    omega
  rw [p.eq_U_leftPart_D_rightPart bal hl, count_append _ _ p.rightPart,
    count_append _ _ p.rightPart, ceq, add_right_inj] at h1
  refine' ⟨h1, fun i ↦ _⟩
  rw [p.eq_U_leftPart_D_rightPart bal hl] at h2
  conv at h2 => intro i; rw [take_append_eq_append_take]
  replace h2 := h2 (i + (↑[U] ++ p.leftPart ++ ↑[D]).length)
  rw [take_all_of_le (Nat.le_add_left _ _), Nat.add_sub_cancel,
    count_append _ _ (p.rightPart.take i), count_append _ _ (p.rightPart.take i), ceq] at h2
  exact Nat.add_le_add_iff_left.mp h2

variable {p} {q : DyckPath}

theorem compose_firstReturn : (↑[U] ++ p ++ ↑[D] ++ q).firstReturn = p.length + 1 := by
  rw [firstReturn]
  apply eq_findIdx_of_not
  pick_goal 3
  · rw [length_range, length_append, length_append, length_append, length_singleton,
      length_singleton]; omega
  · intro j hji
    simp only [get_range, decide_eq_true_eq]
    rw [append_assoc, take_append_eq_append_take]
    have l1 : j + 1 - (↑[U] ++ p).length = 0 := by rw [length_append, length_singleton]; omega
    rw [l1, take_zero, append_nil, singleton_append, take_cons, count_cons, count_cons]
    simp only [ite_true, ite_false, add_zero]
    have := bal.2 j; omega
  · simp only [get_range, decide_eq_true_eq]
    rw [take_append_eq_append_take, length_append, length_append, length_singleton,
      length_singleton, show p.length + 1 + 1 - (1 + p.length + 1) = 0 by omega, take_zero,
      append_nil, take_all_of_le]
    iterate 4 rw [count_append]
    simp_rw [count_singleton', ite_true, ite_false, bal.1]; omega
    rw [length_append, length_append, length_singleton, length_singleton]; omega

theorem compose_leftPart_eq_leftPart : (↑[U] ++ p ++ ↑[D] ++ q).leftPart = p := by
  rw [leftPart, compose_firstReturn bal, append_assoc, take_append_eq_append_take,
    length_append, length_singleton, show p.length + 1 - (1 + p.length) = 0 by omega, take_zero,
    append_nil, take_append_eq_append_take, length_singleton, Nat.add_sub_cancel,
    take_all_of_le (by rw [length_singleton]; omega), take_all_of_le (le_refl _), singleton_append,
    tail_cons]

theorem compose_rightPart_eq_rightPart : (↑[U] ++ p ++ ↑[D] ++ q).rightPart = q := by
  rw [rightPart, compose_firstReturn bal, drop_append_eq_append_drop, length_append, length_append,
    length_singleton, length_singleton, show p.length + 1 + 1 - (1 + p.length + 1) = 0 by omega,
    drop_zero, drop_eq_nil_of_le, nil_append]
  rw [length_append, length_append, length_singleton, length_singleton]
  omega

end Decomp

section Tree

open Tree

/-- Convert a balanced Dyck path to a binary rooted tree. -/
def treeEquivToFun (st : { p : DyckPath // p.IsBalanced }) : Tree Unit :=
  if e : st.1.length = 0 then nil else by
    obtain ⟨p, bal⟩ := st
    simp only [length_eq_zero] at e
    have := p.leftPart_length_lt bal e
    have := p.rightPart_length_lt bal e
    exact treeEquivToFun ⟨_, p.leftPart_isBalanced bal e⟩ △
      treeEquivToFun ⟨_, p.rightPart_isBalanced bal e⟩
termination_by _ => st.1.length

/-- Convert a binary rooted tree to a Dyck path (that it is balanced is shown in
`isBalanced_treeEquivInvFun'`). -/
def treeEquivInvFun' (tr : Tree Unit) : DyckPath :=
  match tr with
  | Tree.nil => []
  | Tree.node _ l r => ↑[U] ++ treeEquivInvFun' l ++ ↑[D] ++ treeEquivInvFun' r

theorem isBalanced_treeEquivInvFun' (tr : Tree Unit) : (treeEquivInvFun' tr).IsBalanced := by
  induction' tr with _ l r bl br
  · rw [treeEquivInvFun']; decide
  · rw [treeEquivInvFun']; constructor
    · iterate 6 rw [count_append]
      simp_rw [bl.1, br.1, count_singleton']; omega
    · intro i
      iterate 3 rw [take_append_eq_append_take]
      iterate 6 rw [count_append]
      apply add_le_add _ (br.2 _)
      conv_lhs => rw [← add_rotate]
      conv_rhs => rw [← add_rotate]
      apply add_le_add _ (bl.2 _)
      cases' (i - (↑[U] ++ treeEquivInvFun' l).length).eq_zero_or_pos with k k
      · simp_rw [k, take_zero, count_nil, zero_add]
        cases' i.eq_zero_or_pos with l l
        · rw [l, take_zero, count_nil, count_nil]
        · rw [take_all_of_le (by rw [length_singleton]; exact l),
            count_singleton', count_singleton']
          simp only [ite_true, ite_false, zero_le]
      · rw [take_all_of_le (by rw [length_singleton]; exact k),
          take_all_of_le (by rw [length_singleton]; omega)]
        simp only [count_singleton', ite_true, ite_false]
        omega

/-- Convert a binary rooted tree to a balanced Dyck path. -/
def treeEquivInvFun (tr : Tree Unit) : { p : DyckPath // p.IsBalanced } :=
  ⟨treeEquivInvFun' tr, isBalanced_treeEquivInvFun' tr⟩

@[nolint unusedHavesSuffices]
theorem treeEquiv_left_inv (st) {n : ℕ} (hl : st.1.length = n) :
    treeEquivInvFun (treeEquivToFun st) = st := by
  induction' n using Nat.strongInductionOn with n ih generalizing st
  cases' eq_or_ne st.1 [] with j j
  · rw [treeEquivToFun, Subtype.mk.injEq]
    simp_rw [length_eq_zero.mpr j, dite_true, treeEquivInvFun, treeEquivInvFun', j]
  rw [treeEquivToFun, Subtype.mk.injEq]
  simp_rw [(length_pos.mpr j).ne', dite_false, treeEquivInvFun, treeEquivInvFun']
  let p := st.1
  let bal := st.2
  change _ = p; rw [p.eq_U_leftPart_D_rightPart bal j]
  have tl := ih _ (hl ▸ p.leftPart_length_lt bal j) ⟨_, p.leftPart_isBalanced bal j⟩ rfl
  have tr := ih _ (hl ▸ p.rightPart_length_lt bal j) ⟨_, p.rightPart_isBalanced bal j⟩ rfl
  rw [treeEquivInvFun, Subtype.mk.injEq] at tl tr
  congr

@[nolint unusedHavesSuffices]
theorem treeEquiv_right_inv (tr) : treeEquivToFun (treeEquivInvFun tr) = tr := by
  induction' tr with _ l r ttl ttr
  · simp_rw [treeEquivInvFun, treeEquivInvFun']
    rw [treeEquivToFun]; simp
  simp_rw [treeEquivInvFun, treeEquivInvFun']
  rw [treeEquivToFun]
  have ln : (↑[U] ++ treeEquivInvFun' l ++ ↑[D] ++ treeEquivInvFun' r).length ≠ 0 := by
    rw [length_append, length_append, length_append, length_singleton, length_singleton]; omega
  simp_rw [ln, dite_false, node.injEq, true_and]
  rw [treeEquivInvFun] at ttl ttr
  simp_rw [compose_leftPart_eq_leftPart (isBalanced_treeEquivInvFun' _),
    compose_rightPart_eq_rightPart (isBalanced_treeEquivInvFun' _)]
  exact ⟨ttl, ttr⟩

/-- Equivalence between Dyck words and rooted binary trees. -/
def treeEquiv : { p : DyckPath // p.IsBalanced } ≃ Tree Unit where
  toFun := treeEquivToFun
  invFun := treeEquivInvFun
  left_inv st := treeEquiv_left_inv st rfl
  right_inv := treeEquiv_right_inv

@[nolint unusedHavesSuffices]
theorem length_eq_two_mul_iff_numNodes_eq {n : ℕ} (st : { p : DyckPath // p.IsBalanced }) :
    st.1.length = 2 * n ↔ (treeEquiv st).numNodes = n := by
  induction' n using Nat.strongInductionOn with n ih generalizing st
  cases' eq_or_ne st.1 [] with j j
  · rw [j, length_nil, zero_eq_mul]; norm_num
    rw [treeEquiv, Equiv.coe_fn_mk, treeEquivToFun]
    have := congrArg List.length j
    rw [length_nil] at this
    simp only [this, dite_true, numNodes]; omega
  rw [treeEquiv, Equiv.coe_fn_mk, treeEquivToFun]
  simp_rw [(length_pos.mpr j).ne', dite_false, numNodes]
  obtain ⟨p, bal⟩ := st
  dsimp only at j ⊢
  have bl := p.leftPart_isBalanced bal j
  have br := p.rightPart_isBalanced bal j
  obtain ⟨sl, le⟩ := p.leftPart.length_even bl
  obtain ⟨sr, re⟩ := p.rightPart.length_even br
  conv_lhs =>
    rw [p.eq_U_leftPart_D_rightPart bal j, length_append, length_append, length_append,
      length_singleton, length_singleton, le, re,
      show 1 + 2 * sl + 1 + 2 * sr = 2 * (sl + sr + 1) by omega]
  constructor <;> intro h
  · have tl := (ih sl (by omega) ⟨_, bl⟩).mp le
    have tr := (ih sr (by omega) ⟨_, br⟩).mp re
    dsimp only [treeEquiv, Equiv.coe_fn_mk] at tl tr
    rw [tl, tr]
    rw [mul_eq_mul_left_iff] at h
    simp only [show ¬2 = 0 by omega, or_false] at h
    exact h
  · set wl := Subtype.mk _ bl
    set wr := Subtype.mk _ br
    have ntwl_lt : (treeEquivToFun wl).numNodes < n := by omega
    have ntwr_lt : (treeEquivToFun wr).numNodes < n := by omega
    have el := ih _ ntwl_lt ⟨_, bl⟩
    have er := ih _ ntwr_lt ⟨_, br⟩
    simp only [treeEquiv, Equiv.coe_fn_mk, iff_true] at el er
    rw [le, Nat.mul_left_cancel_iff zero_lt_two] at el
    rw [re, Nat.mul_left_cancel_iff zero_lt_two] at er
    rw [← el, ← er] at h
    rw [mul_eq_mul_left_iff]
    simpa only [show ¬2 = 0 by omega, or_false]

/-- Equivalence between Dyck words of length `2 * n` and
rooted binary trees with `n` internal nodes. -/
def finiteTreeEquiv (n : ℕ) :
    { p : DyckPath // p.IsBalanced ∧ p.length = 2 * n } ≃ treesOfNumNodesEq n where
  toFun := fun ⟨p, ⟨bal, len⟩⟩ ↦
    ⟨treeEquiv ⟨p, bal⟩, by rw [mem_treesOfNumNodesEq, ← length_eq_two_mul_iff_numNodes_eq, len]⟩
  invFun := fun ⟨tr, sz⟩ ↦
    ⟨(treeEquiv.symm tr).1, ⟨(treeEquiv.symm tr).2, by rwa [length_eq_two_mul_iff_numNodes_eq,
      ← mem_treesOfNumNodesEq, Equiv.apply_symm_apply]⟩⟩
  left_inv := fun ⟨p, ⟨bal, len⟩⟩ ↦ by simp only [Equiv.symm_apply_apply]
  right_inv := fun ⟨tr, sz⟩ ↦ by simp only [Subtype.coe_eta, Equiv.apply_symm_apply]

instance instFintypeDyckWords {n : ℕ} :
    Fintype { p : DyckPath // p.IsBalanced ∧ p.length = 2 * n } :=
  Fintype.ofEquiv _ (finiteTreeEquiv n).symm

/-- There are `catalan n` Dyck words of length `2 * n`. -/
theorem dyckPath_isBalanced_card_eq_catalan (n : ℕ) :
    Fintype.card { p : DyckPath // p.IsBalanced ∧ p.length = 2 * n } = catalan n := by
  rw [← Fintype.ofEquiv_card (finiteTreeEquiv n), ← treesOfNumNodesEq_card_eq_catalan]
  convert Fintype.card_coe _

end Tree

end DyckPath
