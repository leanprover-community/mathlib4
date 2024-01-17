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

* `DyckPath`: a list of `U`p or `D`own `Step`s.
* `IsBalanced`: the property defining Dyck words. Translating `U` and `D` to `(` and `)`,
  the resulting brackets are balanced.

## Main results

* `treeEquiv`: equivalence between Dyck words and rooted binary trees.
* `finiteTreeEquiv`: equivalence between Dyck words of length `2 * n` and rooted binary trees
  with `n` internal nodes.
* `dyckPath_isBalanced_card_eq_catalan`: there are `catalan n` Dyck words of length `2 * n`.
-/


open List

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

/-- A Dyck path is balanced if its running `D`-count never exceeds its running `U`-count
and both counts are equal at the end. -/
def IsBalanced : Prop :=
  p.count U = p.count D ∧ ∀ i, (p.take i).count D ≤ (p.take i).count U

/-- Decidable version of `IsBalanced`. -/
def IsBalanced' : Prop :=
  p.count U = p.count D ∧ ∀ i < p.length, (p.take i).count D ≤ (p.take i).count U

lemma isBalanced_iff_isBalanced' : p.IsBalanced ↔ p.IsBalanced' := by
  constructor <;> (intro ⟨h1, h2⟩; refine' ⟨h1, _⟩)
  · intro i _; exact h2 i
  · intro i
    cases' lt_or_ge i p.length with hi hi
    · exact h2 i hi
    · rw [take_all_of_le hi]; exact h1.symm.le

instance : DecidablePred IsBalanced := fun _ ↦
  decidable_of_iff (_ ∧ _) (isBalanced_iff_isBalanced' _).symm

end Defs

section Lemmas

variable {p : DyckPath} (bp : p.IsBalanced)

lemma IsBalanced.length_even : Even p.length := by
  use p.count U
  rw [← count_U_add_count_D_eq_length, bp.1]

/-- If `x` and `y` are balanced Dyck paths then so is `xy`. -/
lemma IsBalanced.append {q : DyckPath} (bq : q.IsBalanced) : (p ++ q).IsBalanced := by
  simp only [IsBalanced, take_append_eq_append_take, count_append]
  exact ⟨by rw [bp.1, bq.1], fun _ ↦ add_le_add (bp.2 _) (bq.2 _)⟩

/-- If `x` is a balanced Dyck path then so is `(x)`. -/
lemma IsBalanced.nest : (↑[U] ++ p ++ ↑[D]).IsBalanced := by
  simp only [IsBalanced, take_append_eq_append_take, count_append]
  refine' ⟨by rw [bp.1]; omega, fun i ↦ _⟩
  rw [← add_rotate (count D _), ← add_rotate (count U _)]
  apply add_le_add _ (bp.2 _)
  cases' i.eq_zero_or_pos with hi hi; · simp [hi]
  simp_rw [take_all_of_le (show [U].length ≤ i by rwa [length_singleton]),
    count_singleton', ite_true, ite_false, add_comm _ 0]
  exact add_le_add (zero_le _) ((count_le_length _ _).trans (by simp))

/-- A balanced Dyck path is split into two parts. If one part is balanced, so is the other. -/
lemma IsBalanced.split (i : ℕ) : IsBalanced (p.take i) ↔ IsBalanced (p.drop i) := by
  rw [IsBalanced, ← p.take_append_drop i] at bp
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

/-- If `p.take i` satisfies the equality part of `IsBalanced`, it also satisfies the other part
and is balanced itself. -/
lemma IsBalanced.from_take {i : ℕ} (h : (p.take i).count U = (p.take i).count D) :
    IsBalanced (p.take i) := ⟨h, fun j ↦ by rw [take_take]; apply bp.2⟩

variable (np : p ≠ [])

/-- The first element of a nonempty balanced Dyck path is `U`. -/
lemma IsBalanced.head_U : p.head np = U := by
  cases' p with h _; · tauto
  by_contra f; simpa [(step_cases h).resolve_left f] using bp.2 1

/-- The last element of a nonempty balanced Dyck path is `D`. -/
lemma IsBalanced.getLast_D : p.getLast np = D := by
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

lemma append_tail_dropLast_append : p = [U] ++ tail (dropLast p) ++ [D] := by
  nth_rw 1 [← p.dropLast_append_getLast np, ← p.dropLast.take_append_drop 1]
  rw [bp.getLast_D, drop_one, (denest_aux bp np).2.1, bp.head_U]

/-- If the inequality part of `IsBalanced` is strict in the interior of a nonempty
balanced Dyck path, the interior is itself balanced. -/
lemma IsBalanced.denest
    (h : ∀ i (_ : 0 < i ∧ i < p.length), (p.take i).count D < (p.take i).count U) :
    IsBalanced p.dropLast.tail := by
  obtain ⟨l1, _, l3⟩ := denest_aux bp np
  constructor
  · replace bp := (append_tail_dropLast_append bp np) ▸ bp.1
    simp_rw [count_append, count_singleton', ite_true, ite_false] at bp; omega
  · intro i
    rw [← drop_one, ← drop_take, dropLast_eq_take, take_take]
    have ub : min (1 + i) p.length.pred < p.length :=
      (min_le_right _ p.length.pred).trans_lt (Nat.pred_lt ((length_pos.mpr np).ne'))
    have lb : 0 < min (1 + i) p.length.pred := by
      rw [l3, add_comm, min_add_add_right]; omega
    have eq := h _ ⟨lb, ub⟩
    set j := min (1 + i) p.length.pred
    rw [← (p.take j).take_append_drop 1, count_append, count_append, take_take,
      min_eq_left (by omega), l1, bp.head_U] at eq
    simp only [count_singleton', ite_true, ite_false] at eq; omega

end Lemmas

section FirstReturn

/-- Index of the first return of a Dyck path to zero. -/
def firstReturn (p : DyckPath) : ℕ :=
  (range p.length).findIdx (fun i ↦ (p.take (i + 1)).count U = (p.take (i + 1)).count D)

variable {p : DyckPath} (bp : p.IsBalanced) (np : p ≠ [])

lemma firstReturn_lt_length : p.firstReturn < p.length := by
  have lp := length_pos_of_ne_nil np
  rw [← length_range p.length]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.length - 1
  exact ⟨by omega, by rw [Nat.sub_add_cancel lp, take_all_of_le (le_refl _), bp.1]⟩

lemma take_firstReturn_isBalanced : IsBalanced (p.take (p.firstReturn + 1)) := by
  have := findIdx_get (w := (length_range p.length).symm ▸ firstReturn_lt_length bp np)
  simp only [get_range, decide_eq_true_eq] at this
  exact bp.from_take this

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

variable {p : DyckPath} (bp : p.IsBalanced) (np : p ≠ [])

lemma count_U_eq_count_D_of_firstReturn :
    (p.take (p.firstReturn + 1)).count U = (p.take (p.firstReturn + 1)).count D := by
  have := findIdx_get (w := (length_range p.length).symm ▸ firstReturn_lt_length bp np)
  simpa only [get_range, decide_eq_true_eq]

theorem leftPart_isBalanced : p.leftPart.IsBalanced := by
  have := firstReturn_lt_length bp np
  rw [leftPart, take_firstReturn_eq_dropLast bp np]
  apply (bp.from_take (count_U_eq_count_D_of_firstReturn bp np)).denest
    (take_firstReturn_ne_nil np)
  intro i hi
  rw [length_take, min_eq_left (by omega)] at hi
  rw [take_take, min_eq_left_of_lt hi.2]
  have ne := not_of_lt_findIdx (show i - 1 < p.firstReturn by omega)
  rw [get_range, decide_eq_true_eq, ← ne_eq, Nat.sub_add_cancel hi.1] at ne
  exact lt_of_le_of_ne (bp.2 i) ne.symm

theorem rightPart_isBalanced : p.rightPart.IsBalanced :=
  (bp.split _).mp <| bp.from_take (count_U_eq_count_D_of_firstReturn bp np)

theorem eq_U_leftPart_D_rightPart : p = ↑[U] ++ p.leftPart ++ ↑[D] ++ p.rightPart := by
  nth_rw 1 [← p.take_append_drop (p.firstReturn + 1)]; congr
  rw [leftPart, take_firstReturn_eq_dropLast bp np]
  exact append_tail_dropLast_append (take_firstReturn_isBalanced bp np) (take_firstReturn_ne_nil np)

theorem leftPart_length_lt : p.leftPart.length < p.length := by
  conv_rhs => rw [eq_U_leftPart_D_rightPart bp np]
  simp_rw [length_append, length_singleton]; omega

theorem rightPart_length_lt : p.rightPart.length < p.length := by
  conv_rhs => rw [eq_U_leftPart_D_rightPart bp np]
  simp_rw [length_append, length_singleton]; omega

variable {q : DyckPath}

theorem compose_firstReturn : (↑[U] ++ p ++ ↑[D] ++ q).firstReturn = p.length + 1 := by
  rw [firstReturn]; apply eq_findIdx_of_not
  pick_goal 3; · simp_rw [length_range, length_append, length_singleton]; omega
  all_goals simp only [get_range, decide_eq_true_eq]
  · intro j hji
    simp_rw [append_assoc _ _ [D], singleton_append, take_append_eq_append_take, length_cons,
      length_append, show j + 1 - (p.length + [D].length).succ = 0 by omega, take_zero,
      append_nil, take_cons, count_cons, ite_true, ite_false, take_append_eq_append_take,
      show j - p.length = 0 by omega, take_zero, append_nil]
    have := bp.2 j; omega
  · simp_rw [take_append_eq_append_take (l₂ := q), length_append, length_singleton,
      show p.length + 1 + 1 - (1 + p.length + 1) = 0 by omega, take_zero, append_nil]
    rw [take_all_of_le, bp.nest.1]; simp_rw [length_append, length_singleton]; omega

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
def treeEquivToFun (st : { p : DyckPath // p.IsBalanced }) : Tree Unit :=
  if e : st.1.length = 0 then nil else by
    obtain ⟨p, bp⟩ := st
    simp only [length_eq_zero] at e
    have := leftPart_length_lt bp e
    have := rightPart_length_lt bp e
    exact treeEquivToFun ⟨_, leftPart_isBalanced bp e⟩ △
      treeEquivToFun ⟨_, rightPart_isBalanced bp e⟩
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
  · rw [treeEquivInvFun']; exact bl.nest.append br

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
  toFun := fun ⟨p, ⟨bp, len⟩⟩ ↦
    ⟨treeEquiv ⟨p, bp⟩, by rw [mem_treesOfNumNodesEq, ← length_eq_two_mul_iff_numNodes_eq, len]⟩
  invFun := fun ⟨tr, sz⟩ ↦
    ⟨(treeEquiv.symm tr).1, ⟨(treeEquiv.symm tr).2, by rwa [length_eq_two_mul_iff_numNodes_eq,
      ← mem_treesOfNumNodesEq, Equiv.apply_symm_apply]⟩⟩
  left_inv := fun ⟨p, ⟨bp, len⟩⟩ ↦ by simp only [Equiv.symm_apply_apply]
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
