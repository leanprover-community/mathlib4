/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Order.CollectFacts
import Mathlib.Data.Set.Finite.Basic

/-!
# Facts preprocessing for the `order` tactic

In this file we implement the preprocessing procedure for the `order` tactic.
See `Mathlib.Tactic.Order` for details of preprocessing.
-/

namespace Mathlib.Tactic.Order

section Lemmas

/--
Auxiliary definition used by the `order` tactic to
transfer facts in a linear order to `Nat`
-/
def translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) (k : Fin n) : ℕ :=
  (Finset.image val {u : Fin n | val u < val k}).card

theorem translation_le_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i ≤ translation val j ↔ val i ≤ val j := by
  intro i j
  have hi := Finset.mem_univ i
  have hj := Finset.mem_univ j
  generalize @Finset.univ (Fin n) _ = s at hi hj
  induction s using Finset.strongInduction with | _ s ih =>
  have hs : s.Nonempty := ⟨i, hi⟩
  obtain ⟨m, hms, hm⟩ := Set.Finite.exists_maximal_wrt val s s.finite_toSet hs.to_set
  rw [Finset.mem_coe] at hms
  let t : Finset (Fin n) := {u ∈ s | val u < val m}
  have ht : t ⊂ s := by
    rw [Finset.ssubset_def]
    constructor
    · apply Finset.filter_subset
    · intro hst
      apply lt_irrefl (val m)
      exact (Finset.mem_filter.mp (hst hms)).right
  have hmm (k : Fin n) (hk : k ∈ s) : val k ≤ val m :=
    (le_total (val k) (val m)).elim id fun h => by rw [hm k hk h]
  obtain him | him := lt_or_eq_of_le (hmm i hi) <;> obtain hjm | hjm := lt_or_eq_of_le (hmm j hj)
  · exact ih t ht (Finset.mem_filter.mpr ⟨hi, him⟩) (Finset.mem_filter.mpr ⟨hj, hjm⟩)
  · rw [hjm, iff_true_right him.le]
    apply Finset.card_le_card
    apply Finset.image_subset_image
    apply Finset.monotone_filter_right
    intro u hu
    rw [hjm]
    exact hu.trans him
  · rw [him, iff_false_right hjm.not_le, not_le]
    apply Finset.card_lt_card
    rw [him, Finset.ssubset_def]
    constructor
    · apply Finset.image_subset_image
      apply Finset.monotone_filter_right
      intro u hu
      exact hu.trans hjm
    · intro hii
      have hjj :=
        hii (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjm⟩, rfl⟩)
      rw [Finset.mem_image] at hjj
      obtain ⟨k, hk, hkj⟩ := hjj
      rw [Finset.mem_filter] at hk
      rw [hkj] at hk
      exact hk.right.false
  · rw [him, hjm, iff_true_right le_rfl, translation, him, translation, hjm]

theorem translation_lt_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i < translation val j ↔ val i < val j := by
  intro i j
  simpa using (translation_le_translation val j i).not

theorem translation_eq_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i = translation val j ↔ val i = val j := by
  simp_rw [le_antisymm_iff, translation_le_translation, implies_true]

theorem translation_ne_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i ≠ translation val j ↔ val i ≠ val j := by
  intro i j
  simpa using (translation_eq_translation val i j).not

theorem translation_nle_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, ¬translation val i ≤ translation val j ↔ ¬val i ≤ val j := by
  intro i j
  simpa using translation_lt_translation val j i

theorem translation_nlt_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, ¬translation val i < translation val j ↔ ¬val i < val j := by
  intro i j
  simpa using translation_le_translation val j i

theorem translation_sup_translation_eq_translation {α : Type*} [LinearOrder α] {n : ℕ}
    (val : Fin n → α) : ∀ i j k, translation val i ⊔ translation val j = translation val k ↔
      val i ⊔ val j = val k := by
  intro i j k
  simp_rw [le_antisymm_iff, sup_le_iff, le_sup_iff, translation_le_translation]

theorem translation_inf_translation_eq_translation {α : Type*} [LinearOrder α] {n : ℕ}
    (val : Fin n → α) : ∀ i j k, translation val i ⊓ translation val j = translation val k ↔
      val i ⊓ val j = val k := by
  intro i j k
  simp_rw [le_antisymm_iff, inf_le_iff, le_inf_iff, translation_le_translation]

end Lemmas

open Qq

/--
Labeled binary tree, with leaves labeled by `α` and nodes labeled by `ℕ`.
-/
inductive BinTree (α : Type*) where
| leaf : α → BinTree α
| node : Nat → BinTree α → BinTree α → BinTree α

namespace BinTree

variable {α : Type*}

/--
Get a value out of a binary tree, deciding at each fork whether to go left or right
by comparing to the label.
-/
def get (tree : BinTree α) (n : Nat) : α :=
  match tree with
  | leaf a => a
  | node m l r => if n < m then l.get n else r.get n

open Lean Qq

/--
Given a nonempty array `atoms`, create an expression representing a binary tree `t`
such that `t.get n` is defeq to `atoms[n]` for `n < atoms.size`.
-/
def mkExpr {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) (_ : atoms.size ≠ 0) :
    Q(BinTree $α) :=
  go 0 atoms.size
where
  /--
  Auxiliary definition for `Mathlib.Tactic.Order.Bintree.mkExpr`. Builds a tree,
  using `atoms`, with nodes lying between `lo` and `hi`.
  -/
  go (lo hi : Nat) (_ : lo < hi := by omega) (_ : hi ≤ atoms.size := by omega) : Q(BinTree $α) :=
    let mid := (lo + hi) / 2
    if h : lo = mid then
      q(leaf $(atoms[lo]))
    else
      let l := go lo mid
      let r := go mid hi
      let n : Q(Nat) := mkRawNatLit mid
      q(node $n $l $r)
  termination_by hi - lo

/--
Given an array `atoms : Array α`, create an expression representing a function
`f : Fin atoms.size → α` such that `f n` is defeq to `atoms[n]` for `n : Fin n`.
-/
def mkFinFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : Expr :=
  if h : atoms.isEmpty then q(Fin.elim0 : Fin 0 → $α) else
  let tree := BinTree.mkExpr atoms (mt Array.isEmpty_iff_size_eq_zero.mpr h)
  q(($tree).get)

end BinTree

/--
Translates a set of values in a linear ordered type to `ℕ`,
preserving all the facts except for `.isTop` and `.isBot`.
-/
def translateToNat {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $type))
    (idxToAtom : Std.HashMap ℕ Q($type))
    (facts : Array AtomicFact) :
    Std.HashMap ℕ Q(ℕ) × Array AtomicFact :=
  haveI mkNatQ : ℕ → Q(ℕ) := Lean.mkRawNatLit
  haveI nE : Q(ℕ) := mkNatQ idxToAtom.size
  haveI finFun : Q(Fin $nE → $type) :=
    BinTree.mkFinFun (Array.ofFn fun (n : Fin idxToAtom.size) => idxToAtom[n]!)
  haveI toFinUnsafe : ℕ → Q(Fin $nE) := fun k =>
    haveI kE := mkNatQ k
    haveI heq : decide ($kE < $nE) =Q true := ⟨⟩
    q(⟨$kE, of_decide_eq_true $heq⟩)
  Prod.snd <| facts.foldl (fun (curr, map, facts) fact =>
    match fact with
    | .eq lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin = $finFun $rhsFin) := prf
        .eq lhs rhs q((translation_eq_translation $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .ne lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin ≠ $finFun $rhsFin) := prf
        .ne lhs rhs q((translation_ne_translation $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .le lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin ≤ $finFun $rhsFin) := prf
        .le lhs rhs q((translation_le_translation $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .lt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin < $finFun $rhsFin) := prf
        .lt lhs rhs q((translation_lt_translation $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nle lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin ≤ $finFun $rhsFin) := prf
        .nle lhs rhs q((translation_nle_translation $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nlt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin < $finFun $rhsFin) := prf
        .nlt lhs rhs q((translation_nlt_translation $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .isBot _
    | .isTop _ => (curr, map, facts)
    | .isSup lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
      haveI heq : max («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q «$finFun» «$valFin» := ⟨⟩
      (curr + 1, map.insert curr q(translation $finFun $lhsFin ⊔ translation $finFun $rhsFin),
        (facts.push (.isSup lhs rhs curr)).push (.eq curr val
          q((translation_sup_translation_eq_translation $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      )
    | .isInf lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
      haveI heq : min («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q «$finFun» «$valFin» := ⟨⟩
      (curr + 1, map.insert curr q(translation $finFun $lhsFin ⊓ translation $finFun $rhsFin),
        (facts.push (.isInf lhs rhs curr)).push (.eq curr val
          q((translation_inf_translation_eq_translation $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      ))
    (idxToAtom.size, idxToAtom.map fun k _ =>
      haveI kFin := toFinUnsafe k
      q(translation $finFun $kFin), Array.emptyWithCapacity idxToAtom.size)

end Mathlib.Tactic.Order
