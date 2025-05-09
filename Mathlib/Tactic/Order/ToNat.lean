/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Order.CollectFacts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Facts preprocessing for the `order` tactic

In this file we implement the preprocessing procedure for the `order` tactic.
See `Mathlib.Tactic.Order` for details of preprocessing.
-/

namespace Mathlib.Tactic.Order

section Lemmas

lemma exists_max {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin (n + 1) → α) :
    ∃ imax, ∀ j, val j ≤ val imax := by
  induction n with
  | zero => simp [Fin.forall_fin_one, Fin.exists_fin_one]
  | succ n ih =>
    cases val using Fin.consCases with | _ x val =>
    obtain ⟨i, hi⟩ := ih val
    by_cases h_max : val i < x
    · use 0
      intro j
      cases j using Fin.cases with
      | zero => simp
      | succ j =>
        simp only [Fin.cons_succ, Fin.cons_zero]
        apply (hi _).trans
        exact le_of_lt h_max
    · use i.succ
      intro j
      cases j using Fin.cases with
      | zero => simpa using h_max
      | succ j => simp [hi]

lemma exists_bound {n : ℕ} (tr : Fin n → ℕ) : ∃ M, ∀ i, tr i < M := by
  cases n with
  | zero => simp
  | succ n =>
    obtain ⟨i, hi⟩ := exists_max tr
    use tr i + 1
    intro j
    specialize hi j
    omega

theorem exists_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) : ∃ tr : Fin n → ℕ,
    ∀ i j, val i ≤ val j ↔ tr i ≤ tr j := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨imax, h_imax⟩ := exists_max val
    obtain ⟨tr, h2⟩ := ih (Fin.removeNth imax val)
    by_cases h_imax' : ∃ j : Fin n, val (imax.succAbove j) = val imax
    · obtain ⟨imax2, h3⟩ := h_imax'
      use Fin.insertNth imax (tr imax2) tr
      intro i j
      cases i using Fin.succAboveCases imax <;> cases j using Fin.succAboveCases imax
        <;> simp [← h3, ← h2, Fin.removeNth]
    · push_neg at h_imax'
      obtain ⟨M, hM⟩ : ∃ M, ∀ i, tr i < M := exists_bound tr
      use Fin.insertNth imax M tr
      have h_succ (i : Fin n) : val (Fin.succAbove imax i) < val imax :=
        lt_of_le_of_ne (h_imax (Fin.succAbove imax i)) (h_imax' i)
      intro i j
      cases i using Fin.succAboveCases imax <;> cases j using Fin.succAboveCases imax
        <;> simp [(hM _).not_le, (hM _).le, h_succ, h_imax, ← h2, Fin.removeNth]

/-- Auxiliary definition used by the `order` tactic to
transfer facts in a linear order to `Nat`. -/
noncomputable def translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α)
    (k : Fin n) : ℕ :=
  (exists_translation val).choose k

theorem translation_le_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i ≤ translation val j ↔ val i ≤ val j := by
  simp [translation, (exists_translation val).choose_spec]

theorem translation_lt_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i < translation val j ↔ val i < val j := by
  intro i j
  simpa using (translation_le_translation val j i).not

theorem translation_eq_translation {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α) :
    ∀ i j, translation val i = translation val j ↔ val i = val j := by
  simp [translation_le_translation, le_antisymm_iff]

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
def get (tree : BinTree α) {m : Nat} (n : Fin m) : α :=
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
  let m : Q(ℕ) := mkNatLit atoms.size
  q(($tree).get (m := $m))

end BinTree

/--
Translates a set of values in a linear ordered type to `ℕ`,
preserving all the facts except for `.isTop` and `.isBot`.
-/
def translateToNat {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $type))
    (idxToAtom : Std.HashMap ℕ Q($type))
    (facts : Array AtomicFact) :
    Std.HashMap ℕ Q(ℕ) × Array AtomicFact :=
  haveI mkNatQ : ℕ → Q(ℕ) := Lean.mkNatLit
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
