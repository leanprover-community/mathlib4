/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Data.Int.ModEq

/-! # `mod_cases` tactic

The `mod_cases` tactic does case disjunction on `e % n`, where `e : ℤ` or `e : ℕ`,
to yield `n` new subgoals corresponding to the possible values of `e` modulo `n`.
-/

set_option autoImplicit true

namespace Mathlib.Tactic.ModCases
open Lean Meta Elab Tactic Term Qq

namespace IntMod
open Int

/--
`OnModCases n a lb p` represents a partial proof by cases that
there exists `0 ≤ z < n` such that `a ≡ z (mod n)`.
It asserts that if `∃ z, lb ≤ z < n ∧ a ≡ z (mod n)` holds, then `p`
(where `p` is the current goal).
-/
def OnModCases (n : ℕ) (a : ℤ) (lb : ℕ) (p : Sort*) :=
  ∀ z, lb ≤ z ∧ z < n ∧ a ≡ ↑z [ZMOD ↑n] → p

/--
The first theorem we apply says that `∃ z, 0 ≤ z < n ∧ a ≡ z (mod n)`.
The actual mathematical content of the proof is here.
-/
@[inline] def onModCases_start (p : Sort*) (a : ℤ) (n : ℕ) (hn : Nat.ble 1 n = true)
    (H : OnModCases n a (nat_lit 0) p) : p :=
  H (a % ↑n).toNat <| by
    have := ofNat_pos.2 <| Nat.le_of_ble_eq_true hn
    have nonneg := emod_nonneg a <| Int.ne_of_gt this
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · rw [Int.toNat_lt nonneg]; exact Int.emod_lt_of_pos _ this
    · rw [Int.ModEq, Int.toNat_of_nonneg nonneg, emod_emod]

/--
The end point is that once we have reduced to `∃ z, n ≤ z < n ∧ a ≡ z (mod n)`
there are no more cases to consider.
-/
@[inline] def onModCases_stop (p : Sort*) (n : ℕ) (a : ℤ) : OnModCases n a n p :=
  fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

/--
The successor case decomposes `∃ z, b ≤ z < n ∧ a ≡ z (mod n)` into
`a ≡ b (mod n) ∨ ∃ z, b+1 ≤ z < n ∧ a ≡ z (mod n)`,
and the `a ≡ b (mod n) → p` case becomes a subgoal.
-/
@[inline] def onModCases_succ {p : Sort*} {n : ℕ} {a : ℤ} (b : ℕ)
    (h : a ≡ OfNat.ofNat b [ZMOD OfNat.ofNat n] → p) (H : OnModCases n a (Nat.add b 1) p) :
    OnModCases n a b p :=
  fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

/--
Proves an expression of the form `OnModCases n a b p` where `n` and `b` are raw nat literals
and `b ≤ n`. Returns the list of subgoals `?gi : a ≡ i [ZMOD n] → p`.
-/
partial def proveOnModCases (n : Q(ℕ)) (a : Q(ℤ)) (b : Q(ℕ)) (p : Q(Sort u)) :
    MetaM (Q(OnModCases $n $a $b $p) × List MVarId) := do
  if n.natLit! ≤ b.natLit! then
    haveI' : $b =Q $n := ⟨⟩
    pure (q(onModCases_stop $p $n $a), [])
  else
    let ty := q($a ≡ OfNat.ofNat $b [ZMOD OfNat.ofNat $n] → $p)
    let g ← mkFreshExprMVarQ ty
    have b1 : Q(ℕ) := mkRawNatLit (b.natLit! + 1)
    haveI' : $b1 =Q ($b).succ := ⟨⟩
    let (pr, acc) ← proveOnModCases n a b1 p
    pure (q(onModCases_succ $b $g $pr), g.mvarId! :: acc)

/--
Int case of `mod_cases h : e % n`.
-/
def modCases (h : TSyntax `Lean.binderIdent) (e : Q(ℤ)) (n : ℕ) : TacticM Unit := do
  let ⟨u, p, g⟩ ← inferTypeQ (.mvar (← getMainGoal))
  have lit : Q(ℕ) := mkRawNatLit n
  let p₁ : Nat.ble 1 $lit =Q true := ⟨⟩
  let (p₂, gs) ← proveOnModCases lit e (mkRawNatLit 0) p
  let gs ← gs.mapM fun g => do
    let (fvar, g) ← match h with
    | `(binderIdent| $n:ident) => g.intro n.getId
    | _ => g.intro `H
    g.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
    pure g
  g.mvarId!.assign q(onModCases_start $p $e $lit $p₁ $p₂)
  replaceMainGoal gs

end IntMod

namespace NatMod

/--
`OnModCases n a lb p` represents a partial proof by cases that
there exists `0 ≤ m < n` such that `a ≡ m (mod n)`.
It asserts that if `∃ m, lb ≤ m < n ∧ a ≡ m (mod n)` holds, then `p`
(where `p` is the current goal).
-/
def OnModCases (n : ℕ) (a : ℕ) (lb : ℕ) (p : Sort _) :=
  ∀ m, lb ≤ m ∧ m < n ∧ a ≡ m [MOD n] → p

/--
The first theorem we apply says that `∃ m, 0 ≤ m < n ∧ a ≡ m (mod n)`.
The actual mathematical content of the proof is here.
-/
@[inline] def onModCases_start (p : Sort _) (a : ℕ) (n : ℕ) (hn : Nat.ble 1 n = true)
    (H : OnModCases n a (nat_lit 0) p) : p :=
  H (a % n) <| by
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · exact Nat.mod_lt _ (Nat.le_of_ble_eq_true hn)
    · rw [Nat.ModEq, Nat.mod_mod]


/--
The end point is that once we have reduced to `∃ m, n ≤ m < n ∧ a ≡ m (mod n)`
there are no more cases to consider.
-/
@[inline] def onModCases_stop (p : Sort _) (n : ℕ) (a : ℕ) : OnModCases n a n p :=
  fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

/--
The successor case decomposes `∃ m, b ≤ m < n ∧ a ≡ m (mod n)` into
`a ≡ b (mod n) ∨ ∃ m, b+1 ≤ m < n ∧ a ≡ m (mod n)`,
and the `a ≡ b (mod n) → p` case becomes a subgoal.
-/
@[inline] def onModCases_succ {p : Sort _} {n : ℕ} {a : ℕ} (b : ℕ)
    (h : a ≡ b [MOD n] → p) (H : OnModCases n a (Nat.add b 1) p) :
    OnModCases n a b p :=
  fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

/--
Proves an expression of the form `OnModCases n a b p` where `n` and `b` are raw nat literals
and `b ≤ n`. Returns the list of subgoals `?gi : a ≡ i [MOD n] → p`.
-/
partial def proveOnModCases (n : Q(ℕ)) (a : Q(ℕ)) (b : Q(ℕ)) (p : Q(Sort u)) :
    MetaM (Q(OnModCases $n $a $b $p) × List MVarId) := do
  if n.natLit! ≤ b.natLit! then
    pure ((q(onModCases_stop $p $n $a) : Expr), [])
  else
    let ty := q($a ≡ $b [MOD $n] → $p)
    let g ← mkFreshExprMVarQ ty
    let ((pr : Q(OnModCases $n $a (Nat.add $b 1) $p)), acc) ←
      proveOnModCases n a (mkRawNatLit (b.natLit! + 1)) p
    pure ((q(onModCases_succ $b $g $pr) : Expr), g.mvarId! :: acc)

/--
Nat case of `mod_cases h : e % n`.
-/
def modCases (h : TSyntax `Lean.binderIdent) (e : Q(ℕ)) (n : ℕ) : TacticM Unit := do
  let ⟨u, p, g⟩ ← inferTypeQ (.mvar (← getMainGoal))
  have lit : Q(ℕ) := mkRawNatLit n
  let p₁ : Q(Nat.ble 1 $lit = true) := (q(Eq.refl true) : Expr)
  let (p₂, gs) ← proveOnModCases lit e (mkRawNatLit 0) p
  let gs ← gs.mapM fun g => do
    let (fvar, g) ← match h with
    | `(binderIdent| $n:ident) => g.intro n.getId
    | _ => g.intro `H
    g.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
    pure g
  g.mvarId!.assign q(onModCases_start $p $e $lit $p₁ $p₂)
  replaceMainGoal gs

end NatMod

/--
* The tactic `mod_cases h : e % 3` will perform a case disjunction on `e`.
  If `e : ℤ`, then it will yield subgoals containing the assumptions
  `h : e ≡ 0 [ZMOD 3]`, `h : e ≡ 1 [ZMOD 3]`, `h : e ≡ 2 [ZMOD 3]`
  respectively. If `e : ℕ` instead, then it works similarly, except with
  `[MOD 3]` instead of `[ZMOD 3]`.
* In general, `mod_cases h : e % n` works
  when `n` is a positive numeral and `e` is an expression of type `ℕ` or `ℤ`.
* If `h` is omitted as in `mod_cases e % n`, it will be default-named `H`.
-/
syntax "mod_cases " (atomic(binderIdent ":"))? term:71 " % " num : tactic

elab_rules : tactic
  | `(tactic| mod_cases $[$h :]? $e % $n) => do
    let n := n.getNat
    if n == 0 then Elab.throwUnsupportedSyntax
    let h := h.getD (← `(binderIdent| _))
    withMainContext do
    let e ← Tactic.elabTerm e none
    let α : Q(Type) ← inferType e
    match α with
    | ~q(ℤ) => IntMod.modCases h e n
    | ~q(ℕ) => NatMod.modCases h e n
    | _ => throwError "mod_cases only works with Int and Nat"
