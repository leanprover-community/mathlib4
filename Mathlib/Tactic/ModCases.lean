/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Data.Int.ModEq

/-! # `mod_cases` tactic

The `mod_cases` tactic does case disjunction on `e % n`, where `e : ℤ`, to yield a number of
subgoals in which `e ≡ 0 [ZMOD n]`, ..., `e ≡ n-1 [ZMOD n]` are assumed.
-/

set_option autoImplicit true

namespace Mathlib.Tactic.ModCases
open Lean Meta Elab Tactic Term Qq Int

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
    -- ⊢ 0 ≤ toNat (a % ↑n) ∧ toNat (a % ↑n) < n ∧ a ≡ ↑(toNat (a % ↑n)) [ZMOD ↑n]
    have nonneg := emod_nonneg a <| Int.ne_of_gt this
    -- ⊢ 0 ≤ toNat (a % ↑n) ∧ toNat (a % ↑n) < n ∧ a ≡ ↑(toNat (a % ↑n)) [ZMOD ↑n]
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    -- ⊢ toNat (a % ↑n) < n
    · rw [Int.toNat_lt nonneg]; exact Int.emod_lt_of_pos _ this
      -- ⊢ a % ↑n < ↑n
                                -- 🎉 no goals
    · rw [Int.ModEq, Int.toNat_of_nonneg nonneg, emod_emod]
      -- 🎉 no goals

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
* The tactic `mod_cases h : e % 3` will perform a case disjunction on `e : ℤ` and yield subgoals
  containing the assumptions `h : e ≡ 0 [ZMOD 3]`, `h : e ≡ 1 [ZMOD 3]`, `h : e ≡ 2 [ZMOD 3]`
  respectively.
* In general, `mod_cases h : e % n` works
  when `n` is a positive numeral and `e` is an expression of type `ℤ`.
* If `h` is omitted as in `mod_cases e % n`, it will be default-named `H`.
-/
syntax "mod_cases " (atomic(binderIdent " : "))? term:71 " % " num : tactic

elab_rules : tactic
  | `(tactic| mod_cases $[$h :]? $e % $n) => do
    let n := n.getNat
    if n == 0 then Elab.throwUnsupportedSyntax
    let g ← getMainGoal
    g.withContext do
    let ⟨u, p, g⟩ ← inferTypeQ (.mvar g)
    let e : Q(ℤ) ← Tactic.elabTermEnsuringType e q(ℤ)
    let h := h.getD (← `(binderIdent| _))
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
