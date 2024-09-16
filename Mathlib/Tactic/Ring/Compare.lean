/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.NormNum.Ineq

/-!
# Automation for proving inequalities in commutative (semi)rings

This file provides automation for proving certain kinds of inequalities in commutative semirings:
goals of the form `A ≤ B` and `A < B` for which the ring-normal forms of `A` and `B` differ by a
nonnegative (resp. positive) constant.

For example, `⊢ x + 3 + y < y + x + 4` is in scope because the normal forms of the LHS and RHS are,
respectively, `3 + (x + y)` and `4 + (x + y)`, which differ by a constant.

## Main declarations

* `Mathlib.Tactic.Ring.proveLE`: prove goals of the form `A ≤ B` (subject to the scope constraints
  described)
* `Mathlib.Tactic.Ring.proveLT`: prove goals of the form `A < B` (subject to the scope constraints
  described)

## Implementation notes

The automation is provided in the `MetaM` monad; that is, these functions are not user-facing. It
would not be hard to provide user-facing versions (see the test file), but the scope of this
automation is rather specialized and might be confusing to users. It is also subsumed by `linarith`.
-/

namespace Mathlib.Tactic.Ring

open Lean Qq Meta

/-- Inductive type carrying the two kinds of errors which can arise in the metaprograms
`Mathlib.Tactic.Ring.evalLE` and `Mathlib.Tactic.Ring.evalLT`. -/
inductive ExceptType | tooSmall | notComparable
export ExceptType (tooSmall notComparable)

/-- In a commutative semiring, given `Ring.ExSum` objects `va`, `vb` which differ by a positive
constant, construct a proof of `$a < $b`, where `a` (resp. `b`) is the expression in the semiring to
which `va` (resp. `vb`) evaluates. -/
def evalLE {v : Level} {α : Q(Type v)} (sα : Q(CommSemiring $α)) (lα : Q(LE $α)) {a b : Q($α)}
    (va : Ring.ExSum sα a) (vb : Ring.ExSum sα b) : MetaM (Except ExceptType Q($a ≤ $b)) := do
  let mα ← synthInstanceQ q(AddMonoidWithOne $α)
  let _i ← synthInstanceQ q(CovariantClass $α $α (Function.swap (· + ·)) (· ≤ ·))
  let _i ← synthInstanceQ q(Preorder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α mα (mkRawNatLit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat mα (mkRawNatLit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  /- `0 ≤ 0` -/
  | .zero, .zero => pure <| .ok (q(le_refl (0:$α)):)
  /- For numerals `c₁` and `c₂`, `c₁ + x ≤ c₂ + x` if `c₁ ≤ c₂` -/
  | .add (b := a') (.const (e := xa) ca hypa) va', .add (.const (e := xb) cb hypb) vb' => do
    unless va'.eq vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_le_add_right (a := $a') $pf):)
  /- For a numeral `c ≤ 0`, `c + x ≤ x` -/
  | .add (.const (e := xa) ca hypa) va', _ => do
    unless va'.eq vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rz | return .error tooSmall
    pure <| .ok (q(add_le_of_nonpos_left (a := $b) $pf):)
  /- For a numeral `0 ≤ c`, `x ≤ c + x` -/
  | _, .add (.const (e := xb) cb hypb) vb' => do
    unless va.eq vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rz rxb | return .error tooSmall
    pure <| .ok (q(le_add_of_nonneg_left (a := $a) $pf):)
  | _, _ => return .error notComparable

/-- In a commutative semiring, given `Ring.ExSum` objects `va`, `vb` which differ by a positive
constant, construct a proof of `$a < $b`, where `a` (resp. `b`) is the expression in the semiring to
which `va` (resp. `vb`) evaluates. -/
def evalLT {v : Level} {α : Q(Type v)} (sα : Q(CommSemiring $α)) (lα : Q(LT $α)) {a b : Q($α)}
    (va : Ring.ExSum sα a) (vb : Ring.ExSum sα b) : MetaM (Except ExceptType Q($a < $b)) := do
  let mα ← synthInstanceQ q(AddMonoidWithOne $α)
  let _i ← synthInstanceQ q(CovariantClass $α $α (Function.swap (· + ·)) (· < ·))
  let _i ← synthInstanceQ q(Preorder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α mα (mkRawNatLit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat mα (mkRawNatLit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  /- `0 < 0` -/
  | .zero, .zero => return .error tooSmall
  /- For numerals `c₁` and `c₂`, `c₁ + x < c₂ + x` if `c₁ < c₂` -/
  | .add (b := a') (.const (e := xa) ca hypa) va', .add (.const (e := xb) cb hypb) vb' => do
    unless va'.eq vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_lt_add_right (a := $a') $pf):)
  /- For a numeral `c < 0`, `c + x < x` -/
  | .add (.const (e := xa) ca hypa) va', _ => do
    unless va'.eq vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rz | return .error tooSmall
    pure <| .ok (q(add_lt_of_neg_left (a := $b) $pf):)
  /- For a numeral `0 < c`, `x < c + x` -/
  | _, .add (.const (e := xb) cb hypb) vb' => do
    unless va.eq vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rz rxb | return .error tooSmall
    pure <| .ok (q(lt_add_of_pos_left (a := $a) $pf):)
  | _, _ => return .error notComparable

theorem le_congr {α : Type*} [LE α] {a b c d : α} (h1 : a = b) (h2 : b ≤ c) (h3 : d = c) :
    a ≤ d := by
  rwa [h1, h3]

theorem lt_congr {α : Type*} [LT α] {a b c d : α} (h1 : a = b) (h2 : b < c) (h3 : d = c) :
    a < d := by
  rwa [h1, h3]

/-- Prove goals of the form `A ≤ B` in a commutative semiring, if the ring-normal forms of `A` and
`B` differ by a nonnegative constant. -/
def proveLE (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A ≤ B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(CommSemiring $α)
  let lα ← synthInstanceQ q(LE $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← mkCache sα
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩) ← AtomM.run .instances do pure (← eval sα c e₁, ← eval sα c e₂)
  match ← evalLE sα lα va vb with
  | .ok p => g.assign q(le_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a ≤ $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to a constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is larger\n{g'.mvarId!}"

/-- Prove goals of the form `A < B` in a commutative semiring, if the ring-normal forms of `A` and
`B` differ by a positive constant. -/
def proveLT (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).lt?
    | throwError "ring failed: not of the form `A < B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(CommSemiring $α)
  let lα ← synthInstanceQ q(LT $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← mkCache sα
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩) ← AtomM.run .instances do pure (← eval sα c e₁, ← eval sα c e₂)
  match ← evalLT sα lα va vb with
  | .ok p => g.assign q(lt_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a < $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to a constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is at least as large\n{g'.mvarId!}"

end Mathlib.Tactic.Ring
