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
respectively, `3 + (x + y)` and `4 + (x + y)`, which differ by an additive constant.

## Main declarations

* `Mathlib.Tactic.Ring.proveLE`: prove goals of the form `A ≤ B` (subject to the scope constraints
  described)
* `Mathlib.Tactic.Ring.proveLT`: prove goals of the form `A < B` (subject to the scope constraints
  described)

## Implementation notes

The automation is provided in the `MetaM` monad; that is, these functions are not user-facing. It
would not be hard to provide user-facing versions (see the test file), but the scope of this
automation is rather specialized and might be confusing to users.

However, this automation serves as the discharger for the `linear_combination` tactic on inequality
goals, so it is available to the user indirectly as the "degenerate" case of that tactic -- that is,
by calling `linear_combination` without arguments.
-/

namespace Mathlib.Tactic.Ring

open Lean Qq Meta

/-! Rather than having the metaprograms `Mathlib.Tactic.Ring.evalLE.lean` and
`Mathlib.Tactic.Ring.evalLT.lean` perform all type class inference at the point of use, we record in
advance, as `abbrev`s, a few type class deductions which will certainly be necessary.  They add no
new information (they can already be proved by `inferInstance`).

This helps in speeding up the metaprograms in this file substantially -- about a 50% reduction in
heartbeat count in representative test cases -- since otherwise a substantial fraction of their
runtime is devoted to type class inference. -/

section Typeclass

/-- `CommSemiring` implies `AddMonoidWithOne`. -/
abbrev amwo_of_cs (α : Type*) [CommSemiring α] : AddMonoidWithOne α := inferInstance

/-- `PartialOrder` implies `LE`. -/
abbrev le_of_po (α : Type*) [PartialOrder α] : LE α := inferInstance

/-- `PartialOrder` implies `LT`. -/
abbrev lt_of_po (α : Type*) [PartialOrder α] : LT α := inferInstance

end Typeclass

/-! The lemmas like `add_le_add_right` in the root namespace are stated under minimal type classes,
typically just `[AddRightMono α]` or similar.  Here we restate these
lemmas under stronger type class assumptions (`[OrderedCommSemiring α]` or similar), which helps in
speeding up the metaprograms in this file (`Mathlib.Tactic.Ring.proveLT.lean` and
`Mathlib.Tactic.Ring.proveLE.lean`) substantially -- about a 50% reduction in heartbeat count in
representative test cases -- since otherwise a substantial fraction of their runtime is devoted to
type class inference.

These metaprograms at least require `CommSemiring`, `LE`/`LT`, and all
`CovariantClass`/`ContravariantClass` permutations for addition, and in their main use case (in
`linear_combination`) the `Preorder` type class is also required, so it is rather little loss of
generality simply to require `OrderedCommSemiring`/`StrictOrderedCommSemiring`. -/

section Lemma

theorem add_le_add_right {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    {b c : α} (bc : b ≤ c) (a : α) :
    b + a ≤ c + a :=
  _root_.add_le_add_right bc a

theorem add_le_of_nonpos_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    (a : α) {b : α} (h : b ≤ 0) :
    b + a ≤ a :=
  _root_.add_le_of_nonpos_left h

theorem le_add_of_nonneg_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    (a : α) {b : α} (h : 0 ≤ b) :
    a ≤ b + a :=
  _root_.le_add_of_nonneg_left h

theorem add_lt_add_right {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    {b c : α} (bc : b < c) (a : α) :
    b + a < c + a :=
  _root_.add_lt_add_right bc a

theorem add_lt_of_neg_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) {b : α} (h : b < 0) :
    b + a < a :=
  _root_.add_lt_of_neg_left a h

theorem lt_add_of_pos_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) {b : α} (h : 0 < b) :
    a < b + a :=
  _root_.lt_add_of_pos_left a h

end Lemma

/-- Inductive type carrying the two kinds of errors which can arise in the metaprograms
`Mathlib.Tactic.Ring.evalLE.lean` and `Mathlib.Tactic.Ring.evalLT.lean`. -/
inductive ExceptType | tooSmall | notComparable
export ExceptType (tooSmall notComparable)

/-- In a commutative semiring, given `Ring.ExSum` objects `va`, `vb` which differ by a positive
(additive) constant, construct a proof of `$a < $b`, where `a` (resp. `b`) is the expression in the
semiring to which `va` (resp. `vb`) evaluates. -/
def evalLE {v : Level} {α : Q(Type v)}
    (ics : Q(CommSemiring $α)) (_ : Q(PartialOrder $α)) (_ : Q(IsOrderedRing $α))
    {a b : Q($α)} (va : Ring.ExSum q($ics) a) (vb : Ring.ExSum q($ics) b) :
    MetaM (Except ExceptType Q($a ≤ $b)) := do
  let lα : Q(LE $α) := q(le_of_po $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(amwo_of_cs $α) (mkRawNatLit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(amwo_of_cs $α) (mkRawNatLit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  /- `0 ≤ 0` -/
  | .zero, .zero => pure <| .ok (q(le_refl (0:$α)):)
  /- For numerals `ca` and `cb`, `ca + x ≤ cb + x` if `ca ≤ cb` -/
  | .add (b := a') (.const (e := xa) ca hypa) va', .add (.const (e := xb) cb hypb) vb' => do
    unless va'.eq vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_le_add_right (a := $a') $pf):)
  /- For a numeral `ca ≤ 0`, `ca + x ≤ x` -/
  | .add (.const (e := xa) ca hypa) va', _ => do
    unless va'.eq vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rz | return .error tooSmall
    pure <| .ok (q(add_le_of_nonpos_left (a := $b) $pf):)
  /- For a numeral `0 ≤ cb`, `x ≤ cb + x` -/
  | _, .add (.const (e := xb) cb hypb) vb' => do
    unless va.eq vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rz rxb | return .error tooSmall
    pure <| .ok (q(le_add_of_nonneg_left (a := $a) $pf):)
  | _, _ =>
    unless va.eq vb do return .error notComparable
    pure <| .ok (q(le_refl $a):)
--[CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
/-- In a commutative semiring, given `Ring.ExSum` objects `va`, `vb` which differ by a positive
(additive) constant, construct a proof of `$a < $b`, where `a` (resp. `b`) is the expression in the
semiring to which `va` (resp. `vb`) evaluates. -/
def evalLT {v : Level} {α : Q(Type v)}
    (ics : Q(CommSemiring $α)) (_ : Q(PartialOrder $α)) (_ : Q(IsStrictOrderedRing $α))
    {a b : Q($α)} (va : Ring.ExSum q($ics) a) (vb : Ring.ExSum q($ics) b) :
    MetaM (Except ExceptType Q($a < $b)) := do
  let lα : Q(LT $α) := q(lt_of_po $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(amwo_of_cs $α) (mkRawNatLit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(amwo_of_cs $α) (mkRawNatLit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  /- `0 < 0` -/
  | .zero, .zero => return .error tooSmall
  /- For numerals `ca` and `cb`, `ca + x < cb + x` if `ca < cb` -/
  | .add (b := a') (.const (e := xa) ca hypa) va', .add (.const (e := xb) cb hypb) vb' => do
    unless va'.eq vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_lt_add_right $pf $a'):)
  /- For a numeral `ca < 0`, `ca + x < x` -/
  | .add (.const (e := xa) ca hypa) va', _ => do
    unless va'.eq vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rz | return .error tooSmall
    have pf : Q($xa < 0) := pf
    pure <| .ok (q(add_lt_of_neg_left $b $pf):)
  /- For a numeral `0 < cb`, `x < cb + x` -/
  | _, .add (.const (e := xb) cb hypb) vb' => do
    unless va.eq vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rz rxb | return .error tooSmall
    pure <| .ok (q(lt_add_of_pos_left $a $pf):)
  | _, _ => return .error notComparable

theorem le_congr {α : Type*} [LE α] {a b c d : α} (h1 : a = b) (h2 : b ≤ c) (h3 : d = c) :
    a ≤ d := by
  rwa [h1, h3]

theorem lt_congr {α : Type*} [LT α] {a b c d : α} (h1 : a = b) (h2 : b < c) (h3 : d = c) :
    a < d := by
  rwa [h1, h3]

attribute [local instance] monadLiftOptionMetaM in
/-- Prove goals of the form `A ≤ B` in an ordered commutative semiring, if the ring-normal forms of
`A` and `B` differ by a nonnegative (additive) constant. -/
def proveLE (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A ≤ B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthInstanceQ q(CommSemiring $α)
  let ipo ← synthInstanceQ q(PartialOrder $α)
  let sα ← synthInstanceQ q(IsOrderedRing $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← mkCache q($ics)
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩)
    ← AtomM.run .instances do pure (← eval q($ics) c e₁, ← eval q($ics) c e₂)
  match ← evalLE ics ipo sα va vb with
  | .ok p => g.assign q(le_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a ≤ $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to an additive constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is larger\n{g'.mvarId!}"

attribute [local instance] monadLiftOptionMetaM in
/-- Prove goals of the form `A < B` in an ordered commutative semiring, if the ring-normal forms of
`A` and `B` differ by a positive (additive) constant. -/
def proveLT (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).lt?
    | throwError "ring failed: not of the form `A < B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthInstanceQ q(CommSemiring $α)
  let ipo ← synthInstanceQ q(PartialOrder $α)
  let sα ← synthInstanceQ q(IsStrictOrderedRing $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← mkCache q($ics)
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩)
    ← AtomM.run .instances do pure (← eval q($ics) c e₁, ← eval q($ics) c e₂)
  match ← evalLT ics ipo sα va vb with
  | .ok p => g.assign q(lt_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a < $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to an additive constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is at least as large\n{g'.mvarId!}"

end Mathlib.Tactic.Ring
