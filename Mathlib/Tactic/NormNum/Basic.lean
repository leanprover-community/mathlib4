/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core
import Qq.Match

/-!
## `norm_num` basic plugins

This file adds `norm_num` plugins for `+`, `*` and `^` along with other basic operations.
-/

namespace Mathlib
open Lean Meta

/--
  Return `some n` if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def _root_.Lean.Expr.numeral? (e : Expr) : Option Nat :=
  if let some n := e.natLit? then n
  else
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none

namespace Meta.NormNum
open Qq

/-- Given a monadic function `k`
which takes typed expressions representing a semiring element to a `NormNum.Result`,
and lifts it to a `norm_num` extension. -/
def withSemiring
  (k : {u : Level} → (α : Q(Type u)) → Q($α) → Q(Semiring «$α») → MetaM Result) :
    NormNumExt where eval e := do
  let ⟨.succ u, α, e'⟩ ← inferTypeQ e | throwError "not data"
  k α e' (← synthInstanceQ (q(Semiring $α) : Q(Type u)) <|> throwError "not a semiring")

theorem isNat_zero (α) [Semiring α] : isNat (Zero.zero : α) (nat_lit 0) := Nat.cast_zero.symm

/-- The `norm_num` extension which identifies the expression `Zero.zero`, returning `0`. -/
@[norm_num Zero.zero] def evalZero : NormNumExt := withSemiring fun α e _i => do
  match e with
  | ~q(Zero.zero) =>
    return .isNat (mkRawNatLit 0) q(isNat_zero $α)

theorem isNat_one (α) [Semiring α] : isNat (One.one : α) (nat_lit 1) := Nat.cast_one.symm

/-- The `norm_num` extension which identifies the expression `One.one`, returning `1`. -/
@[norm_num One.one] def evalOne : NormNumExt := withSemiring fun α e _i => do
  match e with
  | ~q(One.one) =>
    return .isNat (mkRawNatLit 1) q(isNat_one $α)

/-- The `norm_num` extension which identifies an expression `OfNat.ofNat n`, returning `n`. -/
@[norm_num OfNat.ofNat _] def evalOfNat : NormNumExt := withSemiring fun α e _ => do
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(ℕ) ← whnf n
    guard n.isNatLit
    have : Q(OfNat $α $n) := oα
    _ ← synthInstanceQ (q(LawfulOfNat $α $n) : Q(Prop))
    return .isNat n q(LawfulOfNat.isNat_ofNat (α := $α) (n := $n))

theorem isNat_add {α} [Semiring α] : {a b : α} → {a' b' c : Nat} →
    isNat a a' → isNat b b' → Nat.add a' b' = c → isNat (a + b) c
  | _, _, _, _, _, rfl, rfl, rfl => Nat.cast_add.symm

/-- The `norm_num` extension which identifies expressions of the form `a + b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ + _, Add.add _ _] def evalAdd : NormNumExt := withSemiring fun α e _i => do
  let arm (a b : Q($α)) : MetaM Result := do
    let (⟨na, pa⟩, ⟨nb, pb⟩) := (← deriveQ a, ← deriveQ b)
    have c : Q(Nat) := mkRawNatLit (na.natLit! + nb.natLit!)
    let r : Q(Nat.add «$na» «$nb» = «$c») := (q(Eq.refl $c) : Expr)
    return .isNat c q(isNat_add $pa $pb $r)
  match e with
  | ~q($a + $b) => arm a b
  | ~q(Add.add $a $b) => arm a b

theorem isNat_mul {α} [Semiring α] : {a b : α} → {a' b' c : Nat} →
    isNat a a' → isNat b b' → Nat.mul a' b' = c → isNat (a * b) c
  | _, _, _, _, _, rfl, rfl, rfl => Nat.cast_mul.symm

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ * _, Mul.mul _ _] def evalMul : NormNumExt := withSemiring fun α e _i => do
  let arm (a b : Q($α)) : MetaM Result := do
    let (⟨na, pa⟩, ⟨nb, pb⟩) := (← deriveQ a, ← deriveQ b)
    have c : Q(Nat) := mkRawNatLit (na.natLit! * nb.natLit!)
    let r : Q(Nat.mul «$na» «$nb» = «$c») := (q(Eq.refl $c) : Expr)
    return .isNat c q(isNat_mul $pa $pb $r)
  match e with
  | ~q($a * $b) => arm a b
  | ~q(Mul.mul $a $b) => arm a b

theorem isNat_pow {α} [Semiring α] : {a : α} → {b a' b' c : Nat} →
    isNat a a' → isNat b b' → Nat.pow a' b' = c → isNat (a ^ b) c
  | _, _, _, _, _, rfl, rfl, rfl => by simp [isNat]

def instSemiringNat : Semiring Nat := inferInstance

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : Nat), Pow.pow _ (_ : Nat)]
def evalPow : NormNumExt := withSemiring fun α e _i => do
  let arm (a : Q($α)) (b : Q(Nat)) : MetaM Result := do
    let (⟨na, pa⟩, ⟨nb, pb⟩) := (← deriveQ a, ← deriveQ b q(instSemiringNat))
    have c : Q(Nat) := mkRawNatLit (na.natLit! ^ nb.natLit!)
    let r : Q(Nat.pow «$na» «$nb» = «$c») := (q(Eq.refl $c) : Expr)
    return .isNat c q(isNat_pow $pa $pb $r)
  match e with
  | ~q($a ^ ($b : Nat)) => arm a b
  | ~q(Pow.pow $a ($b : Nat)) => arm a b

theorem isNat_cast {R} [Semiring R] (n m : Nat) :
    isNat n m → isNat (n : R) m := by
  rintro ⟨⟩; rfl

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
@[norm_num Nat.cast _] def evalNatCast : NormNumExt := withSemiring fun α e _i => do
  match e with
  | ~q(Nat.cast $a) =>
    let ⟨na, pa⟩ ← deriveQ a q(instSemiringNat)
    let pa : Q(isNat $a $na) := pa
    return .isNat na q(@isNat_cast $α _ $a $na $pa)
