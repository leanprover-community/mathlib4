/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Data.Int.Cast
import Mathlib.Algebra.GroupPower.Lemmas
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
partial def _root_.Lean.Expr.numeral? (e : Expr) : Option ℕ :=
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

theorem isNat_zero (α) [Semiring α] : IsNat (Zero.zero : α) (nat_lit 0) := ⟨Nat.cast_zero.symm⟩

/-- The `norm_num` extension which identifies the expression `Zero.zero`, returning `0`. -/
@[norm_num Zero.zero] def evalZero : NormNumExt where eval {u α} e := do
  let sα ← inferSemiring α
  match e with
  | ~q(Zero.zero) => return (.isNat sα (mkRawNatLit 0) q(isNat_zero $α) : Result q(Zero.zero))

theorem isNat_one (α) [Semiring α] : IsNat (One.one : α) (nat_lit 1) := ⟨Nat.cast_one.symm⟩

/-- The `norm_num` extension which identifies the expression `One.one`, returning `1`. -/
@[norm_num One.one] def evalOne : NormNumExt where eval {u α} e := do
  let sα ← inferSemiring α
  match e with
  | ~q(One.one) => return (.isNat sα (mkRawNatLit 1) q(isNat_one $α) : Result q(One.one))

theorem isNat_ofNat (α : Type u_1) [Semiring α] (n : ℕ) [OfNat α n]
  [LawfulOfNat α n] : IsNat (OfNat.ofNat n : α) n := ⟨LawfulOfNat.eq_ofNat.symm⟩

/-- The `norm_num` extension which identifies an expression `OfNat.ofNat n`, returning `n`. -/
@[norm_num OfNat.ofNat _] def evalOfNat : NormNumExt where eval {u α} e := do
  let sα ← inferSemiring α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(ℕ) ← whnf n
    guard n.isNatLit
    have : Q(OfNat $α $n) := oα
    _ ← synthInstanceQ (q(LawfulOfNat $α $n) : Q(Prop))
    return (.isNat sα n q(isNat_ofNat $α $n) : Result q((OfNat.ofNat $n : $α)))

theorem isNat_cast {R} [Semiring R] (n m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
@[norm_num Nat.cast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferSemiring α
  match e with
  | ~q(Nat.cast $a) =>
    let ⟨na, pa⟩ ← deriveNat a q(instSemiringNat)
    let pa : Q(IsNat $a $na) := pa
    return (.isNat sα na q(@isNat_cast $α _ $a $na $pa) : Result q((Nat.cast $a : $α)))

theorem isNat_int_cast {R} [Ring R] (n : ℤ) (m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_cast {R} [Ring R] (n m : ℤ) :
    IsInt n m → IsInt (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Int.cast n`, returning `n`. -/
@[norm_num Int.cast _] def evalIntCast : NormNumExt where eval {u α} e := do
  let rα ← inferRing α
  match e with
  | ~q(Int.cast $a) =>
    match ← derive (α := q(ℤ)) a with
    | .isNat _ na pa =>
      let sα : Q(Semiring $α) := q(Ring.toSemiring)
      let pa : Q(@IsNat _ Ring.toSemiring $a $na) := pa
      return (.isNat sα na q(@isNat_int_cast $α _ $a $na $pa) : Result q((Int.cast $a : $α)))
    | .isNegNat _ na pa =>
      let pa : Q(@IsInt _ instRingInt $a (.negOfNat $na)) := pa
      return (.isNegNat rα na q(isInt_cast $a (.negOfNat $na) $pa) : Result q((Int.cast $a : $α)))
    | _ => failure

theorem isNat_add {α} [Semiring α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Nat.cast_add.symm⟩

theorem isInt_add {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.add a' b' = c → IsInt (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

instance : MonadLift Option MetaM where
  monadLift
  | none => failure
  | some e => pure e

/-- The `norm_num` extension which identifies expressions of the form `a + b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ + _, Add.add _ _] def evalAdd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ ..
  | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. =>
    guard <|← withNewMCtxDepth <| isDefEq f q(HAdd.hAdd (α := $α))
  | _, _ => failure
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za + zb
      have c := mkRawIntLit zc
      let r : Q(Int.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα zc q(isInt_add $pa $pb $r) : Result q($a + $b))
    match ra, rb with
    | .isNat _ na pa, .isNat sα nb pb =>
      have pa : Q(IsNat $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
      let r : Q(Nat.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat sα c q(isNat_add $pa $pb $r) : Result q($a + $b))
    | .isNat _ .., .isNegNat rα ..
    | .isNegNat rα .., .isNat _ ..
    | .isNegNat _ .., .isNegNat rα .. => intArm rα
    | _, _ => failure
  core

theorem isInt_neg {α} [Ring α] : {a : α} → {a' b : ℤ} →
    IsInt a a' → Int.neg a' = b → IsInt (-a) b
  | _, _, _, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← withReducible (whnf e) | failure
  let rα ← inferRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(Neg.neg (α := $α))
  let ⟨za, na, pa⟩ ← (← derive a).toInt
  let zb := -za
  have b := mkRawIntLit zb
  let r : Q(Int.neg $na = $b) := (q(Eq.refl $b) : Expr)
  return (.isInt rα zb (z := b) q(isInt_neg $pa $r) : Result q(-$a))

theorem isInt_sub {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.sub a' b' = c → IsInt (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

/-- The `norm_num` extension which identifies expressions of the form `a - b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ - _, Sub.sub _ _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | failure
  let rα ← inferRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(HSub.hSub (α := $α))
  let ⟨za, na, pa⟩ ← (← derive a).toInt; let ⟨zb, nb, pb⟩ ← (← derive b).toInt
  let zc := za - zb
  have c := mkRawIntLit zc
  let r : Q(Int.sub $na $nb = $c) := (q(Eq.refl $c) : Expr)
  return (.isInt rα zc (z := c) q(isInt_sub $pa $pb $r) : Result q($a - $b))

theorem isNat_mul {α} [Semiring α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Nat.cast_mul.symm⟩

theorem isInt_mul {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.mul a' b' = c → IsInt (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ * _, Mul.mul _ _] def evalMul : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ ..
  | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. =>
    guard <|← withNewMCtxDepth <| isDefEq f q(HMul.hMul (α := $α))
  | _, _ => failure
  let rec
  /-- Main part of `evalMul`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za * zb
      have c := mkRawIntLit zc
      let r : Q(Int.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα zc q(isInt_mul $pa $pb $r) : Result q($a * $b))
    match ra, rb with
    | .isNat _ na pa, .isNat sα nb pb =>
      have pa : Q(IsNat $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! * nb.natLit!)
      let r : Q(Nat.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat sα c q(isNat_mul $pa $pb $r) : Result q($a * $b))
    | .isNat _ .., .isNegNat rα ..
    | .isNegNat rα .., .isNat _ ..
    | .isNegNat _ .., .isNegNat rα .. => intArm rα
    | _, _ => failure
  core

theorem isNat_pow {α} [Semiring α] : {a : α} → {b a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isInt_pow {α} [Ring α] : {a : α} → {b : ℕ} → {a' : ℤ} → {b' : ℕ} → {c : ℤ} →
    IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q(ℕ)) ← withReducible (whnf e) | failure
  let ⟨nb, pb⟩ ← deriveNat b q(instSemiringNat)
  let ra ← derive a
  match ra with
  | .isNat _ .. | .isNegNat _ .. =>
    guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  | _ => failure
  let rec
  /-- Main part of `evalPow`. -/
  core : Option (Result e) := do
    match ra with
    | .isNat sα na pa =>
      have c : Q(ℕ) := mkRawNatLit (na.natLit! ^ nb.natLit!)
      let r : Q(Nat.pow $na $nb = $c) := (q(Eq.refl $c) : Expr)
      let pb : Q(IsNat $b $nb) := pb
      return (.isNat sα c q(isNat_pow $pa $pb $r) : Result q($a ^ $b))
    | .isNegNat rα .. =>
      let ⟨za, na, pa⟩ ← ra.toInt
      let zc := za ^ nb.natLit!
      let c := mkRawIntLit zc
      let r : Q(Int.pow $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα zc (z := c) q(isInt_pow $pa $pb $r) : Result q($a ^ $b))
    | _ => failure
  core
