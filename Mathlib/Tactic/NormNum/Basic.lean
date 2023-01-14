/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Algebra.GroupPower.Lemmas
import Qq.Match

/-!
## `norm_num` basic plugins

This file adds `norm_num` plugins for `+`, `*` and `^` along with other basic operations.
-/

set_option warningAsError false -- FIXME: prove the sorries

namespace Mathlib
open Lean Meta

namespace Meta.NormNum
open Qq

theorem isNat_zero (α) [AddMonoidWithOne α] : IsNat (Zero.zero : α) (nat_lit 0) :=
  ⟨Nat.cast_zero.symm⟩

/-- The `norm_num` extension which identifies the expression `Zero.zero`, returning `0`. -/
@[norm_num Zero.zero] def evalZero : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Zero.zero) => return (.isNat sα (mkRawNatLit 0) q(isNat_zero $α) : Result q(Zero.zero))

theorem isNat_one (α) [AddMonoidWithOne α] : IsNat (One.one : α) (nat_lit 1) := ⟨Nat.cast_one.symm⟩

/-- The `norm_num` extension which identifies the expression `One.one`, returning `1`. -/
@[norm_num One.one] def evalOne : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return (.isNat sα (mkRawNatLit 1) q(isNat_one $α) : Result q(One.one))

theorem isNat_ofNat (α : Type u_1) [AddMonoidWithOne α] {a : α} {n : ℕ}
    (h : n = a) : IsNat a n := ⟨h.symm⟩

/-- The `norm_num` extension which identifies an expression `OfNat.ofNat n`, returning `n`. -/
@[norm_num OfNat.ofNat _] def evalOfNat : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(ℕ) ← whnf n
    guard n.isNatLit
    let ⟨a, (pa : Q($n = $e))⟩ ← mkOfNat α sα n
    guard <|← isDefEq a e
    return .isNat sα n (q(isNat_ofNat $α $pa) : Expr)

theorem isNat_cast {R} [AddMonoidWithOne R] (n m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
@[norm_num Nat.cast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Nat.cast $a) =>
    let ⟨na, pa⟩ ← deriveNat a q(instAddMonoidWithOneNat)
    let pa : Q(IsNat $a $na) := pa
    return (.isNat sα na q(@isNat_cast $α _ $a $na $pa) : Result q(Nat.cast $a : $α))

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
      let sα : Q(AddMonoidWithOne $α) := q(instAddMonoidWithOne)
      let pa : Q(@IsNat _ instAddMonoidWithOne $a $na) := pa
      return (.isNat sα na q(@isNat_int_cast $α _ $a $na $pa) : Result q(Int.cast $a : $α))
    | .isNegNat _ na pa =>
      let pa : Q(@IsInt _ instRingInt $a (.negOfNat $na)) := pa
      return (.isNegNat rα na q(isInt_cast $a (.negOfNat $na) $pa) : Result q(Int.cast $a : $α))
    | _ => failure

theorem isNat_add {α} [AddMonoidWithOne α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_add _ _).symm⟩

theorem isInt_add {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.add a' b' = c → IsInt (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

theorem isRat_add {α} [Ring α] : {a b : α} → {an bn cn : ℤ} → {ad bd cd g : ℕ} →
    IsRat a an ad → IsRat b bn bd →
    Int.add (Int.mul an bd) (Int.mul bn ad) = Int.mul (Nat.succ g) cn →
    Nat.mul ad bd = Nat.mul (Nat.succ g) cd →
    IsRat (a + b) cn cd
  | _, _, _, _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h₁, h₂ => sorry

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
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isRat _ ..
  | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. | .isNegNat _ .., .isRat _ ..
  | .isRat _ .., .isNat _ .. | .isRat _ .., .isNegNat _ .. | .isRat _ .., .isRat _ .. =>
    guard <|← withNewMCtxDepth <| isDefEq f q(HAdd.hAdd (α := $α))
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za + zb
      have c := mkRawIntLit zc
      let r : Q(Int.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc q(isInt_add $pa $pb $r) : Result q($a + $b))
    let ratArm (dα : Q(DivisionRing $α)) : Result _ :=
      let ⟨qa, na, da, pa⟩ := ra.toRat'; let ⟨qb, nb, db, pb⟩ := rb.toRat'
      let qc := qa + qb
      let dd := qa.den * qb.den
      let g := dd / qc.den - 1
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have g : Q(ℕ) := mkRawNatLit g
      let r1 : Q(Int.add (Int.mul $na $db) (Int.mul $nb $da) = Int.mul (Nat.succ $g) $nc) :=
        (q(Eq.refl (Int.mul (Nat.succ $g) $nc)) : Expr)
      have t2 : Q(ℕ) := mkRawNatLit dd
      let r2 : Q(Nat.mul $da $db = Nat.mul (Nat.succ $g) $dc) := (q(Eq.refl $t2) : Expr)
      (.isRat dα qc nc dc q(isRat_add $pa $pb $r1 $r2) : Result q($a + $b))
    match ra, rb with
    | .isNat _ na pa, .isNat sα nb pb =>
      have pa : Q(IsNat $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
      let r : Q(Nat.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat sα c q(isNat_add $pa $pb $r) : Result q($a + $b))
    | .isNat _ .., .isNegNat rα ..
    | .isNegNat rα .., .isNat _ ..
    | .isNegNat _ .., .isNegNat rα .. => intArm rα
    | _, .isRat dα .. | .isRat dα .., _ => some (ratArm dα)
  core

theorem isInt_neg {α} [Ring α] : {a : α} → {a' b : ℤ} →
    IsInt a a' → Int.neg a' = b → IsInt (-a) b
  | _, _, _, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

theorem isRat_neg {α} [Ring α] : {a : α} → {n n' : ℤ} → {d : ℕ} →
    IsRat a n d → Int.neg n = n' → IsRat (-a) n' d
  | _, _, _, _, ⟨_, rfl⟩, rfl => sorry

/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← withReducible (whnf e) | failure
  let ra ← derive a
  let rα ← inferRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(Neg.neg (α := $α))
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt
      let zb := -za
      have b := mkRawIntLit zb
      let r : Q(Int.neg $na = $b) := (q(Eq.refl $b) : Expr)
      return (.isInt rα b zb q(isInt_neg $pa $r) : Result q(-$a))
    let ratArm (dα : Q(DivisionRing $α)) : Result _ :=
      by clear rα; exact
      let ⟨qa, na, da, pa⟩ := ra.toRat'
      let qb := -qa
      have nb := mkRawIntLit qb.num
      let r : Q(Int.neg $na = $nb) := (q(Eq.refl $nb) : Expr)
      (.isRat' dα qb nb da q(isRat_neg $pa $r) : Result q(-$a))
    match ra with
    | .isNat _ .. => intArm rα
    | .isNegNat rα .. => intArm rα
    | .isRat dα .. => some (ratArm dα)
  core

theorem isInt_sub {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.sub a' b' = c → IsInt (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

theorem isRat_sub {α} [Ring α] : {a b : α} → {an bn cn : ℤ} → {ad bd cd g : ℕ} →
    IsRat a an ad → IsRat b bn bd →
    Int.sub (Int.mul an bd) (Int.mul bn ad) = Int.mul (Nat.succ g) cn →
    Nat.mul ad bd = Nat.mul (Nat.succ g) cd →
    IsRat (a - b) cn cd
  | _, _, _, _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h₁, h₂ => sorry

/-- The `norm_num` extension which identifies expressions of the form `a - b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ - _, Sub.sub _ _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | failure
  let ra ← derive a; let rb ← derive b
  let rα ← inferRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(HSub.hSub (α := $α))
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za - zb
      have c := mkRawIntLit zc
      let r : Q(Int.sub $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc q(isInt_sub $pa $pb $r) : Result q($a - $b))
    let ratArm (dα : Q(DivisionRing $α)) : (Result _) :=
      by clear rα; exact
      let ⟨qa, na, da, pa⟩ := ra.toRat'; let ⟨qb, nb, db, pb⟩ := rb.toRat'
      let qc := qa - qb
      let dd := qa.den * qb.den
      let gsucc := dd / qc.den
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have g : Q(ℕ) := mkRawNatLit (gsucc - 1)
      have t1 : Q(ℤ) := mkRawIntLit (gsucc * qc.num)
      have t2 : Q(ℕ) := mkRawNatLit dd
      let r1 : Q(Int.sub (Int.mul $na $db) (Int.mul $nb $da) = Int.mul (Nat.succ $g) $nc) :=
        (q(Eq.refl $t1) : Expr)
      let r2 : Q(Nat.mul $da $db = Nat.mul (Nat.succ $g) $dc) := (q(Eq.refl $t2) : Expr)
      (.isRat dα qc nc dc q(isRat_sub $pa $pb $r1 $r2) : Result q($a - $b))
    match ra, rb with
    | .isNat _ .., .isNat _ ..
    | .isNat _ .., .isNegNat rα ..
    | .isNegNat rα .., .isNat _ ..
    | .isNegNat _ .., .isNegNat rα .. => intArm rα
    | _, .isRat dα .. | .isRat dα .., _ => some (ratArm dα)
  core

theorem isNat_mul {α} [Semiring α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_mul ..).symm⟩

theorem isInt_mul {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.mul a' b' = c → IsInt (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩

theorem isRat_mul {α} [Ring α] : {a b : α} → {an bn cn : ℤ} → {ad bd cd g : ℕ} →
    IsRat a an ad → IsRat b bn bd →
    Int.mul an bn = Int.mul (Nat.succ g) cn →
    Nat.mul ad bd = Nat.mul (Nat.succ g) cd →
    IsRat (a * b) cn cd
  | _, _, _, _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h₁, h₂ => sorry

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ * _, Mul.mul _ _] def evalMul : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
  guard <|← withNewMCtxDepth <| isDefEq f q(HMul.hMul (α := $α))
  let rec
  /-- Main part of `evalMul`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za * zb
      have c := mkRawIntLit zc
      let r : Q(Int.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc (q(isInt_mul $pa $pb $r) : Expr) : Result q($a * $b))
    let ratArm (dα : Q(DivisionRing $α)) : Result _ :=
      let ⟨qa, na, da, pa⟩ := ra.toRat'; let ⟨qb, nb, db, pb⟩ := rb.toRat'
      let qc := qa * qb
      let dd := qa.den * qb.den
      let g := dd / qc.den - 1
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have g : Q(ℕ) := mkRawNatLit g
      let r1 : Q(Int.mul $na $nb = Int.mul (Nat.succ $g) $nc) :=
        (q(Eq.refl (Int.mul $na $nb)) : Expr)
      have t2 : Q(ℕ) := mkRawNatLit dd
      let r2 : Q(Nat.mul $da $db = Nat.mul (Nat.succ $g) $dc) := (q(Eq.refl $t2) : Expr)
      (.isRat dα qc nc dc q(isRat_mul $pa $pb $r1 $r2) : Result q($a * $b))
    match ra, rb with
    | .isNat _ na pa, .isNat mα nb pb =>
      let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
      let pb : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $b $nb) := pb
      have c : Q(ℕ) := mkRawNatLit (na.natLit! * nb.natLit!)
      let r : Q(Nat.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat mα c (q(isNat_mul (α := $α) $pa $pb $r) : Expr) : Result q($a * $b))
    | .isNat _ .., .isNegNat rα ..
    | .isNegNat rα .., .isNat _ ..
    | .isNegNat _ .., .isNegNat rα .. => intArm rα
    | _, .isRat dα .. | .isRat dα .., _ => some (ratArm dα)
  core

theorem isNat_pow {α} [Semiring α] : {a : α} → {b a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isInt_pow {α} [Ring α] : {a : α} → {b : ℕ} → {a' : ℤ} → {b' : ℕ} → {c : ℤ} →
    IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isRat_pow {α} [Ring α] : {a : α} → {an cn : ℤ} → {ad b b' cd : ℕ} →
    IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (a ^ b) cn cd
  | _, _, _, _, _, _, _, ⟨_, rfl⟩, ⟨rfl⟩, rfl, rfl => sorry

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q(ℕ)) ← withReducible (whnf e) | failure
  let ⟨nb, pb⟩ ← deriveNat b q(instAddMonoidWithOneNat)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  let rec
  /-- Main part of `evalPow`. -/
  core : Option (Result e) := do
    match ra with
    | .isNat sα na pa =>
      let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! ^ nb.natLit!)
      let r : Q(Nat.pow $na $nb = $c) := (q(Eq.refl $c) : Expr)
      let pb : Q(IsNat $b $nb) := pb
      return (.isNat sα c (q(isNat_pow $pa $pb $r) : Expr) : Result q($a ^ $b))
    | .isNegNat rα .. =>
      let ⟨za, na, pa⟩ ← ra.toInt
      let zc := za ^ nb.natLit!
      let c := mkRawIntLit zc
      let r : Q(Int.pow $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc (q(isInt_pow $pa $pb $r) : Expr) : Result q($a ^ $b))
    | .isRat dα qa na da pa =>
      let qc := qa ^ nb.natLit!
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have r1 : Q(Int.pow $na $nb = $nc) := (q(Eq.refl $nc) : Expr)
      have r2 : Q(Nat.pow $da $nb = $dc) := (q(Eq.refl $dc) : Expr)
      return (.isRat dα qc nc dc (q(isRat_pow $pa $pb $r1 $r2) : Expr) : Result q($a ^ $b))
  core

theorem isRat_inv_pos {α} [DivisionRing α] : {a : α} → {n d : ℕ} →
    Nat.ble (nat_lit 1) n = true → IsRat a (.ofNat n) d → IsRat a⁻¹ (.ofNat d) n
  | _, _, _, _, ⟨_, rfl⟩ => sorry

theorem isRat_inv_zero {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 0) → IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_neg {α} [DivisionRing α] : {a : α} → {n d : ℕ} →
    Nat.ble 1 n = true → IsRat a (.negOfNat n) d → IsRat a⁻¹ (.negOfNat d) n
  | _, _, _, _, ⟨_, rfl⟩ => sorry

/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← withReducible (whnf e) | failure
  let ra ← derive a
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  let ⟨qa, na, da, pa⟩ := ra.toRat'
  let qb := qa⁻¹
  if qa > 0 then
    have lit : Q(ℕ) := na.appArg!
    let pa : Q(IsRat «$a» (Int.ofNat $lit) $da) := pa
    let r : Q(Nat.ble (nat_lit 1) $lit = true) := (q(Eq.refl true) : Expr)
    return (.isRat' dα qb q(.ofNat $da) lit
      (q(isRat_inv_pos (α := $α) $r $pa) : Expr) : Result q($a⁻¹))
  else if qa < 0 then
    have lit : Q(ℕ) := na.appArg!
    let pa : Q(IsRat «$a» (Int.negOfNat $lit) $da) := pa
    let r : Q(Nat.ble (nat_lit 1) $lit = true) := (q(Eq.refl true) : Expr)
    return (.isRat' dα qb q(.negOfNat $da) lit
      (q(isRat_inv_neg (α := $α) $r $pa) : Expr) : Result q($a⁻¹))
  else
    let .isNat inst _z (pa : Q(@IsNat _ AddGroupWithOne.toAddMonoidWithOne $a (nat_lit 0))) := ra
      | failure
    return (.isNat inst _z (q(isRat_inv_zero $pa) : Expr) : Result q($a⁻¹))

theorem isRat_div {α} [DivisionRing α] : {a b : α} → {cn : ℤ} → {cd : ℕ} → IsRat (a * b⁻¹) cn cd →
    IsRat (a / b) cn cd
  | _, _, _, _, h => by simp [div_eq_mul_inv]; exact h

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ / _, Div.div _ _] def evalDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | failure
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  let ⟨qa, na, da, pa⟩ := rab.toRat'
  let pa : Q(IsRat ($a * $b⁻¹) $na $da) := pa
  return (.isRat' dα qa na da q(isRat_div $pa) : Result q($a / $b))

attribute [nolint defLemma] isRat_add isRat_neg isRat_sub isRat_mul isRat_pow isRat_inv_pos
  isRat_inv_neg isRat_div -- FIXME: figure out how to get the linter to work with these
