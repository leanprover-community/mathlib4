/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Order.Invertible
import Mathlib.Util.Qq

/-!
## `norm_num` basic plugins

This file adds `norm_num` plugins for `+`, `*` and `^` along with other basic operations.
-/

namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq

/-! # Constructors and constants -/

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

theorem isNat_intOfNat : {n n' : ℕ} → IsNat n n' → IsNat (Int.ofNat n) n'
  | _, _, ⟨rfl⟩ => ⟨rfl⟩

/-- The `norm_num` extension which identifies the constructor application `Int.ofNat n` such that
`norm_num` successfully recognizes `n`, returning `n`. -/
@[norm_num Int.ofNat _] def evalIntOfNat : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.ofNat _) (n : Q(ℕ)) ← whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let sℤ : Q(AddMonoidWithOne ℤ) := q(AddGroupWithOne.toAddMonoidWithOne)
  let ⟨n', p⟩ ← deriveNat n sℕ
  return (.isNat sℤ n' q(isNat_intOfNat $p) : Result q(Int.ofNat $n))

/-! # Casts -/

theorem isNat_cast {R} [AddMonoidWithOne R] (n m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
@[norm_num Nat.cast _, NatCast.natCast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  let .app n (a : Q(ℕ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq n q(Nat.cast (R := $α))
  let ⟨na, pa⟩ ← deriveNat a q(instAddMonoidWithOneNat)
  let pa : Q(IsNat $a $na) := pa
  return (.isNat sα na q(@isNat_cast $α _ $a $na $pa) : Result q(Nat.cast (R := $α) $a))

theorem isNat_int_cast {R} [Ring R] (n : ℤ) (m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_cast {R} [Ring R] (n m : ℤ) :
    IsInt n m → IsInt (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Int.cast n`, returning `n`. -/
@[norm_num Int.cast _, IntCast.intCast _] def evalIntCast : NormNumExt where eval {u α} e := do
  let rα ← inferRing α
  let .app i (a : Q(ℤ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq i q(Int.cast (R := $α))
  match ← derive (α := q(ℤ)) a with
  | .isNat _ na pa =>
    let sα : Q(AddMonoidWithOne $α) := q(instAddMonoidWithOne)
    let pa : Q(@IsNat _ instAddMonoidWithOne $a $na) := pa
    return (.isNat sα na q(@isNat_int_cast $α _ $a $na $pa) : Result q(Int.cast (R := $α) $a))
  | .isNegNat _ na pa =>
    let pa : Q(@IsInt _ instRingInt $a (.negOfNat $na)) := pa
    return (.isNegNat rα na q(isInt_cast $a (.negOfNat $na) $pa) : Result q(Int.cast (R := $α) $a))
  | _ => failure

theorem isNat_ratCast [DivisionRing R] : {q : ℚ} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isInt_ratCast [DivisionRing R] : {q : ℚ} → {n : ℤ} →
    IsInt q n → IsInt (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_ratCast [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℤ} → {d : ℕ} →
    IsRat q n d → IsRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only []; norm_cast⟩

/-- The `norm_num` extension which identifies an expression `RatCast.ratCast q` where `norm_num`
recognizes `q`, returning the cast of `q`. -/
@[norm_num Rat.cast _, RatCast.ratCast _] def evalRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionRing α
  let .app r (a : Q(ℚ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq r q(Rat.cast (K := $α))
  let r ← derive (α := q(ℚ)) a
  match r with
  | .isNat _ na pa =>
    let sα : Q(AddMonoidWithOne $α) := q(instAddMonoidWithOne')
    let pa : Q(@IsNat _ instAddMonoidWithOne' $a $na) := pa
    return (.isNat sα na q(@isNat_ratCast $α _ $a $na $pa) : Result q(Rat.cast (K := $α) $a))
  | .isNegNat _ na pa =>
    let rα : Q(Ring $α) := q(instRing)
    let pa : Q(@IsInt _ instRing $a (.negOfNat $na)) := pa
    return (.isNegNat rα na q(@isInt_ratCast $α _ $a (.negOfNat $na) $pa) :
        Result q(RatCast.ratCast (K := $α) $a))
  | .isRat _ qa na da pa =>
    let i ← inferCharZeroOfDivisionRing dα
    let pa : Q(@IsRat _ instRingRat $a $na $da) := pa
    return (.isRat dα qa na da q(isRat_ratCast $pa) : Result q(Rat.cast (K := $α) $a))
  | _ => failure

/-! # Arithmetic -/

theorem isNat_add {α} [AddMonoidWithOne α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_add _ _).symm⟩

theorem isInt_add {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.add a' b' = c → IsInt (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
def invertibleOfMul {α} [Semiring α] (k : ℕ) (b : α) :
    ∀ (a : α) [Invertible a], a = k * b → Invertible b
  | _, ⟨c, hc1, hc2⟩, rfl => by
    rw [← mul_assoc] at hc1
    rw [Nat.cast_commute k, mul_assoc, Nat.cast_commute k] at hc2
    exact ⟨_, hc1, hc2⟩

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
def invertibleOfMul' {α} [Semiring α] {a k b : ℕ} [Invertible (a : α)]
    (h : a = k * b) : Invertible (b : α) := invertibleOfMul k (b:α) ↑a (by simp [h])

-- TODO: clean up and move it somewhere in mathlib? It's a bit much for this file
theorem isRat_add {α} [Ring α] {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    IsRat a na da → IsRat b nb db →
    Int.add (Int.mul na db) (Int.mul nb da) = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (a + b) nc dc := by
  rintro ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (↑· * (⅟↑da * ⅟↑db : α)) h₁
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, ← mul_assoc,
    add_mul, mul_mul_invOf_self_cancel] at h₁
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp [← mul_assoc, H] at h₁ h₂; rw [h₁, h₂, Nat.cast_commute]
  simp only [mul_mul_invOf_self_cancel,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

instance : MonadLift Option MetaM where
  monadLift
  | none => failure
  | some e => pure e

/-- The `norm_num` extension which identifies expressions of the form `a + b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ + _, Add.add _ _] def evalAdd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
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
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      let qc := qa + qb
      let dd := qa.den * qb.den
      let k := dd / qc.den
      have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
      have t2 : Q(ℕ) := mkRawNatLit dd
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have k : Q(ℕ) := mkRawNatLit k
      let r1 : Q(Int.add (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
        (q(Eq.refl $t1) : Expr)
      let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
      return (.isRat' dα qc nc dc q(isRat_add $pa $pb $r1 $r2) : Result q($a + $b))
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
    | .isNat _ na pa, .isNat sα nb pb =>
      have pa : Q(IsNat $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
      let r : Q(Nat.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat sα c q(isNat_add $pa $pb $r) : Result q($a + $b))
  core

theorem isInt_neg {α} [Ring α] : {a : α} → {a' b : ℤ} →
    IsInt a a' → Int.neg a' = b → IsInt (-a) b
  | _, _, _, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

theorem isRat_neg {α} [Ring α] : {a : α} → {n n' : ℤ} → {d : ℕ} →
    IsRat a n d → Int.neg n = n' → IsRat (-a) n' d
  | _, _, _, _, ⟨h, rfl⟩, rfl => ⟨h, by rw [← neg_mul, ← Int.cast_neg]; rfl⟩

/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← whnfR e | failure
  have _e_eq : $e =Q $f $a := ⟨⟩
  let ra ← derive a
  let rα ← inferRing α
  let ⟨(_f_eq : $f =Q Neg.neg)⟩ ← withNewMCtxDepth <| assertDefEqQ _ _
  let rec
  /-- Main part of `evalNeg`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt
      let zb := -za
      have b := mkRawIntLit zb
      let r : Q(Int.neg $na = $b) := (q(Eq.refl $b) : Expr)
      return (.isInt rα b zb q(isInt_neg $pa $r) : Result q(-$a))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      assumeInstancesCommute
      let ⟨qa, na, da, pa⟩ ← ra.toRat'
      let qb := -qa
      have nb := mkRawIntLit qb.num
      let r : Q(Int.neg $na = $nb) := (q(Eq.refl $nb) : Expr)
      return (.isRat' dα qb nb da q(isRat_neg $pa $r) : Result q(-$a))
    match ra with
    | .isBool _ .. => failure
    | .isNat _ .. => intArm rα
    | .isNegNat rα .. => intArm rα
    | .isRat dα .. => ratArm dα
  core

theorem isInt_sub {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.sub a' b' = c → IsInt (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

theorem isRat_sub {α} [Ring α] {a b : α} {na nb nc : ℤ} {da db dc k : ℕ}
    (ra : IsRat a na da) (rb : IsRat b nb db)
    (h₁ : Int.sub (Int.mul na db) (Int.mul nb da) = Int.mul k nc)
    (h₂ : Nat.mul da db = Nat.mul k dc) :
    IsRat (a - b) nc dc := by
  rw [sub_eq_add_neg]
  refine isRat_add ra (isRat_neg (n' := -nb) rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

/-- The `norm_num` extension which identifies expressions of the form `a - b` in a ring,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ - _, Sub.sub _ _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  have _e_eq : $e =Q $f $a $b := ⟨⟩
  let rα ← inferRing α
  let ⟨(_f_eq : $f =Q HSub.hSub)⟩ ← withNewMCtxDepth <| assertDefEqQ _ _
  let ra ← derive a; let rb ← derive b
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za - zb
      have c := mkRawIntLit zc
      let r : Q(Int.sub $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc q(isInt_sub $pa $pb $r) : Result q($a - $b))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      assumeInstancesCommute
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      let qc := qa - qb
      let dd := qa.den * qb.den
      let k := dd / qc.den
      have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
      have t2 : Q(ℕ) := mkRawNatLit dd
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have k : Q(ℕ) := mkRawNatLit k
      let r1 : Q(Int.sub (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
        (q(Eq.refl $t1) : Expr)
      let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
      return (.isRat' dα qc nc dc q(isRat_sub $pa $pb $r1 $r2) : Result q($a - $b))
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα ..
    | .isNat _ .., .isNat _ .. => intArm rα
  core

theorem isNat_mul {α} [Semiring α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_mul ..).symm⟩

theorem isInt_mul {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.mul a' b' = c → IsInt (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩

theorem isRat_mul {α} [Ring α] {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    IsRat a na da → IsRat b nb db →
    Int.mul na nb = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (a * b) nc dc := by
  rintro ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (Int.cast (R := α)) h₁
  simp only [Int.cast_mul, Int.cast_ofNat] at h₁
  simp [← mul_assoc, (Nat.cast_commute (α := α) da nb).invOf_left.right_comm, h₁]
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp [← mul_assoc] at h₂; rw [H] at h₂
  simp [mul_mul_invOf_self_cancel] at h₂; rw [h₂, Nat.cast_commute]
  simp only [mul_mul_invOf_self_cancel,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ * _, Mul.mul _ _] def evalMul : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
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
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      let qc := qa * qb
      let dd := qa.den * qb.den
      let k := dd / qc.den
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have k : Q(ℕ) := mkRawNatLit k
      let r1 : Q(Int.mul $na $nb = Int.mul $k $nc) :=
        (q(Eq.refl (Int.mul $na $nb)) : Expr)
      have t2 : Q(ℕ) := mkRawNatLit dd
      let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
      return (.isRat' dα qc nc dc q(isRat_mul $pa $pb $r1 $r2) : Result q($a * $b))
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
    | .isNat _ na pa, .isNat mα nb pb =>
      let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
      let pb : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $b $nb) := pb
      have c : Q(ℕ) := mkRawNatLit (na.natLit! * nb.natLit!)
      let r : Q(Nat.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat mα c (q(isNat_mul (α := $α) $pa $pb $r) : Expr) : Result q($a * $b))
  core

theorem isNat_pow {α} [Semiring α] : {a : α} → {b a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isInt_pow {α} [Ring α] : {a : α} → {b : ℕ} → {a' : ℤ} → {b' : ℕ} → {c : ℤ} →
    IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isRat_pow {α} [Ring α] {a : α} {an cn : ℤ} {ad b b' cd : ℕ} :
    IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (a ^ b) cn cd := by
  rintro ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(instAddMonoidWithOneNat)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  let rec
  /-- Main part of `evalPow`. -/
  core : Option (Result e) := do
    match ra with
    | .isBool .. => failure
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
      return (.isRat' dα qc nc dc (q(isRat_pow $pa $pb $r1 $r2) : Expr) : Result q($a ^ $b))
  core

theorem isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.ofNat (Nat.succ n)) d → IsRat a⁻¹ (.ofNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  refine ⟨this, by simp⟩

theorem isRat_inv_one {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 1) → IsNat a⁻¹ (nat_lit 1)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_zero {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 0) → IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_neg_one {α} [DivisionRing α] : {a : α} →
    IsInt a (.negOfNat (nat_lit 1)) → IsInt a⁻¹ (.negOfNat (nat_lit 1))
  | _, ⟨rfl⟩ => ⟨by simp [inv_neg_one]⟩

theorem isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.negOfNat (Nat.succ n)) d → IsRat a⁻¹ (.negOfNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_coe, Int.cast_neg,
    Int.cast_ofNat, invOf_eq_inv, inv_neg,  neg_mul, mul_inv_rev, inv_inv]

/-- The `norm_num` extension which identifies expressions of the form `a⁻¹`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dα ← inferDivisionRing α
  let _i ← inferCharZeroOfDivisionRing? dα
  guard <|← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  let rec
  /-- Main part of `evalInv`. -/
  core : Option (Result e) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat'
    let qb := qa⁻¹
    if qa > 0 then
      if let some _i := _i then
        have lit : Q(ℕ) := na.appArg!
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        let pa : Q(IsRat $a (Int.ofNat (Nat.succ $lit2)) $da) := pa
        return (.isRat' dα qb q(.ofNat $da) lit
          (q(isRat_inv_pos (α := $α) $pa) : Expr) : Result q($a⁻¹))
      else
        guard (qa = 1)
        let .isNat inst n
          (pa : Q(@IsNat _ AddGroupWithOne.toAddMonoidWithOne $a (nat_lit 1))) := ra | failure
        return (.isNat inst n (q(isRat_inv_one $pa) : Expr) : Result q($a⁻¹))
    else if qa < 0 then
      if let some _i := _i then
        have lit : Q(ℕ) := na.appArg!
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        let pa : Q(IsRat $a (Int.negOfNat (Nat.succ $lit2)) $da) := pa
        return (.isRat' dα qb q(.negOfNat $da) lit
          (q(isRat_inv_neg (α := $α) $pa) : Expr) : Result q($a⁻¹))
      else
        guard (qa = -1)
        let .isNegNat inst n
          (pa : Q(@IsInt _ DivisionRing.toRing $a (.negOfNat 1))) := ra | failure
        return (.isNegNat inst n (q(isRat_inv_neg_one $pa) : Expr) : Result q($a⁻¹))
    else
      let .isNat inst n (pa : Q(@IsNat _ AddGroupWithOne.toAddMonoidWithOne $a (nat_lit 0))) := ra
        | failure
      return (.isNat inst n (q(isRat_inv_zero $pa) : Expr) : Result q($a⁻¹))
  core

theorem isRat_div [DivisionRing α] : {a b : α} → {cn : ℤ} → {cd : ℕ} → IsRat (a * b⁻¹) cn cd →
    IsRat (a / b) cn cd
  | _, _, _, _, h => by simp [div_eq_mul_inv]; exact h

/-- The `norm_num` extension which identifies expressions of the form `a / b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ / _, Div.div _ _] def evalDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  let ⟨qa, na, da, pa⟩ ← rab.toRat'
  let pa : Q(IsRat ($a * $b⁻¹) $na $da) := pa
  return (.isRat' dα qa na da q(isRat_div $pa) : Result q($a / $b))

/-! # Constructor-like operations -/

theorem isRat_mkRat : {a na n : ℤ} → {b nb d : ℕ} → IsInt a na → IsNat b nb →
    IsRat (na / nb : ℚ) n d → IsRat (mkRat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [Rat.mkRat_eq_div]; exact ⟨_, h⟩

/-- The `norm_num` extension which identifies expressions of the form `mkRat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num mkRat _ _] def evalMkRat : NormNumExt where eval {u α} e := do
  let .app (.app (.const ``mkRat _) (a : Q(ℤ))) (b : Q(ℕ)) ← whnfR e | failure
  let ra ← derive a
  let rℤ : Q(Ring ℤ) := q(Int.instRingInt)
  let some ⟨_, na, pa⟩ := ra.toInt | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let ⟨nb, pb⟩ ← deriveNat b sℕ
  let rab ← derive (q($na / $nb) : Q(Rat))
  let dℚ : Q(DivisionRing ℚ) := q(Rat.divisionRing)
  let ⟨q, n, d, p⟩ ← rab.toRat' dℚ
  let p : Q(IsRat ($na / $nb : ℚ) $n $d) := p
  return (.isRat' (inst := dℚ) q n d q(isRat_mkRat $pa $pb $p) : Result q(mkRat $a $b))

/- Note: the following lemmas take an explicit `OfScientific α` argument to prevent a
`(kernel) deep recursion detected` error arising from `Nat.gcd` (see lean4#2171). When we use these
lemmas in `evalOfScientific`, we always take `σα` to be the `OfScientific α` instance obtained from
the `DivisionRing` structure even though this isn't enforced by the type. -/

theorem isRat_ofScientific_of_true [DivisionRing α] (σα : OfScientific α) :
    {m e : ℕ} → {n : ℤ} → {d : ℕ} →
    @OfScientific.ofScientific α σα = (fun m s e ↦ (Rat.ofScientific m s e : α)) →
    IsRat (mkRat m (10 ^ e) : α) n d → IsRat (@OfScientific.ofScientific α σα m true e) n d
  | _, _, _, _, σh, ⟨_, eq⟩ => ⟨_, by simp only [σh, Rat.ofScientific_true_def]; exact eq⟩

theorem isNat_ofScientific_of_false [DivisionRing α] (σα : OfScientific α) : {m e nm ne n : ℕ} →
    @OfScientific.ofScientific α σα = (fun m s e ↦ (Rat.ofScientific m s e : α)) →
    IsNat m nm → IsNat e ne → n = Nat.mul nm ((10 : ℕ) ^ ne) →
    IsNat (@OfScientific.ofScientific α σα m false e : α) n
  | _, _, _, _, _, σh, ⟨rfl⟩, ⟨rfl⟩, h => ⟨by simp [σh, Rat.ofScientific_false_def, h]; norm_cast⟩

/-- The `norm_num` extension which identifies expressions in scientific notation, normalizing them
to rat casts if the scientific notation is inherited from the one for rationals. -/
@[norm_num OfScientific.ofScientific _ _ _] def evalOfScientific :
    NormNumExt where eval {u α} e := do
  let .app (.app (.app f (m : Q(ℕ))) (b : Q(Bool))) (exp : Q(ℕ)) ← whnfR e | failure
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(OfScientific.ofScientific (α := $α))
  let σα ← inferOfScientific α
  assumeInstancesCommute
  have lh : Q(@OfScientific.ofScientific $α $σα = (fun m s e ↦ (Rat.ofScientific m s e : $α))) :=
    (q(Eq.refl (fun m s e ↦ (Rat.ofScientific m s e : $α))) : Expr)
  match b with
  | ~q(true)  =>
    let rme ← derive (q(mkRat $m (10 ^ $exp)) : Q($α))
    let some ⟨q, n, d, p⟩ := rme.toRat' | failure
    let p : Q(IsRat (mkRat $m (10 ^ $exp) : $α) $n $d) := p
    return (.isRat' dα q n d q(isRat_ofScientific_of_true $σα $lh $p) :
        Result q(@OfScientific.ofScientific $α $σα $m true $exp))
  | ~q(false) =>
    let ⟨nm, pm⟩ ← deriveNat m q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨ne, pe⟩ ← deriveNat exp q(AddCommMonoidWithOne.toAddMonoidWithOne)
    have pm : Q(IsNat $m $nm) := pm
    have pe : Q(IsNat $exp $ne) := pe
    let m' := nm.natLit!
    let exp' := ne.natLit!
    let n' := Nat.mul m' (Nat.pow (10 : ℕ) exp')
    have n : Q(ℕ) := mkRawNatLit n'
    have r : Q($n = Nat.mul $nm ((10 : ℕ) ^ $ne)) := (q(Eq.refl $n) : Expr)
    return ((.isNat _ n
      (q(isNat_ofScientific_of_false $σα $lh $pm $pe $r) :
          Q(IsNat (@OfScientific.ofScientific $α $σα $m false $exp) $n))) :
        Result q(@OfScientific.ofScientific $α $σα $m false $exp))

/-! # Logic -/

/-- The `norm_num` extension which identifies `True`. -/
@[norm_num True] def evalTrue : NormNumExt where eval {u α} e :=
  return (.isTrue q(True.intro) : Result q(True))

/-- The `norm_num` extension which identifies `False`. -/
@[norm_num False] def evalFalse : NormNumExt where eval {u α} e :=
  return (.isFalse q(not_false) : Result q(False))

/-- The `norm_num` extension which identifies expressions of the form `¬a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num ¬_] def evalNot : NormNumExt where eval {u α} e := do
  let .app (.const ``Not _) (a : Q($α)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq α q(Prop)
  let .isBool b p ← derive a | failure
  have a : Q(Prop) := a
  if b then
    have p : Q($a) := p
    return (.isFalse q(not_not_intro $p) : Result q(¬$a))
  else
    return (.isTrue p : Result q(¬$a))

/-! # (In)equalities -/

theorem isNat_eq_true [AddMonoidWithOne α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.beq a' b' = true → a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => congr_arg Nat.cast <| Nat.eq_of_beq_eq_true h

theorem isNat_le_true [OrderedSemiring α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble a' b' = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.mono_cast (Nat.le_of_ble_eq_true h)

theorem ble_eq_false {x y : ℕ} : x.ble y = false ↔ y < x := by
  rw [← Nat.not_le, ← Bool.not_eq_true, Nat.ble_eq]

theorem isNat_lt_true [OrderedSemiring α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble b' a' = false → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h =>
    Nat.cast_lt.2 <| ble_eq_false.1 h

theorem isNat_eq_false [AddMonoidWithOne α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.beq a' b' = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simp; exact Nat.ne_of_beq_eq_false h

theorem isNat_le_false [OrderedSemiring α] [CharZero α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b' = false) : ¬a ≤ b :=
  not_le_of_lt (isNat_lt_true hb ha h)

theorem isNat_lt_false [OrderedSemiring α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a < b :=
  not_lt_of_le (isNat_le_true hb ha h)

theorem isInt_eq_true [Ring α] : {a b : α} → {z : ℤ} → IsInt a z → IsInt b z → a = b
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => rfl

theorem isInt_le_true [OrderedRing α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' ≤ b') → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_mono <| of_decide_eq_true h

theorem isInt_lt_true [OrderedRing α] [Nontrivial α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' < b') → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 <| of_decide_eq_true h

theorem isInt_eq_false [Ring α] [CharZero α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' = b') = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simp; exact of_decide_eq_false h

theorem isInt_le_false [OrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a')) : ¬a ≤ b :=
  not_le_of_lt (isInt_lt_true hb ha h)

theorem isInt_lt_false [OrderedRing α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' ≤ a')) : ¬a < b :=
  not_lt_of_le (isInt_le_true hb ha h)

theorem Rat.invOf_denom_swap [Ring α] (n₁ n₂ : ℤ) (a₁ a₂ : α)
    [Invertible a₁] [Invertible a₂] : n₁ * ⅟a₁ = n₂ * ⅟a₂ ↔ n₁ * a₂ = n₂ * a₁ := by
  rw [mul_invOf_eq_iff_eq_mul_right, ← Int.commute_cast, mul_assoc,
    ← mul_left_eq_iff_eq_invOf_mul, Int.commute_cast]

theorem isRat_eq_true [Ring α] : {a b : α} → {n : ℤ} → {d : ℕ} →
    IsRat a n d → IsRat b n d → a = b
  | _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by congr; apply Subsingleton.elim

theorem isRat_le_true [LinearOrderedRing α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) ≤ Int.mul nb (.ofNat da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_mono (α := α) <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp at h; rwa [Int.commute_cast] at h

theorem isRat_lt_true [LinearOrderedRing α] [Nontrivial α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_strictMono (α := α) <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp at h
    rwa [Int.commute_cast] at h

theorem isRat_eq_false [Ring α] [CharZero α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) = Int.mul nb (.ofNat da)) = false → ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    rw [Rat.invOf_denom_swap]; exact_mod_cast of_decide_eq_false h

theorem isRat_le_false [LinearOrderedRing α] [Nontrivial α] {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_lt (isRat_lt_true hb ha h)

theorem isRat_lt_false [LinearOrderedRing α] {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_le (isRat_le_true hb ha h)

theorem eq_of_true {a b : Prop} (ha : a) (hb : b) : a = b := propext (iff_of_true ha hb)
theorem ne_of_false_of_true (ha : ¬a) (hb : b) : a ≠ b := mt (· ▸ hb) ha
theorem ne_of_true_of_false (ha : a) (hb : ¬b) : a ≠ b := mt (· ▸ ha) hb
theorem eq_of_false (ha : ¬a) (hb : ¬b) : a = b := propext (iff_of_false ha hb)

/-- The `norm_num` extension which identifies expressions of the form `a = b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ = _, Eq _ _] def evalEq : NormNumExt where eval {u α} e := do
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  guard <|← withNewMCtxDepth <| isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let intArm (rα : Q(Ring $α)) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
    if za = zb then
      let pb : Q(IsInt $b $na) := pb
      return (.isTrue q(isInt_eq_true $pa $pb) : Result q($a = $b))
    else if let some _i ← inferCharZeroOfRing? rα then
      let r : Q(decide ($na = $nb) = false) := (q(Eq.refl false) : Expr)
      return (.isFalse q(isInt_eq_false $pa $pb $r) : Result q($a = $b))
    else
      failure --TODO: nonzero characteristic ≠
  let ratArm (dα : Q(DivisionRing $α)) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
    if qa = qb then
      let pb : Q(IsRat $b $na $da) := pb
      return (.isTrue q(isRat_eq_true $pa $pb) : Result q($a = $b))
    else if let some _i ← inferCharZeroOfDivisionRing? dα then
      let r : Q(decide (Int.mul $na (.ofNat $db) = Int.mul $nb (.ofNat $da)) = false) :=
        (q(Eq.refl false) : Expr)
      return (.isFalse q(isRat_eq_false $pa $pb $r) : Result q($a = $b))
    else
      failure --TODO: nonzero characteristic ≠
  match ra, rb with
  | .isBool b₁ p₁, .isBool b₂ p₂ =>
    have a : Q(Prop) := a; have b : Q(Prop) := b
    match b₁, p₁, b₂, p₂ with
    | true, (p₁ : Q($a)), true, (p₂ : Q($b)) =>
      return (.isTrue q(eq_of_true $p₁ $p₂) : Result q($a = $b))
    | false, (p₁ : Q(¬$a)), false, (p₂ : Q(¬$b)) =>
      return (.isTrue q(eq_of_false $p₁ $p₂) : Result q($a = $b))
    | false, (p₁ : Q(¬$a)), true, (p₂ : Q($b)) =>
      return (.isFalse q(ne_of_false_of_true $p₁ $p₂) : Result q($a = $b))
    | true, (p₁ : Q($a)), false, (p₂ : Q(¬$b)) =>
      return (.isFalse q(ne_of_true_of_false $p₁ $p₂) : Result q($a = $b))
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat _ na pa, .isNat mα nb pb =>
    let pa : Q(IsNat $a $na) := pa
    if na.natLit!.beq nb.natLit! then
      let r : Q(Nat.beq $na $nb = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isNat_eq_true $pa $pb $r) : Result q($a = $b))
    else if let some _i ← inferCharZeroOfAddMonoidWithOne? mα then
      let r : Q(Nat.beq $na $nb = false) := (q(Eq.refl false) : Expr)
      return (.isFalse q(isNat_eq_false $pa $pb $r) : Result q($a = $b))
    else
      failure --TODO: nonzero characteristic ≠

/-- The `norm_num` extension which identifies expressions of the form `a ≤ b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ ≤ _] def evalLE : NormNumExt where eval (e : Q(Prop)) := do
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
    let intArm (_ : Unit) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    let _i ← inferOrderedRing α
    guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
    let ⟨za, na, pa⟩ ← ra.toInt q(OrderedRing.toRing)
    let ⟨zb, nb, pb⟩ ← rb.toInt q(OrderedRing.toRing)
    let pa : Q(@IsInt _ OrderedRing.toRing $a $na) := pa
    let pb : Q(@IsInt _ OrderedRing.toRing $b $nb) := pb
    if decide (za ≤ zb) then
      let r : Q(decide ($na ≤ $nb) = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isInt_le_true $pa $pb $r) : Result q($a ≤ $b))
    else if let .some _i ← trySynthInstanceQ (q(@Nontrivial $α) : Q(Prop)) then
      let r : Q(decide ($nb < $na) = true) := (q(Eq.refl true) : Expr)
      return (.isFalse q(isInt_le_false $pa $pb $r) : Result q($a ≤ $b))
    else
      failure
  let ratArm (_ : Unit) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    -- We need a division ring with an order, and `LinearOrderedField` is the closest mathlib has.
    let _i ← inferLinearOrderedField α
    guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    let pa : Q(@IsRat _ StrictOrderedRing.toRing $a $na $da) := pa
    let pb : Q(@IsRat _ StrictOrderedRing.toRing $b $nb $db) := pb
    if decide (qa ≤ qb) then
      let r : Q(decide ($na * $db ≤ $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isRat_le_true $pa $pb $r) : Result q($a ≤ $b))
    else
      let _i : Q(Nontrivial $α) := q(StrictOrderedRing.toNontrivial)
      let r : Q(decide ($nb * $da < $na * $db) = true) := (q(Eq.refl true) : Expr)
      return (.isFalse q(isRat_le_false $pa $pb $r) : Result q($a ≤ $b))
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat _ .., _ | _, .isRat _ .. => ratArm ()
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm ()
  | .isNat _ na pa, .isNat _ nb pb =>
    let _i ← inferOrderedSemiring α
    guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
    let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
    let pb : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $b $nb) := pb
    if na.natLit! ≤ nb.natLit! then
      let r : Q(Nat.ble $na $nb = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isNat_le_true $pa $pb $r) : Result q($a ≤ $b))
    else if let .some _i ←
        trySynthInstanceQ (q(@CharZero $α AddCommMonoidWithOne.toAddMonoidWithOne) : Q(Prop)) then
      let r : Q(Nat.ble $na $nb = false) := (q(Eq.refl false) : Expr)
      return (.isFalse q(isNat_le_false $pa $pb $r) : Result q($a ≤ $b))
    else -- Nats can appear in an `OrderedRing` without `CharZero`.
      intArm ()

/-- The `norm_num` extension which identifies expressions of the form `a < b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ < _] def evalLT : NormNumExt where eval (e : Q(Prop)) := do
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let intArm (_ : Unit) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    let _i ← inferOrderedRing α
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    let ⟨za, na, pa⟩ ← ra.toInt q(OrderedRing.toRing)
    let ⟨zb, nb, pb⟩ ← rb.toInt q(OrderedRing.toRing)
    let pa : Q(@IsInt _ OrderedRing.toRing $a $na) := pa
    let pb : Q(@IsInt _ OrderedRing.toRing $b $nb) := pb
    if za < zb then
      if let .some _i ← trySynthInstanceQ (q(@Nontrivial $α) : Q(Prop)) then
        let r : Q(decide ($na < $nb) = true) := (q(Eq.refl true) : Expr)
        return (.isTrue q(isInt_lt_true $pa $pb $r) : Result q($a < $b))
      else
        failure
    else
      let r : Q(decide ($nb ≤ $na) = true) := (q(Eq.refl true) : Expr)
      return (.isFalse q(isInt_lt_false $pa $pb $r) : Result q($a < $b))
  let ratArm (_ : Unit) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    -- We need a division ring with an order, and `LinearOrderedField` is the closest mathlib has.
    let _i ← inferLinearOrderedField α
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    let pa : Q(@IsRat _ StrictOrderedRing.toRing $a $na $da) := pa
    let pb : Q(@IsRat _ StrictOrderedRing.toRing $b $nb $db) := pb
    if qa < qb then
      let _i : Q(Nontrivial $α) := q(StrictOrderedRing.toNontrivial)
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isRat_lt_true $pa $pb $r) : Result q($a < $b))
    else
      let r : Q(decide ($nb * $da ≤ $na * $db) = true) := (q(Eq.refl true) : Expr)
      return (.isFalse q(isRat_lt_false $pa $pb $r) : Result q($a < $b))
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat _ .., _ | _, .isRat _ .. => ratArm ()
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm ()
  | .isNat _ na pa, .isNat _ nb pb =>
    let _i ← inferOrderedSemiring α
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
    let pb : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $b $nb) := pb
    if na.natLit! < nb.natLit! then
      if let .some _i ←
          trySynthInstanceQ (q(@CharZero $α AddCommMonoidWithOne.toAddMonoidWithOne) : Q(Prop)) then
        let r : Q(Nat.ble $nb $na = false) := (q(Eq.refl false) : Expr)
        return (.isTrue q(isNat_lt_true $pa $pb $r) : Result q($a < $b))
      else -- Nats can appear in an `OrderedRing` without `CharZero`.
        intArm ()
    else
      let r : Q(Nat.ble $nb $na = true) := (q(Eq.refl true) : Expr)
      return (.isFalse q(isNat_lt_false $pa $pb $r) : Result q($a < $b))

/-! # Nat operations -/

theorem isNat_natSub : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.sub a' b' = c → IsNat (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.sub a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℕ) - _, Sub.sub (_ : ℕ) _, Nat.sub _ _] def evalNatSub :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  -- We trust that the default instance for `HSub` is `Nat.sub` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HSub.hSub (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have pa : Q(IsNat $a $na) := pa
  have pb : Q(IsNat $b $nb) := pb
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! - nb.natLit!)
  let r : Q(Nat.sub $na $nb = $nc) := (q(Eq.refl $nc) : Expr)
  return (.isNat sℕ nc q(isNat_natSub $pa $pb $r) : Result q($a - $b))

theorem isNat_natMod : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mod a' b' = c → IsNat (a % b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.mod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℕ) % _, Mod.mod (_ : ℕ) _, Nat.mod _ _] def evalNatMod :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  -- We trust that the default instance for `HMod` is `Nat.mod` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HMod.hMod (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have pa : Q(IsNat $a $na) := pa
  have pb : Q(IsNat $b $nb) := pb
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! % nb.natLit!)
  let r : Q(Nat.mod $na $nb = $nc) := (q(Eq.refl $nc) : Expr)
  return (.isNat sℕ nc q(isNat_natMod $pa $pb $r) : Result q($a % $b))
