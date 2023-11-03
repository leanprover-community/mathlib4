/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.NormNum.CharZero
import Mathlib.Tactic.NormNum.OrderedRing
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.HaveI
import Mathlib.Tactic.Clear!
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Order.Invertible
import Mathlib.Util.Qq

/-!
## `norm_num` basic plugins

This file adds `norm_num` plugins for `+`, `*` and `^` along with other basic operations.
-/

set_option autoImplicit true

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
  | ~q(Zero.zero) => return .isNat sα (mkRawNatLit 0) q(isNat_zero $α)

theorem isNat_one (α) [AddMonoidWithOne α] : IsNat (One.one : α) (nat_lit 1) := ⟨Nat.cast_one.symm⟩

/-- The `norm_num` extension which identifies the expression `One.one`, returning `1`. -/
@[norm_num One.one] def evalOne : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return .isNat sα (mkRawNatLit 1) q(isNat_one $α)

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
    return .isNat sα n q(isNat_ofNat $α $pa)

theorem isNat_intOfNat : {n n' : ℕ} → IsNat n n' → IsNat (Int.ofNat n) n'
  | _, _, ⟨rfl⟩ => ⟨rfl⟩

/-- The `norm_num` extension which identifies the constructor application `Int.ofNat n` such that
`norm_num` successfully recognizes `n`, returning `n`. -/
@[norm_num Int.ofNat _] def evalIntOfNat : NormNumExt where eval {u α} e := do
  let .app (.const ``Int.ofNat _) (n : Q(ℕ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q Int := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let sℤ : Q(AddMonoidWithOne ℤ) := q(AddGroupWithOne.toAddMonoidWithOne)
  let ⟨n', p⟩ ← deriveNat n sℕ
  haveI' x : $e =Q Int.ofNat $n := ⟨⟩
  return .isNat sℤ n' q(isNat_intOfNat $p)

/-! # Casts -/

theorem isNat_cast {R} [AddMonoidWithOne R] (n m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
@[norm_num Nat.cast _, NatCast.natCast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  let .app n (a : Q(ℕ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq n q(Nat.cast (R := $α))
  let ⟨na, pa⟩ ← deriveNat a q(instAddMonoidWithOneNat)
  haveI' : $e =Q $a := ⟨⟩
  return .isNat sα na q(isNat_cast $a $na $pa)

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
    assumeInstancesCommute
    haveI' : $e =Q Int.cast $a := ⟨⟩
    return .isNat _ na q(isNat_int_cast $a $na $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    haveI' : $e =Q Int.cast $a := ⟨⟩
    return .isNegNat _ na q(isInt_cast $a (.negOfNat $na) $pa)
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
  let r ← derive q($a)
  haveI' : $e =Q Rat.cast $a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    return .isNegNat _ na q(isInt_ratCast $pa)
  | .isRat _ qa na da pa =>
    assumeInstancesCommute
    let i ← inferCharZeroOfDivisionRing dα
    return .isRat dα qa na da q(isRat_ratCast $pa)
  | _ => failure

/-! # Arithmetic -/

library_note "norm_num lemma function equality"/--
Note: Many of the lemmas in this file use a function equality hypothesis like `f = HAdd.hAdd`
below. The reason for this is that when this is applied, to prove e.g. `100 + 200 = 300`, the
`+` here is `HAdd.hAdd` with an instance that may not be syntactically equal to the one supplied
by the `AddMonoidWithOne` instance, and rather than attempting to prove the instances equal lean
will sometimes decide to evaluate `100 + 200` directly (into whatever `+` is defined to do in this
ring), which is definitely not what we want; if the subterms are expensive to kernel-reduce then
this could cause a `(kernel) deep recursion detected` error (see lean4#2171, mathlib4#4048).

By using an equality for the unapplied `+` function and proving it by `rfl` we take away the
opportunity for lean to unfold the numerals (and the instance defeq problem is usually comparatively
easy).
-/

-- see note [norm_num lemma function equality]
theorem isNat_add {α} [AddMonoidWithOne α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℕ},
    f = HAdd.hAdd → IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_add _ _).symm⟩

-- see note [norm_num lemma function equality]
theorem isInt_add {α} [Ring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℤ},
    f = HAdd.hAdd → IsInt a a' → IsInt b b' → Int.add a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

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
-- see note [norm_num lemma function equality]
theorem isRat_add {α} [Ring α] {f : α → α → α} {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    f = HAdd.hAdd → IsRat a na da → IsRat b nb db →
    Int.add (Int.mul na db) (Int.mul nb da) = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
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
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
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
    let rec intArm (rα : Q(Ring $α)) := do
      haveI' : $e =Q $a + $b := ⟨⟩
      let ⟨za, na, pa⟩ ← ra.toInt _; let ⟨zb, nb, pb⟩ ← rb.toInt _
      haveI' : $f =Q HAdd.hAdd := ⟨⟩
      let zc := za + zb
      have c := mkRawIntLit zc
      haveI' : Int.add $na $nb =Q $c := ⟨⟩
      return .isInt rα c zc q(isInt_add (f := $f) (.refl $f) $pa $pb (.refl $c))
    let rec ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      haveI' : $e =Q $a + $b := ⟨⟩
      haveI' : $f =Q HAdd.hAdd := ⟨⟩
      let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
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
      return .isRat' dα qc nc dc q(isRat_add (f := $f) (.refl $f) $pa $pb $r1 $r2)
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
    | .isNat _ na pa, .isNat sα nb pb =>
      haveI' : $e =Q $a + $b := ⟨⟩
      haveI' : $f =Q HAdd.hAdd := ⟨⟩
      assumeInstancesCommute
      have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
      haveI' : Nat.add $na $nb =Q $c := ⟨⟩
      return .isNat sα c q(isNat_add (f := $f) (.refl $f) $pa $pb (.refl $c))
  core

-- see note [norm_num lemma function equality]
theorem isInt_neg {α} [Ring α] : ∀ {f : α → α} {a : α} {a' b : ℤ},
    f = Neg.neg → IsInt a a' → Int.neg a' = b → IsInt (-a) b
  | _, _, _, _, rfl, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

-- see note [norm_num lemma function equality]
theorem isRat_neg {α} [Ring α] : ∀ {f : α → α} {a : α} {n n' : ℤ} {d : ℕ},
    f = Neg.neg → IsRat a n d → Int.neg n = n' → IsRat (-a) n' d
  | _, _, _, _, _, rfl, ⟨h, rfl⟩, rfl => ⟨h, by rw [← neg_mul, ← Int.cast_neg]; rfl⟩

/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
  let ⟨(_f_eq : $f =Q Neg.neg)⟩ ← withNewMCtxDepth <| assertDefEqQ _ _
  haveI' _e_eq : $e =Q -$a := ⟨⟩
  let rec
  /-- Main part of `evalNeg`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      assumeInstancesCommute
      let ⟨za, na, pa⟩ ← ra.toInt rα
      let zb := -za
      have b := mkRawIntLit zb
      haveI' : Int.neg $na =Q $b := ⟨⟩
      return .isInt rα b zb q(isInt_neg (f := $f) (.refl $f) $pa (.refl $b))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      assumeInstancesCommute
      let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
      let qb := -qa
      have nb := mkRawIntLit qb.num
      haveI' : Int.neg $na =Q $nb := ⟨⟩
      return .isRat' dα qb nb da q(isRat_neg (f := $f) (.refl $f) $pa (.refl $nb))
    match ra with
    | .isBool _ .. => failure
    | .isNat _ .. => intArm rα
    | .isNegNat rα .. => intArm rα
    | .isRat dα .. => ratArm dα
  core

-- see note [norm_num lemma function equality]
theorem isInt_sub {α} [Ring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℤ},
    f = HSub.hSub → IsInt a a' → IsInt b b' → Int.sub a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

-- see note [norm_num lemma function equality]
theorem isRat_sub {α} [Ring α] {f : α → α → α} {a b : α} {na nb nc : ℤ} {da db dc k : ℕ}
    (hf : f = HSub.hSub) (ra : IsRat a na da) (rb : IsRat b nb db)
    (h₁ : Int.sub (Int.mul na db) (Int.mul nb da) = Int.mul k nc)
    (h₂ : Nat.mul da db = Nat.mul k dc) :
    IsRat (f a b) nc dc := by
  rw [hf, sub_eq_add_neg]
  refine isRat_add rfl ra (isRat_neg (n' := -nb) rfl rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

/-- The `norm_num` extension which identifies expressions of the form `a - b` in a ring,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ - _, Sub.sub _ _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let rα ← inferRing α
  let ⟨(_f_eq : $f =Q HSub.hSub)⟩ ← withNewMCtxDepth <| assertDefEqQ _ _
  let ra ← derive a; let rb ← derive b
  haveI' _e_eq : $e =Q $a - $b := ⟨⟩
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      assumeInstancesCommute
      let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
      let zc := za - zb
      have c := mkRawIntLit zc
      haveI' : Int.sub $na $nb =Q $c := ⟨⟩
      return Result.isInt rα c zc q(isInt_sub (f := $f) (.refl $f) $pa $pb (.refl $c))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      assumeInstancesCommute
      let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
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
      return .isRat' dα qc nc dc q(isRat_sub (f := $f) (.refl $f) $pa $pb $r1 $r2)
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα ..
    | .isNat _ .., .isNat _ .. => intArm rα
  core

-- see note [norm_num lemma function equality]
theorem isNat_mul {α} [Semiring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℕ},
    f = HMul.hMul → IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_mul ..).symm⟩

-- see note [norm_num lemma function equality]
theorem isInt_mul {α} [Ring α] : ∀ {f : α → α → α} {a b : α} {a' b' c : ℤ},
    f = HMul.hMul → IsInt a a' → IsInt b b' → Int.mul a' b' = c → IsInt (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩

theorem isRat_mul {α} [Ring α] {f : α → α → α} {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    f = HMul.hMul → IsRat a na da → IsRat b nb db →
    Int.mul na nb = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (f a b) nc dc := by
  rintro rfl ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
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
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
  guard <|← withNewMCtxDepth <| isDefEq f q(HMul.hMul (α := $α))
  haveI' : $f =Q HMul.hMul := ⟨⟩
  haveI' : $e =Q $a * $b := ⟨⟩
  let rec
  /-- Main part of `evalMul`. -/
  core : Option (Result e) := do
    let rec intArm (rα : Q(Ring $α)) := do
      assumeInstancesCommute
      let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
      let zc := za * zb
      have c := mkRawIntLit zc
      haveI' : Int.mul $na $nb =Q $c := ⟨⟩
      return .isInt rα c zc q(isInt_mul (f := $f) (.refl $f) $pa $pb (.refl $c))
    let rec ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      assumeInstancesCommute
      let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
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
      return .isRat' dα qc nc dc q(isRat_mul (f := $f) (.refl $f) $pa $pb $r1 $r2)
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
    | .isNat mα' na pa, .isNat mα nb pb =>
      haveI' : $mα =Q by clear! $mα $mα'; apply AddCommMonoidWithOne.toAddMonoidWithOne := ⟨⟩
      assumeInstancesCommute
      have c : Q(ℕ) := mkRawNatLit (na.natLit! * nb.natLit!)
      haveI' : Nat.mul $na $nb =Q $c := ⟨⟩
      return .isNat mα c q(isNat_mul (f := $f) (.refl $f) $pa $pb (.refl $c))
  core

theorem natPow_zero : Nat.pow a (nat_lit 0) = nat_lit 1 := rfl
theorem natPow_one : Nat.pow a (nat_lit 1) = a := Nat.pow_one _
theorem zero_natPow : Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0 := rfl
theorem one_natPow : Nat.pow (nat_lit 1) b = nat_lit 1 := Nat.one_pow _

/-- This is an opaque wrapper around `Nat.pow` to prevent lean from unfolding the definition of
`Nat.pow` on numerals. The arbitrary precondition `p` is actually a formula of the form
`Nat.pow a' b' = c'` but we usually don't care to unfold this proposition so we just carry a
reference to it. -/
structure IsNatPowT (p : Prop) (a b c : Nat) : Prop where
  /-- Unfolds the assertion. -/
  run' : p → Nat.pow a b = c

theorem IsNatPowT.run
  (p : IsNatPowT (Nat.pow a (nat_lit 1) = a) a b c) : Nat.pow a b = c := p.run' (Nat.pow_one _)

/-- This is the key to making the proof proceed as a balanced tree of applications instead of
a linear sequence. It is just modus ponens after unwrapping the definitions. -/
theorem IsNatPowT.trans (h1 : IsNatPowT p a b c) (h2 : IsNatPowT (Nat.pow a b = c) a b' c') :
    IsNatPowT p a b' c' := ⟨h2.run' ∘ h1.run'⟩

theorem IsNatPowT.bit0 : IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b) (Nat.mul c c) :=
  ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩
theorem IsNatPowT.bit1 :
    IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b + nat_lit 1) (Nat.mul c (Nat.mul c a)) :=
  ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

/--
Proves `Nat.pow a b = c` where `a` and `b` are raw nat literals. This could be done by just
`rfl` but the kernel does not have a special case implementation for `Nat.pow` so this would
proceed by unary recursion on `b`, which is too slow and also leads to deep recursion.

We instead do the proof by binary recursion, but this can still lead to deep recursion,
so we use an additional trick to do binary subdivision on `log2 b`. As a result this produces
a proof of depth `log (log b)` which will essentially never overflow before the numbers involved
themselves exceed memory limits.
-/
partial def evalNatPow (a b : Q(ℕ)) : (c : Q(ℕ)) × Q(Nat.pow $a $b = $c) :=
  if b.natLit! = 0 then
    haveI : $b =Q 0 := ⟨⟩
    ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
    haveI : $a =Q 0 := ⟨⟩
    have b' : Q(ℕ) := mkRawNatLit (b.natLit! - 1)
    haveI : $b =Q Nat.succ $b' := ⟨⟩
    ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
    haveI : $a =Q 1 := ⟨⟩
    ⟨q(nat_lit 1), q(one_natPow)⟩
  else if b.natLit! = 1 then
    haveI : $b =Q 1 := ⟨⟩
    ⟨a, q(natPow_one)⟩
  else
    let ⟨c, p⟩ := go b.natLit!.log2 a (mkRawNatLit 1) a b _ .rfl
    ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ = c₀`, `depth > 0`, `b >>> depth = b₀`, `p := Nat.pow $a $b₀ = $c₀` -/
  go (depth : Nat) (a b₀ c₀ b : Q(ℕ)) (p : Q(Prop)) (hp : $p =Q (Nat.pow $a $b₀ = $c₀)) :
      (c : Q(ℕ)) × Q(IsNatPowT $p $a $b $c) :=
    let b' := b.natLit!
    if depth ≤ 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(ℕ) := mkRawNatLit (c₀' * c₀')
        haveI : $c =Q Nat.mul $c₀ $c₀ := ⟨⟩
        haveI : $b =Q 2 * $b₀ := ⟨⟩
        ⟨c, q(IsNatPowT.bit0)⟩
      else
        have c : Q(ℕ) := mkRawNatLit (c₀' * (c₀' * a'))
        haveI : $c =Q Nat.mul $c₀ (Nat.mul $c₀ $a) := ⟨⟩
        haveI : $b =Q 2 * $b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(ℕ) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a hi c1 b q(Nat.pow $a $hi = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩

theorem intPow_ofNat (h1 : Nat.pow a b = c) :
    Int.pow (Int.ofNat a) b = Int.ofNat c := by simp [← h1]

theorem intPow_negOfNat_bit0 (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' = b) (hc : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  rw [← hb, Int.negOfNat_eq, pow_eq, pow_mul, neg_pow_two, ← pow_mul, two_mul, pow_add, ← hc, ← h1]
  simp

theorem intPow_negOfNat_bit1 (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  rw [← hb, Int.negOfNat_eq, Int.negOfNat_eq, pow_eq, pow_succ, pow_mul, neg_pow_two, ← pow_mul,
    two_mul, pow_add, ← hc, ← h1]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Evaluates `Int.pow a b = c` where `a` and `b` are raw integer literals. -/
partial def evalIntPow (za : ℤ) (a : Q(ℤ)) (b : Q(ℕ)) : ℤ × (c : Q(ℤ)) × Q(Int.pow $a $b = $c) :=
  have a' : Q(ℕ) := a.appArg!
  if 0 ≤ za then
    haveI : $a =Q .ofNat $a' := ⟨⟩
    let ⟨c, p⟩ := evalNatPow a' b
    ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
    haveI : $a =Q .negOfNat $a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(ℕ) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ := evalNatPow a' b₀
    let c' := c₀.natLit!
    if b' &&& 1 == 0 then
      have c : Q(ℕ) := mkRawNatLit (c' * c')
      have pc : Q($c₀ * $c₀ = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ = $b) := (q(Eq.refl $b) : Expr)
      ⟨c.natLit!, q(.ofNat $c), q(intPow_negOfNat_bit0 $p $pb $pc)⟩
    else
      have c : Q(ℕ) := mkRawNatLit (c' * (c' * a'.natLit!))
      have pc : Q($c₀ * ($c₀ * $a') = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ + 1 = $b) := (q(Eq.refl $b) : Expr)
      ⟨-c.natLit!, q(.negOfNat $c), q(intPow_negOfNat_bit1 $p $pb $pc)⟩

-- see note [norm_num lemma function equality]
theorem isNat_pow {α} [Semiring α] : ∀ {f : α → ℕ → α} {a : α} {b a' b' c : ℕ},
    f = HPow.hPow → IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
theorem isInt_pow {α} [Ring α] : ∀ {f : α → ℕ → α} {a : α} {b : ℕ} {a' : ℤ} {b' : ℕ} {c : ℤ},
    f = HPow.hPow → IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
theorem isRat_pow {α} [Ring α] {f : α → ℕ → α} {a : α} {an cn : ℤ} {ad b b' cd : ℕ} :
    f = HPow.hPow → IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → ℕ → $α)) (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(instAddMonoidWithOneNat)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  haveI' : $e =Q $a ^ $b := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  let rec
  /-- Main part of `evalPow`. -/
  core : Option (Result e) := do
    match ra with
    | .isBool .. => failure
    | .isNat sα na pa =>
      assumeInstancesCommute
      have ⟨c, r⟩ := evalNatPow na nb
      return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
    | .isNegNat rα .. =>
      assumeInstancesCommute
      let ⟨za, na, pa⟩ ← ra.toInt rα
      have ⟨zc, c, r⟩ := evalIntPow za na nb
      return .isInt rα c zc q(isInt_pow (f := $f) (.refl $f) $pa $pb $r)
    | .isRat dα qa na da pa =>
      assumeInstancesCommute
      have ⟨zc, nc, r1⟩ := evalIntPow qa.num na nb
      have ⟨dc, r2⟩ := evalNatPow da nb
      let qc := mkRat zc dc.natLit!
      return .isRat' dα qc nc dc q(isRat_pow (f := $f) (.refl $f) $pa $pb $r1 $r2)
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
    Int.cast_ofNat, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

/-- The `norm_num` extension which identifies expressions of the form `a⁻¹`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dα ← inferDivisionRing α
  let _i ← inferCharZeroOfDivisionRing? dα
  guard <|← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  haveI' : $e =Q $a⁻¹ := ⟨⟩
  assumeInstancesCommute
  let rec
  /-- Main part of `evalInv`. -/
  core : Option (Result e) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := qa⁻¹
    if qa > 0 then
      if let some _i := _i then
        have lit : Q(ℕ) := na.appArg!
        haveI : $na =Q Int.ofNat $lit := ⟨⟩
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        haveI : $lit =Q ($lit2).succ := ⟨⟩
        return .isRat' dα qb q(.ofNat $da) lit q(isRat_inv_pos $pa)
      else
        guard (qa = 1)
        let .isNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNat inst n (q(isRat_inv_one $pa))
    else if qa < 0 then
      if let some _i := _i then
        have lit : Q(ℕ) := na.appArg!
        haveI : $na =Q Int.negOfNat $lit := ⟨⟩
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        haveI : $lit =Q ($lit2).succ := ⟨⟩
        return .isRat' dα qb q(.negOfNat $da) lit q(isRat_inv_neg $pa)
      else
        guard (qa = -1)
        let .isNegNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNegNat inst n q(isRat_inv_neg_one $pa)
    else
      let .isNat inst n pa := ra | failure
      haveI' : $n =Q nat_lit 0 := ⟨⟩
      assumeInstancesCommute
      return .isNat inst n q(isRat_inv_zero $pa)
  core

theorem isRat_div [DivisionRing α] : {a b : α} → {cn : ℤ} → {cd : ℕ} → IsRat (a * b⁻¹) cn cd →
    IsRat (a / b) cn cd
  | _, _, _, _, h => by simp [div_eq_mul_inv]; exact h

/-- The `norm_num` extension which identifies expressions of the form `a / b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ / _, Div.div _ _] def evalDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dα ← inferDivisionRing α
  haveI' : $e =Q $a / $b := ⟨⟩
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  let ⟨qa, na, da, pa⟩ ← rab.toRat' dα
  assumeInstancesCommute
  return .isRat' dα qa na da q(isRat_div $pa)

/-! # Constructor-like operations -/

theorem isRat_mkRat : {a na n : ℤ} → {b nb d : ℕ} → IsInt a na → IsNat b nb →
    IsRat (na / nb : ℚ) n d → IsRat (mkRat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [Rat.mkRat_eq_div]; exact ⟨_, h⟩

/-- The `norm_num` extension which identifies expressions of the form `mkRat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num mkRat _ _] def evalMkRat : NormNumExt where eval {u α} (e : Q(ℚ)) : MetaM (Result e):= do
  let .app (.app (.const ``mkRat _) (a : Q(ℤ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : $e =Q mkRat $a $b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRingInt) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : Rat)
  let ⟨q, n, d, p⟩ ← rab.toRat' q(Rat.divisionRing)
  return .isRat' _ q n d q(isRat_mkRat $pa $pb $p)

-- see note [norm_num lemma function equality]
theorem isRat_ofScientific_of_true [DivisionRing α] (σα : OfScientific α) :
    {m e : ℕ} → {n : ℤ} → {d : ℕ} →
    @OfScientific.ofScientific α σα = (fun m s e ↦ (Rat.ofScientific m s e : α)) →
    IsRat (mkRat m (10 ^ e) : α) n d → IsRat (@OfScientific.ofScientific α σα m true e) n d
  | _, _, _, _, σh, ⟨_, eq⟩ => ⟨_, by simp only [σh, Rat.ofScientific_true_def]; exact eq⟩

-- see note [norm_num lemma function equality]
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
  haveI' : $e =Q OfScientific.ofScientific $m $b $exp := ⟨⟩
  haveI' lh : @OfScientific.ofScientific $α $σα =Q (fun m s e ↦ (Rat.ofScientific m s e : $α)) := ⟨⟩
  match b with
  | ~q(true)  =>
    let rme ← derive (q(mkRat $m (10 ^ $exp)) : Q($α))
    let some ⟨q, n, d, p⟩ := rme.toRat' dα | failure
    return .isRat' dα q n d q(isRat_ofScientific_of_true $σα $lh $p)
  | ~q(false) =>
    let ⟨nm, pm⟩ ← deriveNat m q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨ne, pe⟩ ← deriveNat exp q(AddCommMonoidWithOne.toAddMonoidWithOne)
    have pm : Q(IsNat $m $nm) := pm
    have pe : Q(IsNat $exp $ne) := pe
    let m' := nm.natLit!
    let exp' := ne.natLit!
    let n' := Nat.mul m' (Nat.pow (10 : ℕ) exp')
    have n : Q(ℕ) := mkRawNatLit n'
    haveI : $n =Q Nat.mul $nm ((10 : ℕ) ^ $ne) := ⟨⟩
    return .isNat _ n q(isNat_ofScientific_of_false $σα $lh $pm $pe (.refl $n))

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
  let .app (.const ``Not _) (a : Q(Prop)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq α q(Prop)
  let .isBool b p ← derive q($a) | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q Prop := ⟨⟩
  haveI' : $e =Q ¬ $a := ⟨⟩
  if b then
    have p : Q($a) := p
    return .isFalse q(not_not_intro $p)
  else
    have p : Q(¬ $a) := p
    return .isTrue q($p)

/-! # (In)equalities -/

theorem isNat_eq_true [AddMonoidWithOne α] : {a b : α} → {c : ℕ} →
    IsNat a c → IsNat b c → a = b
  | _, _, _, ⟨rfl⟩, ⟨rfl⟩ => rfl

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
@[norm_num _ = _, Eq _ _] def evalEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  haveI' : $e =Q ($a = $b) := ⟨⟩
  guard <|← withNewMCtxDepth <| isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let rec intArm (rα : Q(Ring $α)) := do
    let ⟨za, na, pa⟩ ← ra.toInt rα; let ⟨zb, nb, pb⟩ ← rb.toInt rα
    if za = zb then
      haveI' : $na =Q $nb := ⟨⟩
      return .isTrue q(isInt_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfRing? rα then
      let r : Q(decide ($na = $nb) = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isInt_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠
  let rec ratArm (dα : Q(DivisionRing $α)) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
    if qa = qb then
      haveI' : $na =Q $nb := ⟨⟩
      haveI' : $da =Q $db := ⟨⟩
      return .isTrue q(isRat_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfDivisionRing? dα then
      let r : Q(decide (Int.mul $na (.ofNat $db) = Int.mul $nb (.ofNat $da)) = false) :=
        (q(Eq.refl false) : Expr)
      return .isFalse q(isRat_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠
  match ra, rb with
  | .isBool b₁ p₁, .isBool b₂ p₂ =>
    have a : Q(Prop) := a; have b : Q(Prop) := b
    match b₁, p₁, b₂, p₂ with
    | true, (p₁ : Q($a)), true, (p₂ : Q($b)) =>
      return .isTrue q(eq_of_true $p₁ $p₂)
    | false, (p₁ : Q(¬$a)), false, (p₂ : Q(¬$b)) =>
      return .isTrue q(eq_of_false $p₁ $p₂)
    | false, (p₁ : Q(¬$a)), true, (p₂ : Q($b)) =>
      return .isFalse q(ne_of_false_of_true $p₁ $p₂)
    | true, (p₁ : Q($a)), false, (p₂ : Q(¬$b)) =>
      return .isFalse q(ne_of_true_of_false $p₁ $p₂)
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat _ na pa, .isNat mα nb pb =>
    assumeInstancesCommute
    if na.natLit! = nb.natLit! then
      haveI' : $na =Q $nb := ⟨⟩
      return .isTrue q(isNat_eq_true $pa $pb)
    else if let some _i ← inferCharZeroOfAddMonoidWithOne? mα then
      let r : Q(Nat.beq $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_eq_false $pa $pb $r)
    else
      failure --TODO: nonzero characteristic ≠

/-- The `norm_num` extension which identifies expressions of the form `a ≤ b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ ≤ _] def evalLE : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let rec intArm : MetaM (Result e) := do
    let _i ← inferOrderedRing α
    guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q(OrderedRing.toRing)
    let ⟨zb, nb, pb⟩ ← rb.toInt q(OrderedRing.toRing)
    if decide (za ≤ zb) then
      let r : Q(decide ($na ≤ $nb) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isInt_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ (q(@Nontrivial $α) : Q(Prop)) then
      let r : Q(decide ($nb < $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_le_false $pa $pb $r)
    else
      failure
  let rec ratArm : MetaM (Result e) := do
    -- We need a division ring with an order, and `LinearOrderedField` is the closest mathlib has.
    let _i ← inferLinearOrderedField α
    guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    if decide (qa ≤ qb) then
      let r : Q(decide ($na * $db ≤ $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isRat_le_true $pa $pb $r))
    else
      let _i : Q(Nontrivial $α) := q(StrictOrderedRing.toNontrivial)
      let r : Q(decide ($nb * $da < $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isRat_le_false $pa $pb $r)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat _ .., _ | _, .isRat _ .. => ratArm
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm
  | .isNat ra na pa, .isNat rb nb pb =>
    let _i ← inferOrderedSemiring α
    haveI' : $ra =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $rb =Q by clear! $ra $rb; infer_instance := ⟨⟩
    guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    if na.natLit! ≤ nb.natLit! then
      let r : Q(Nat.ble $na $nb = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNat_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ (q(CharZero $α) : Q(Prop)) then
      let r : Q(Nat.ble $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_le_false $pa $pb $r)
    else -- Nats can appear in an `OrderedRing` without `CharZero`.
      intArm

/-- The `norm_num` extension which identifies expressions of the form `a < b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ < _] def evalLT : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let rec intArm : MetaM (Result e) := do
    let _i ← inferOrderedRing α
    assumeInstancesCommute
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    haveI' : $e =Q ($a < $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q(OrderedRing.toRing)
    let ⟨zb, nb, pb⟩ ← rb.toInt q(OrderedRing.toRing)
    if za < zb then
      if let .some _i ← trySynthInstanceQ (q(@Nontrivial $α) : Q(Prop)) then
        let r : Q(decide ($na < $nb) = true) := (q(Eq.refl true) : Expr)
        return .isTrue q(isInt_lt_true $pa $pb $r)
      else
        failure
    else
      let r : Q(decide ($nb ≤ $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_lt_false $pa $pb $r)
  let rec ratArm : MetaM (Result e) := do
    -- We need a division ring with an order, and `LinearOrderedField` is the closest mathlib has.
    let _i ← inferLinearOrderedField α
    assumeInstancesCommute
    haveI' : $e =Q ($a < $b) := ⟨⟩
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    if qa < qb then
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isRat_lt_true $pa $pb $r)
    else
      let r : Q(decide ($nb * $da ≤ $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isRat_lt_false $pa $pb $r)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat _ .., _ | _, .isRat _ .. => ratArm
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm
  | .isNat ra na pa, .isNat rb nb pb =>
    let _i ← inferOrderedSemiring α
    haveI' : $ra =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $rb =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $e =Q ($a < $b) := ⟨⟩
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    if na.natLit! < nb.natLit! then
      if let .some _i ← trySynthInstanceQ q(CharZero $α) then
        let r : Q(Nat.ble $nb $na = false) := (q(Eq.refl false) : Expr)
        return .isTrue q(isNat_lt_true $pa $pb $r)
      else -- Nats can appear in an `OrderedRing` without `CharZero`.
        intArm
    else
      let r : Q(Nat.ble $nb $na = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isNat_lt_false $pa $pb $r)

/-! # Nat operations -/

theorem isNat_natSucc : {a : ℕ} → {a' c : ℕ} →
    IsNat a a' → Nat.succ a' = c → IsNat (a.succ) c
  | _, _,_, ⟨rfl⟩, rfl => ⟨by simp⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.succ a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num Nat.succ _] def evalNatSucc : NormNumExt where eval {u α} e := do
  let .app f (a : Q(ℕ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(Nat.succ)
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Nat.succ $a := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit!.succ)
  haveI' : $nc =Q ($na).succ := ⟨⟩
  return .isNat sℕ nc q(isNat_natSucc $pa (.refl $nc))

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
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a - $b := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! - nb.natLit!)
  haveI' : Nat.sub $na $nb =Q $nc := ⟨⟩
  return .isNat sℕ nc q(isNat_natSub $pa $pb (.refl $nc))

theorem isNat_natMod : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mod a' b' = c → IsNat (a % b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.mod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℕ) % _, Mod.mod (_ : ℕ) _, Nat.mod _ _] def evalNatMod :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a % $b := ⟨⟩
  -- We trust that the default instance for `HMod` is `Nat.mod` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HMod.hMod (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! % nb.natLit!)
  haveI' : Nat.mod $na $nb =Q $nc := ⟨⟩
  return .isNat sℕ nc q(isNat_natMod $pa $pb (.refl $nc))

theorem isNat_natDiv : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.div a' b' = c → IsNat (a / b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.div a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℕ) / _, Div.div (_ : ℕ) _, Nat.div _ _] def evalNatDiv :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q $a / $b := ⟨⟩
  -- We trust that the default instance for `HDiv` is `Nat.div` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! / nb.natLit!)
  haveI' : Nat.div $na $nb =Q $nc := ⟨⟩
  return .isNat sℕ nc q(isNat_natDiv $pa $pb (.refl $nc))
