/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Invertible
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Cast

/-!
# `norm_num` extensions for inequalities.
-/

set_option autoImplicit true

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

/-- Helper function to synthesize a typed `OrderedSemiring α` expression. -/
def inferOrderedSemiring (α : Q(Type u)) : MetaM Q(OrderedSemiring $α) :=
  return ← synthInstanceQ (q(OrderedSemiring $α) : Q(Type u)) <|>
    throwError "not an ordered semiring"

/-- Helper function to synthesize a typed `OrderedRing α` expression. -/
def inferOrderedRing (α : Q(Type u)) : MetaM Q(OrderedRing $α) :=
  return ← synthInstanceQ (q(OrderedRing $α) : Q(Type u)) <|> throwError "not an ordered ring"

/-- Helper function to synthesize a typed `LinearOrderedField α` expression. -/
def inferLinearOrderedField (α : Q(Type u)) : MetaM Q(LinearOrderedField $α) :=
  return ← synthInstanceQ (q(LinearOrderedField $α) : Q(Type u)) <|>
    throwError "not a linear ordered field"

theorem isNat_le_true [OrderedSemiring α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble a' b' = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.mono_cast (Nat.le_of_ble_eq_true h)

theorem isNat_lt_false [OrderedSemiring α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a < b :=
  not_lt_of_le (isNat_le_true hb ha h)

theorem isRat_le_true [LinearOrderedRing α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) ≤ Int.mul nb (.ofNat da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_mono (R := α) <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp at h; rwa [Int.commute_cast] at h

theorem isRat_lt_true [LinearOrderedRing α] [Nontrivial α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_strictMono (R := α) <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp? at h says simp only [Int.cast_mul, Int.cast_natCast, mul_mul_invOf_self_cancel'] at h
    rwa [Int.commute_cast] at h

theorem isRat_le_false [LinearOrderedRing α] [Nontrivial α] {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_lt (isRat_lt_true hb ha h)

theorem isRat_lt_false [LinearOrderedRing α] {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_le (isRat_le_true hb ha h)

/-! # (In)equalities -/

theorem isNat_lt_true [OrderedSemiring α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble b' a' = false → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h =>
    Nat.cast_lt.2 <| ble_eq_false.1 h

theorem isNat_le_false [OrderedSemiring α] [CharZero α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b' = false) : ¬a ≤ b :=
  not_le_of_lt (isNat_lt_true hb ha h)

theorem isInt_le_true [OrderedRing α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' ≤ b') → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_mono <| of_decide_eq_true h

theorem isInt_lt_true [OrderedRing α] [Nontrivial α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' < b') → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 <| of_decide_eq_true h

theorem isInt_le_false [OrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a')) : ¬a ≤ b :=
  not_le_of_lt (isInt_lt_true hb ha h)

theorem isInt_lt_false [OrderedRing α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' ≤ a')) : ¬a < b :=
  not_lt_of_le (isInt_le_true hb ha h)

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

end Mathlib.Meta.NormNum
