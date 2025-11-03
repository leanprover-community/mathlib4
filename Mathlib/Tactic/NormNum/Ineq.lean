/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Algebra.Order.Invertible
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Cast

/-!
# `norm_num` extensions for inequalities.
-/

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

variable {u : Level}

/-- Helper function to synthesize typed `Semiring α` `PartialOrder α` `IsOrderedSemiring α`
expressions. -/
def inferOrderedSemiring (α : Q(Type u)) : MetaM <|
    (_ : Q(Semiring $α)) × (_ : Q(PartialOrder $α)) × Q(IsOrderedRing $α) :=
  let go := do
    let semiring ← synthInstanceQ q(Semiring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨semiring, partialOrder, isOrderedRing⟩
  go <|> throwError "not an ordered semiring"

/-- Helper function to synthesize typed `Ring α` `PartialOrder α` `IsOrderedSemiring α`
expressions. -/
def inferOrderedRing (α : Q(Type u)) : MetaM <|
    (_ : Q(Ring $α)) × (_ : Q(PartialOrder $α)) × Q(IsOrderedRing $α) :=
  let go := do
    let ring ← synthInstanceQ q(Ring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨ring, partialOrder, isOrderedRing⟩
  go <|> throwError "not an ordered ring"

/-- Helper function to synthesize typed `Semifield α` `LinearOrder α` `IsStrictOrderedRing α`
expressions. -/
def inferLinearOrderedSemifield (α : Q(Type u)) : MetaM <|
    (_ : Q(Semifield $α)) × (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α) :=
  let go := do
    let semifield ← synthInstanceQ q(Semifield $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨semifield, linearOrder, isStrictOrderedRing⟩
  go <|> throwError "not a linear ordered semifield"

/-- Helper function to synthesize typed `Field α` `LinearOrder α` `IsStrictOrderedRing α`
expressions. -/
def inferLinearOrderedField (α : Q(Type u)) : MetaM <|
    (_ : Q(Field $α)) × (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α) :=
  let go := do
    let field ← synthInstanceQ q(Field $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨field, linearOrder, isStrictOrderedRing⟩
  go <|> throwError "not a linear ordered field"

variable {α : Type*}

theorem isNat_le_true [Semiring α] [PartialOrder α] [IsOrderedRing α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble a' b' = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.mono_cast (Nat.le_of_ble_eq_true h)

theorem isNat_lt_false [Semiring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a < b :=
  not_lt_of_ge (isNat_le_true hb ha h)

theorem isNNRat_le_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} → {na nb : ℕ} → {da db : ℕ} →
    IsNNRat a na da → IsNNRat b nb db →
    decide (Nat.mul na (db) ≤ Nat.mul nb (da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := (Nat.cast_le (α := α)).mpr <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Nat.commute_cast] at h
    simp only [Nat.mul_eq, Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

theorem isNNRat_lt_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Nontrivial α] :
    {a b : α} → {na nb : ℕ} → {da db : ℕ} →
    IsNNRat a na da → IsNNRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := (Nat.cast_lt (α := α)).mpr <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Nat.commute_cast] at h
    simp? at h says simp only [Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

theorem isNNRat_le_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Nontrivial α]
    {a b : α} {na nb : ℕ} {da db : ℕ}
    (ha : IsNNRat a na da) (hb : IsNNRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_gt (isNNRat_lt_true hb ha h)

theorem isNNRat_lt_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : ℕ} {da db : ℕ}
    (ha : IsNNRat a na da) (hb : IsNNRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_ge (isNNRat_le_true hb ha h)

theorem isRat_le_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) ≤ Int.mul nb (.ofNat da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_mono (R := α) <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp only [Int.ofNat_eq_natCast, Int.mul_def, Int.cast_mul, Int.cast_natCast,
      mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

theorem isRat_lt_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Nontrivial α] :
    {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_strictMono (R := α) <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp? at h says simp only [Int.cast_mul, Int.cast_natCast, mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

theorem isRat_le_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Nontrivial α]
    {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_gt (isRat_lt_true hb ha h)

theorem isRat_lt_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_ge (isRat_le_true hb ha h)

/-! # (In)equalities -/

theorem isNat_lt_true [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α] :
    {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble b' a' = false → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h =>
    Nat.cast_lt.2 <| ble_eq_false.1 h

theorem isNat_le_false [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α]
    {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b' = false) : ¬a ≤ b :=
  not_le_of_gt (isNat_lt_true hb ha h)

theorem isInt_le_true [Ring α] [PartialOrder α] [IsOrderedRing α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' ≤ b') → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_mono <| of_decide_eq_true h

theorem isInt_lt_true [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] :
    {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' < b') → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 <| of_decide_eq_true h

theorem isInt_le_false [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a')) : ¬a ≤ b :=
  not_le_of_gt (isInt_lt_true hb ha h)

theorem isInt_lt_false [Ring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' ≤ a')) : ¬a < b :=
  not_lt_of_ge (isInt_le_true hb ha h)

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a ≤ b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ ≤ _] def evalLE : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LE $α)
  guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
  core lα ra rb
where
  /-- Identify (as `true` or `false`) expressions of the form `a ≤ b`, where `a` and `b` are numeric
  expressions whose evaluations to `NormNum.Result` have already been computed. -/
  core {u : Level} {α : Q(Type u)} (lα : Q(LE $α)) {a b : Q($α)}
    (ra : NormNum.Result a) (rb : NormNum.Result b) : MetaM (NormNum.Result q($a ≤ $b)) := do
  let e := q($a ≤ $b)
  let rec intArm : MetaM (Result e) := do
    let ⟨_ir, _, _i⟩ ← inferOrderedRing α
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q($_ir)
    let ⟨zb, nb, pb⟩ ← rb.toInt q($_ir)
    assumeInstancesCommute
    if decide (za ≤ zb) then
      let r : Q(decide ($na ≤ $nb) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isInt_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ q(Nontrivial $α) then
      let r : Q(decide ($nb < $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_le_false $pa $pb $r)
    else
      failure
  let rec ratArm : MetaM (Result e) := do
    let ⟨_if, _, _i⟩ ← inferLinearOrderedField α
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    assumeInstancesCommute
    if decide (qa ≤ qb) then
      let r : Q(decide ($na * $db ≤ $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isRat_le_true $pa $pb $r))
    else
      let _i : Q(Nontrivial $α) := q(IsStrictOrderedRing.toNontrivial)
      let r : Q(decide ($nb * $da < $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isRat_le_false $pa $pb $r)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNNRat _ .., _ | _, .isNNRat _ .. => ratArm
  | .isNegNNRat _ .., _ | _, .isNegNNRat _ .. => ratArm
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm
  | .isNat ra na pa, .isNat rb nb pb =>
    let ⟨_, _, _i⟩ ← inferOrderedSemiring α
    haveI' : $ra =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $rb =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    assumeInstancesCommute
    if na.natLit! ≤ nb.natLit! then
      let r : Q(Nat.ble $na $nb = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNat_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ q(CharZero $α) then
      let r : Q(Nat.ble $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_le_false $pa $pb $r)
    else -- Nats can appear in an `OrderedRing` without `CharZero`.
      intArm

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a < b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ < _] def evalLT : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LT $α)
  guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
  core lα ra rb
where
  /-- Identify (as `true` or `false`) expressions of the form `a < b`, where `a` and `b` are numeric
  expressions whose evaluations to `NormNum.Result` have already been computed. -/
  core {u : Level} {α : Q(Type u)} (lα : Q(LT $α)) {a b : Q($α)}
    (ra : NormNum.Result a) (rb : NormNum.Result b) : MetaM (NormNum.Result q($a < $b)) := do
  let e := q($a < $b)
  let rec intArm : MetaM (Result e) := do
    let ⟨_ir, _, _i⟩ ← inferOrderedRing α
    haveI' : $e =Q ($a < $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q($_ir)
    let ⟨zb, nb, pb⟩ ← rb.toInt q($_ir)
    assumeInstancesCommute
    if za < zb then
      if let .some _i ← trySynthInstanceQ q(Nontrivial $α) then
        let r : Q(decide ($na < $nb) = true) := (q(Eq.refl true) : Expr)
        return .isTrue q(isInt_lt_true $pa $pb $r)
      else
        failure
    else
      let r : Q(decide ($nb ≤ $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_lt_false $pa $pb $r)
  let rec nnratArm : MetaM (Result e) := do
    -- We need a division ring with an order, and `LinearOrderedField` is the closest mathlib has.
    /-
       NOTE: after the ordered algebra refactor, this is not true anymore,
       so there may be a better typeclass
    -/
    let ⟨_, _, _⟩ ← inferLinearOrderedSemifield α
    assumeInstancesCommute
    haveI' : $e =Q ($a < $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' q(Semifield.toDivisionSemiring)
    let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' q(Semifield.toDivisionSemiring)
    if qa < qb then
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNNRat_lt_true $pa $pb $r)
    else
      let r : Q(decide ($nb * $da ≤ $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isNNRat_lt_false $pa $pb $r)
  let rec ratArm : MetaM (Result e) := do
    -- We need a division ring with an order, and `LinearOrderedField` is the closest mathlib has.
    /-
       NOTE: after the ordered algebra refactor, this is not true anymore,
       so there may be a better typeclass
    -/
    let ⟨_, _, _i⟩ ← inferLinearOrderedField α
    assumeInstancesCommute
    haveI' : $e =Q ($a < $b) := ⟨⟩
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
  | .isNegNNRat _ .., _ | _, .isNegNNRat _ .. => ratArm
    -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat _ .., .isNegNat _ .. | .isNegNat _ .., .isNNRat _ .. => ratArm
  | .isNNRat _ .., _ | _, .isNNRat _ .. => nnratArm
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm
  | .isNat ra na pa, .isNat rb nb pb =>
    let ⟨_, _, _i⟩ ← inferOrderedSemiring α
    haveI' : $ra =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $rb =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $e =Q ($a < $b) := ⟨⟩
    assumeInstancesCommute
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
