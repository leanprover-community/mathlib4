/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Inv

/-!
# `norm_num` extension for equalities
-/

variable {α : Type*}

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

theorem isNat_eq_false [AddMonoidWithOne α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.beq a' b' = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa using Nat.ne_of_beq_eq_false h

lemma CharP.cast_eq_cast_iff
    (p : ℕ) [AddMonoidWithOne α] [CharP α p] [IsLeftCancelAdd α] (x y : ℕ) :
    (x : α) = y ↔ ↑p ∣ (x - y : ℤ) := by
  obtain (h|h) := Nat.le_total x y
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add, Nat.cast_add, sub_add_cancel_left, Int.dvd_neg,
      Int.natCast_dvd_natCast, ← CharP.cast_eq_zero_iff (R := α),
      ← add_left_cancel_iff (a := (x : α)) (b := k), add_zero, eq_comm]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add, add_comm, Nat.cast_add, add_sub_cancel_right,
      Int.natCast_dvd_natCast, ← CharP.cast_eq_zero_iff (R := α),
      ← add_left_cancel_iff (a := (y : α)) (b := k), add_zero, eq_comm]

theorem isNat_eq_false_of_charP (p : ℕ) [AddMonoidWithOne α] [CharP α p] [IsLeftCancelAdd α] :
    {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → (a' - b' : ℤ) % p ≠ 0 → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa [CharP.cast_eq_cast_iff p, Int.dvd_iff_emod_eq_zero]

theorem isInt_eq_false [Ring α] [CharZero α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' = b') = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simpa using of_decide_eq_false h

theorem Rat.invOf_denom_swap [Ring α] (n₁ n₂ : ℤ) (a₁ a₂ : α)
    [Invertible a₁] [Invertible a₂] : n₁ * ⅟a₁ = n₂ * ⅟a₂ ↔ n₁ * a₂ = n₂ * a₁ := by
  rw [mul_invOf_eq_iff_eq_mul_right, ← Int.commute_cast, mul_assoc,
    ← mul_left_eq_iff_eq_invOf_mul, Int.commute_cast]

theorem isRat_eq_false [Ring α] [CharZero α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) = Int.mul nb (.ofNat da)) = false → ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    rw [Rat.invOf_denom_swap]; exact mod_cast of_decide_eq_false h

-- def evalEqOfCharP (p : ℕ) {u : Level} {α : Q(Type u)} {inst : Q(DivisionRing $α)}
--     {a b : Q($α)} (ra : Result a) (rb : Result b) : NormNumM (Result q($a = $b)) := do
--   let _ ← synthInstanceQ q(CharP $α $p)

--   sorry

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a = b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ = _] def evalEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  haveI' : $e =Q ($a = $b) := ⟨⟩
  guard <|← withNewMCtxDepth <| isDefEq f q(Eq (α := $α))
  let ra ← deriveCharP a; let rb ← deriveCharP b
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
      for p in (← readThe Config).char do
        try
          have pe : Q(ℕ) := mkNatLit p
          let _ ← synthInstanceQ q(CharP $α $pe)
          if (na.natLit! - nb.natLit! : ℤ) % p = 0 then
            failure
            -- a and b should be normalized already so `na.natLit! = nb.natLit!` should capture it.
          else
            let _ ← synthInstanceQ q(IsLeftCancelAdd $α)
            let r ← mkDecideProofQ q(($na - $nb : ℤ) % $pe ≠ 0)
            return .isFalse q(isNat_eq_false_of_charP $pe $pa $pb $r)
        catch e =>
          continue
      failure --TODO: nonzero characteristic ≠

end Mathlib.Meta.NormNum
