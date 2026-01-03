/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
module

public meta import Mathlib.Algebra.Order.Group.PosPart
public meta import Mathlib.Algebra.Order.Ring.Basic
public meta import Mathlib.Algebra.Order.Hom.Basic
public meta import Mathlib.Data.Int.CharZero
public meta import Mathlib.Data.Nat.Factorial.Basic
public meta import Mathlib.Data.NNRat.Defs
public meta import Mathlib.Data.PNat.Defs
public meta import Mathlib.Tactic.Positivity.Core
public meta import Qq

/-!
## `positivity` core extensions

This file sets up the basic `positivity` extensions tagged with the `@[positivity]` attribute.
-/

public meta section

variable {α : Type*}

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section ite
variable [Zero α] (p : Prop) [Decidable p] {a b : α}

set_option backward.privateInPublic true in
private lemma ite_pos [LT α] (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by
  by_cases p <;> simp [*]

set_option backward.privateInPublic true in
private lemma ite_nonneg [LE α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by
  by_cases p <;> simp [*]

set_option backward.privateInPublic true in
private lemma ite_nonneg_of_pos_of_nonneg [Preorder α] (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ ite p a b :=
  ite_nonneg _ ha.le hb

set_option backward.privateInPublic true in
private lemma ite_nonneg_of_nonneg_of_pos [Preorder α] (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ ite p a b :=
  ite_nonneg _ ha hb.le

set_option backward.privateInPublic true in
private lemma ite_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by by_cases p <;> simp [*]

set_option backward.privateInPublic true in
private lemma ite_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) :
    ite p a b ≠ 0 :=
  ite_ne_zero _ ha.ne' hb

set_option backward.privateInPublic true in
private lemma ite_ne_zero_of_ne_zero_of_pos [Preorder α] (ha : a ≠ 0) (hb : 0 < b) :
    ite p a b ≠ 0 :=
  ite_ne_zero _ ha hb.ne'

end ite

/-- The `positivity` extension which identifies expressions of the form `ite p a b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity ite _ _ _] def evalIte : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (.app (.app f (p : Q(Prop))) (_ : Q(Decidable $p))) (a : Q($α))) (b : Q($α))
    ← withReducible (whnf e) | throwError "not ite"
  haveI' : $e =Q ite $p $a $b := ⟨⟩
  let ra ← core zα pα? a; let rb ← core zα pα? b
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(ite (α := $α))
  match ra, rb with
  | .positive pa, .positive pb =>
    assumeInstancesCommute
    pure (.positive q(ite_pos $p $pa $pb))
  | .positive pa, .nonnegative pb =>
    let _b ← synthInstanceQ q(Preorder $α)
    assumeInstancesCommute
    pure (.nonnegative q(ite_nonneg_of_pos_of_nonneg $p $pa $pb))
  | .nonnegative pa, .positive pb =>
    let _b ← synthInstanceQ q(Preorder $α)
    assumeInstancesCommute
    pure (.nonnegative q(ite_nonneg_of_nonneg_of_pos $p $pa $pb))
  | .nonnegative pa, .nonnegative pb =>
    assumeInstancesCommute
    pure (.nonnegative q(ite_nonneg $p $pa $pb))
  | .positive pa, .nonzero pb =>
    let _b ← synthInstanceQ q(Preorder $α)
    assumeInstancesCommute
    pure (.nonzero q(ite_ne_zero_of_pos_of_ne_zero $p $pa $pb))
  | .nonzero pa, .positive pb =>
    let _b ← synthInstanceQ q(Preorder $α)
    assumeInstancesCommute
    pure (.nonzero q(ite_ne_zero_of_ne_zero_of_pos $p $pa $pb))
  | .nonzero pa, .nonzero pb =>
    pure (.nonzero q(ite_ne_zero $p $pa $pb))
  | _, _ => pure .none

section LinearOrder
variable {R : Type*} [LinearOrder R] {a b c : R}

set_option backward.privateInPublic true in
private lemma le_min_of_lt_of_le (ha : a < b) (hb : a ≤ c) : a ≤ min b c := le_min ha.le hb
set_option backward.privateInPublic true in
private lemma le_min_of_le_of_lt (ha : a ≤ b) (hb : a < c) : a ≤ min b c := le_min ha hb.le
set_option backward.privateInPublic true in
private lemma min_ne (ha : a ≠ c) (hb : b ≠ c) : min a b ≠ c := by
  grind

set_option backward.privateInPublic true in
private lemma min_ne_of_ne_of_lt (ha : a ≠ c) (hb : c < b) : min a b ≠ c := min_ne ha hb.ne'
set_option backward.privateInPublic true in
private lemma min_ne_of_lt_of_ne (ha : c < a) (hb : b ≠ c) : min a b ≠ c := min_ne ha.ne' hb

set_option backward.privateInPublic true in
private lemma max_ne (ha : a ≠ c) (hb : b ≠ c) : max a b ≠ c := by
  grind

end LinearOrder

/-- The `positivity` extension which identifies expressions of the form `min a b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity min _ _] def evalMin : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not min"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let lα ← synthInstanceQ q(LinearOrder $α)
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(min)
  match ← core zα pα? a, ← core zα pα? b with
  | .positive (ltα := ltα) pa, .positive pb =>
    haveI' : $ltα =Q ($lα).toLT := ⟨⟩
    assumeInstancesCommute
    pure (.positive q(lt_min $pa $pb))
  | .positive pa, .nonnegative pb =>
    assumeInstancesCommute
    pure (.nonnegative q(le_min_of_lt_of_le $pa $pb))
  | .nonnegative pa, .positive pb =>
    assumeInstancesCommute
    pure (.nonnegative q(le_min_of_le_of_lt $pa $pb))
  | .nonnegative pa (leα := leα), .nonnegative pb =>
    haveI' : $leα =Q ($lα).toLE := ⟨⟩
    assumeInstancesCommute
    pure (.nonnegative q(le_min $pa $pb))
  | .positive pa, .nonzero pb =>
    assumeInstancesCommute
    pure (.nonzero q(min_ne_of_lt_of_ne $pa $pb))
  | .nonzero pa, .positive pb =>
    assumeInstancesCommute
    pure (.nonzero q(min_ne_of_ne_of_lt $pa $pb))
  | .nonzero pa, .nonzero pb => do
    assumeInstancesCommute
    pure (.nonzero q(min_ne $pa $pb))
  | _, _ => pure .none

/-- Extension for the `max` operator. The `max` of two numbers is nonnegative if at least one
is nonnegative, strictly positive if at least one is positive, and nonzero if both are nonzero. -/
@[positivity max _ _] def evalMax : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not max"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(LinearOrder $α)
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(max)
  let result : Strictness zα pα? e ← catchNone do
    let ra ← core zα pα? a
    match ra with
    | .positive pa =>
      assumeInstancesCommute
      pure (.positive q(lt_max_of_lt_left $pa))
    | .nonnegative pa =>
      assumeInstancesCommute
      pure (.nonnegative q(le_max_of_le_left $pa))
    -- If `a ≠ 0`, we might prove `max a b ≠ 0` if `b ≠ 0` but we don't want to evaluate
    -- `b` before having ruled out `0 < a`, for performance. So we do that in the second branch
    -- of the `orElse'`.
    | _ => pure .none
  orElse result do
    let rb ← core zα pα? b
    match rb with
    | .positive pb =>
      assumeInstancesCommute
      pure (.positive q(lt_max_of_lt_right $pb))
    | .nonnegative pb =>
      assumeInstancesCommute
      pure (.nonnegative q(le_max_of_le_right $pb))
    | .nonzero pb => do
      match ← core zα pα? a with
      | .nonzero pa => pure (.nonzero q(max_ne $pa $pb))
      | _ => pure .none
    | _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a + b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ + _] def evalAdd : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not +"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(AddZeroClass $α)
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(HAdd.hAdd)
  let ra ← core zα pα? a; let rb ← core zα pα? b
  let some pα := pα? | failure
  match ra, rb with
  | .positive (ltα := ltα) pa, .positive pb =>
    let _a ← synthInstanceQ q(AddLeftStrictMono $α)
    haveI' : $ltα =Q ($pα).toLT := ⟨⟩
    assumeInstancesCommute
    pure (.positive q(add_pos $pa $pb))
  | .positive pa, .nonnegative pb =>
    let _a ← synthInstanceQ q(AddLeftMono $α)
    assumeInstancesCommute
    pure (.positive q(add_pos_of_pos_of_nonneg $pa $pb))
  | .nonnegative pa, .positive pb =>
    let _a ← synthInstanceQ q(AddRightMono $α)
    assumeInstancesCommute
    pure (.positive q(Right.add_pos_of_nonneg_of_pos $pa $pb))
  | .nonnegative (leα := leα) pa, .nonnegative pb =>
    let _a ← synthInstanceQ q(AddLeftMono $α)
    haveI' : $leα =Q ($pα).toLE := ⟨⟩
    assumeInstancesCommute
    pure (.nonnegative q(add_nonneg $pa $pb))
  | _, _ => failure

/-- The `positivity` extension which identifies expressions of the form `a * b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ * _] def evalMul : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not *"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(Mul $α)
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(HMul.hMul)
  let ra ← core zα pα? a; let rb ← core zα pα? b
  let tryProveNonzero (pα? : Option Q(PartialOrder $α))
      (pa? : Option Q($a ≠ 0)) (pb? : Option Q($b ≠ 0)) :
      MetaM (Strictness zα pα? e) := do
    let pa ← liftOption pa?
    let pb ← liftOption pb?
    let _a ← synthInstanceQ q(NoZeroDivisors $α)
    pure (.nonzero q(mul_ne_zero $pa $pb))
  let tryProveNonneg (pα : Q(PartialOrder $α)) (pa? : Option Q(0 ≤ $a)) (pb? : Option Q(0 ≤ $b)) :
      MetaM (Strictness zα (some pα) e) := do
    let pa ← liftOption pa?
    let pb ← liftOption pb?
    let _a ← synthInstanceQ q(MulZeroClass $α)
    let _a ← synthInstanceQ q(PosMulMono $α)
    assumeInstancesCommute
    pure (.nonnegative q(mul_nonneg $pa $pb))
  let tryProvePositive (pα : Q(PartialOrder $α)) (pa? : Option Q(0 < $a)) (pb? : Option Q(0 < $b)) :
      MetaM (Strictness zα (some pα) e) := do
    let pa ← liftOption pa?
    let pb ← liftOption pb?
    let _a ← synthInstanceQ q(MulZeroClass $α)
    let _a ← synthInstanceQ q(PosMulStrictMono $α)
    assumeInstancesCommute
    pure (.positive q(mul_pos $pa $pb))
  match pα? with
  | .some pα =>
    let mut result : Strictness zα (some pα) e := .none
    result ← orElse result (tryProvePositive pα ra.toPositive rb.toPositive)
    result ← orElse result (tryProveNonneg pα ra.toNonneg rb.toNonneg)
    result ← orElse result (tryProveNonzero (some pα) ra.toNonzero rb.toNonzero)
    return result
  | .none =>
    return ← catchNone <| tryProveNonzero .none ra.toNonzero rb.toNonzero

set_option backward.privateInPublic true in
private lemma int_div_self_pos {a : ℤ} (ha : 0 < a) : 0 < a / a := by
  rw [Int.ediv_self ha.ne']; exact zero_lt_one

set_option backward.privateInPublic true in
private lemma int_div_nonneg_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha.le hb

set_option backward.privateInPublic true in
private lemma int_div_nonneg_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha hb.le

set_option backward.privateInPublic true in
private lemma int_div_nonneg_of_pos_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha.le hb.le

/-- The `positivity` extension which identifies expressions of the form `a / b`,
where `a` and `b` are integers. -/
@[positivity (_ : ℤ) / (_ : ℤ)] def evalIntDiv : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q($a / $b) =>
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    let rb ← core q(inferInstance) (some q(inferInstance)) b
    assertInstancesCommute
    match ra, rb with
    | .positive (pa : Q(0 < $a)), .positive (pb : Q(0 < $b)) =>
      -- Only attempts to prove `0 < a / a`, otherwise falls back to `0 ≤ a / b`
      match ← isDefEqQ a b with
      | .defEq _ => pure (.positive q(int_div_self_pos $pa))
      | .notDefEq => pure (.nonnegative q(int_div_nonneg_of_pos_of_pos $pa $pb))
    | .positive (pa : Q(0 < $a)), .nonnegative (pb : Q(0 ≤ $b)) =>
      pure (.nonnegative q(int_div_nonneg_of_pos_of_nonneg $pa $pb))
    | .nonnegative (pa : Q(0 ≤ $a)), .positive (pb : Q(0 < $b)) =>
      pure (.nonnegative q(int_div_nonneg_of_nonneg_of_pos $pa $pb))
    | .nonnegative (pa : Q(0 ≤ $a)), .nonnegative (pb : Q(0 ≤ $b)) =>
      pure (.nonnegative q(Int.ediv_nonneg $pa $pb))
    | _, _ => pure .none
  | _, _, _ => throwError "not /"

set_option backward.privateInPublic true in
private theorem pow_zero_pos [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    (a : α) : 0 < a ^ 0 :=
  zero_lt_one.trans_le (pow_zero a).ge

private theorem pow_zero_ne_zero [Semiring α] [Nontrivial α] (a : α) : a ^ 0 ≠ 0 :=
  pow_zero a ▸ one_ne_zero

/-- The `positivity` extension which identifies expressions of the form `a ^ (0 : ℕ)`.
This extension is run in addition to the general `a ^ b` extension (they are overlapping). -/
@[positivity _ ^ (0 : ℕ)]
meta def evalPowZeroNat : PositivityExt where eval {u α} _zα _pα e := do
  let .app (.app _ (a : Q($α))) _ ← withReducible (whnf e) | throwError "not ^"
  let _a ← synthInstanceQ q(Semiring $α)
  assumeInstancesCommute
  haveI' : $e =Q $a ^ 0 := ⟨⟩
  let _a ← synthInstanceQ q(Nontrivial $α)
  let some _pα := pα? | pure (.nonzero q(pow_zero_ne_zero $a))
  let _a ← synthInstanceQ q(IsOrderedRing $α)
  pure (.positive q(pow_zero_pos $a))

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℕ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ ^ (_ : ℕ)]
meta def evalPow : PositivityExt where eval {u α} zα pα e := do
  let .app (.app _ (a : Q($α))) (b : Q(ℕ)) ← withReducible (whnf e) | throwError "not ^"
  let some pα := pα? | do
    let _a ← synthInstanceQ q(MonoidWithZero $α)
    let _a ← synthInstanceQ q(NoZeroDivisors $α)
    assumeInstancesCommute
    haveI' : $e =Q $a ^ $b := ⟨⟩
    let .nonzero nza ← core zα .none a | pure .none
    pure (.nonzero q(pow_ne_zero $b $nza))
  let _a ← synthInstanceQ q(Ring $α)
  let _a ← synthInstanceQ q(LinearOrder $α)
  let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
  assumeInstancesCommute
  let result ← catchNone do
    let .true := b.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ n where n is a literal"
    let some n := (b.getRevArg! 1).rawNatLit? | throwError "not a ^ n where n is a literal"
    guard (n % 2 = 0)
    have m : Q(ℕ) := mkRawNatLit (n / 2)
    haveI' : $b =Q 2 * $m := ⟨⟩
    haveI' : $e =Q $a ^ $b := ⟨⟩
    pure (.nonnegative q((even_two_mul $m).pow_nonneg $a))
  orElse result do
    let ra ← core zα pα a
    let ofNonneg (pa : Q(0 ≤ $a)) (_rα : Q(Semiring $α)) (_oα : Q(IsOrderedRing $α)) :
        MetaM (Strictness zα pα e) := do
      haveI' : $e =Q $a ^ $b := ⟨⟩
      assumeInstancesCommute
      pure (.nonnegative q(pow_nonneg $pa $b))
    let ofNonzero (pa : Q($a ≠ 0)) (_rα : Q(Semiring $α)) (_oα : Q(IsOrderedRing $α)) :
        MetaM (Strictness zα pα e) := do
      haveI' : $e =Q $a ^ $b := ⟨⟩
      assumeInstancesCommute
      let _a ← synthInstanceQ q(NoZeroDivisors $α)
      pure (.nonzero q(pow_ne_zero $b $pa))
    match ra with
    | .positive pa =>
      try
        let _a ← synthInstanceQ q(Semiring $α)
        let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
        assumeInstancesCommute
        haveI' : $e =Q $a ^ $b := ⟨⟩
        pure (.positive q(pow_pos $pa $b))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let rα ← synthInstanceQ q(Semiring $α)
        let oα ← synthInstanceQ q(IsOrderedRing $α)
        assumeInstancesCommute
        orElse (← catchNone (ofNonneg q(le_of_lt $pa) rα oα)) (ofNonzero q(ne_of_gt $pa) rα oα)
    | .nonnegative pa =>
        let sα ← synthInstanceQ q(Semiring $α)
        let oα ← synthInstanceQ q(IsOrderedRing $α)
        assumeInstancesCommute
        ofNonneg q($pa) q($sα) q($oα)
    | .nonzero pa =>
        let sα ← synthInstanceQ q(Semiring $α)
        let oα ← synthInstanceQ q(IsOrderedRing $α)
        ofNonzero q($pa) q($sα) q($oα)
    | .none => pure .none

set_option backward.privateInPublic true in
private theorem abs_pos_of_ne_zero {α : Type*} [AddGroup α] [LinearOrder α]
    [AddLeftMono α] {a : α} : a ≠ 0 → 0 < |a| := abs_pos.mpr

/-- The `positivity` extension which identifies expressions of the form `|a|`. -/
@[positivity |_|]
meta def evalAbs : PositivityExt where eval {_u} (α zα pα) (e : Q($α)) := do
  let ~q(@abs _ (_) (_) $a) := e | throwError "not |·|"
  let some pα := pα? | pure .none
  try
    match ← core zα (some pα) a with
    | .positive pa =>
      let pa' ← mkAppM ``abs_pos_of_pos #[pa]
      pure (.positive (ltα := q(($pα).toLT)) pa')
    | .nonzero pa =>
      let pa' ← mkAppM ``abs_pos_of_ne_zero #[pa]
      pure (.positive (ltα := q(($pα).toLT)) pa')
    | _ => pure .none
  catch _ => do
    let pa' ← mkAppM ``abs_nonneg #[a]
    pure (.nonnegative (leα := q(($pα).toLE)) pa')

set_option backward.privateInPublic true in
private theorem int_natAbs_pos {n : ℤ} (hn : 0 < n) : 0 < n.natAbs :=
  Int.natAbs_pos.mpr hn.ne'

/-- Extension for the `positivity` tactic: `Int.natAbs` is positive when its input is.
Since the output type of `Int.natAbs` is `ℕ`, the nonnegative case is handled by the default
`positivity` tactic.
-/
@[positivity Int.natAbs _]
meta def evalNatAbs : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Int.natAbs $a) =>
    let zα' : Q(Zero Int) := q(inferInstance)
    let pα' : Q(PartialOrder Int) := q(inferInstance)
    let ra ← core zα' pα' a
    match ra with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(int_natAbs_pos $pa))
    | .nonzero pa =>
      assertInstancesCommute
      pure (.positive q(Int.natAbs_pos.mpr $pa))
    | .nonnegative _pa =>
      pure .none
    | .none =>
      pure .none
  | _, _, _ => throwError "not Int.natAbs"

/-- Extension for the `positivity` tactic: `Nat.cast` is always non-negative,
and positive when its input is. -/
@[positivity Nat.cast _]
meta def evalNatCast : PositivityExt where eval {u α} _zα _pα e := do
  let ~q(@Nat.cast _ (_) ($a : ℕ)) := e | throwError "not Nat.cast"
  let zα' : Q(Zero Nat) := q(inferInstance)
  let (_i1 : Q(AddMonoidWithOne $α)) ← synthInstanceQ q(AddMonoidWithOne $α)
  let some _pα := pα? | do
    let (_cz : Q(CharZero $α)) ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    match ← core zα' .none a with
    | .nonzero nza => pure (.nonzero q(Nat.cast_ne_zero.2 $nza))
    | _ => pure .none
  let pα' : Q(PartialOrder Nat) := q(inferInstance)
  let (_i2 : Q(AddLeftMono $α)) ← synthInstanceQ q(AddLeftMono $α)
  let (_i3 : Q(ZeroLEOneClass $α)) ← synthInstanceQ q(ZeroLEOneClass $α)
  assumeInstancesCommute
  match ← core zα' pα' a with
  | .positive pa =>
    let _nz ← synthInstanceQ q(NeZero (1 : $α))
    assumeInstancesCommute
    pure (.positive q(Nat.cast_pos'.2 $pa))
  | _ =>
    pure (.nonnegative q(Nat.cast_nonneg' _))

/-- Extension for the `positivity` tactic: `Int.cast` is positive (resp. non-negative)
if its input is. -/
@[positivity Int.cast _]
meta def evalIntCast : PositivityExt where eval {u α} _zα _pα e := do
  let ~q(@Int.cast _ (_) ($a : ℤ)) := e | throwError "not Int.cast"
  let zα' : Q(Zero Int) := q(inferInstance)
  let pα' : Q(PartialOrder Int) := q(inferInstance)
  let ra ← core zα' pα' a
  match ra, pα? with
  | .positive pa, some _ =>
    let _rα ← synthInstanceQ q(Ring $α)
    let _oα ← synthInstanceQ q(IsOrderedRing $α)
    let _nt ← synthInstanceQ q(Nontrivial $α)
    assumeInstancesCommute
    pure (.positive q(Int.cast_pos.mpr $pa))
  | .nonnegative pa, some _ =>
    let _rα ← synthInstanceQ q(Ring $α)
    let _oα ← synthInstanceQ q(IsOrderedRing $α)
    let _nt ← synthInstanceQ q(Nontrivial $α)
    assumeInstancesCommute
    pure (.nonnegative q(Int.cast_nonneg $pa))
  | .nonzero pa, _ =>
    let _oα ← synthInstanceQ q(AddGroupWithOne $α)
    let _nt ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    pure (.nonzero q(Int.cast_ne_zero.mpr $pa))
  | _ , _ =>
    pure .none

/-- Extension for `Nat.succ`. -/
@[positivity Nat.succ _]
meta def evalNatSucc : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.succ $a) =>
    assertInstancesCommute
    pure (.positive q(Nat.succ_pos $a))
  | _, _, _ => throwError "not Nat.succ"

/-- Extension for `PNat.val`. -/
@[positivity PNat.val _]
meta def evalPNatVal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(PNat.val $a) =>
    assertInstancesCommute
    pure (.positive q(PNat.pos $a))
  | _, _, _ => throwError "not PNat.val"

/-- Extension for `Nat.factorial`. -/
@[positivity Nat.factorial _]
meta def evalFactorial : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.factorial $a) =>
    assertInstancesCommute
    pure (.positive q(Nat.factorial_pos $a))
  | _, _, _ => throwError "failed to match Nat.factorial"

/-- Extension for `Nat.ascFactorial`. -/
@[positivity Nat.ascFactorial _ _]
meta def evalAscFactorial : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.ascFactorial ($n + 1) $k) =>
    assertInstancesCommute
    pure (.positive q(Nat.ascFactorial_pos $n $k))
  | _, _, _ => throwError "failed to match Nat.ascFactorial"

/-- Extension for `Nat.gcd`.
Uses positivity of the left term, if available, then tries the right term.

The implementation relies on the fact that `Positivity.core` on `ℕ` never returns `nonzero`. -/
@[positivity Nat.gcd _ _]
meta def evalNatGCD : PositivityExt where eval {u α} z p e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.gcd $a $b) =>
    assertInstancesCommute
    match ← core z p a with
    | .positive pa =>
      assertInstancesCommute
      return .positive q(Nat.gcd_pos_of_pos_left $b $pa)
    | _ =>
      match ← core z p b with
      | .positive pb =>
        assertInstancesCommute
        return .positive q(Nat.gcd_pos_of_pos_right $a $pb)
      | _ => failure
  | _, _, _ => throwError "not Nat.gcd"

/-- Extension for `Nat.lcm`. -/
@[positivity Nat.lcm _ _]
meta def evalNatLCM : PositivityExt where eval {u α} z p e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.lcm $a $b) =>
    assertInstancesCommute
    match ← core z p a with
    | .positive pa =>
      assertInstancesCommute
      match ← core z p b with
      | .positive pb =>
        assertInstancesCommute
        return .positive q(Nat.lcm_pos $pa $pb)
      | _ => failure
    | _ => failure
  | _, _, _ => throwError "not Nat.lcm"

/-- Extension for `Nat.sqrt`. -/
@[positivity Nat.sqrt _]
meta def evalNatSqrt : PositivityExt where eval {u α} z p e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.sqrt $n) =>
    assumeInstancesCommute
    match ← core z p n with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Nat.sqrt_pos.mpr $pa)
    | _ => failure
  | _, _, _ => throwError "not Nat.sqrt"

/-- Extension for `Int.gcd`.
Uses positivity of the left term, if available, then tries the right term. -/
@[positivity Int.gcd _ _]
meta def evalIntGCD : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Int.gcd $a $b) =>
    let z ← synthInstanceQ (q(Zero ℤ) : Q(Type))
    let p ← synthInstanceQ (q(PartialOrder ℤ) : Q(Type))
    assertInstancesCommute
    match (← catchNone (core z (some p) a)).toNonzero with
    | some na => return .positive q(Int.gcd_pos_of_ne_zero_left $b $na)
    | none =>
      match (← core z (some p) b).toNonzero with
      | some nb => return .positive q(Int.gcd_pos_of_ne_zero_right $a $nb)
      | none => failure
  | _, _, _ => throwError "not Int.gcd"

/-- Extension for `Int.lcm`. -/
@[positivity Int.lcm _ _]
meta def evalIntLCM : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Int.lcm $a $b) =>
    let z ← synthInstanceQ (q(Zero ℤ) : Q(Type))
    let p ← synthInstanceQ (q(PartialOrder ℤ) : Q(Type))
    assertInstancesCommute
    match (← core z (some p) a).toNonzero with
    | some na =>
      match (← core z (some p) b).toNonzero with
      | some nb => return .positive q(Int.lcm_pos $na $nb)
      | _ => failure
    | _ => failure
  | _, _, _ => throwError "not Int.lcm"

section NNRat
open NNRat

set_option backward.privateInPublic true in
private alias ⟨_, NNRat.num_pos_of_pos⟩ := num_pos
set_option backward.privateInPublic true in
private alias ⟨_, NNRat.num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `NNRat.num q`,
such that `positivity` successfully recognises `q`. -/
@[positivity NNRat.num _]
meta def evalNNRatNum : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(NNRat.num $a) =>
    let zα : Q(Zero ℚ≥0) := q(inferInstance)
    let pα : Q(PartialOrder ℚ≥0) := q(inferInstance)
    trace[Tactic.positivity] "I'm evalNNRatNum: {e}"
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(NNRat.num_pos_of_pos $pa)
    | .nonzero pa => return .nonzero q(NNRat.num_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not NNRat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity NNRat.den _]
meta def evalNNRatDen : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(NNRat.den $a) =>
    assumeInstancesCommute
    return .positive q(den_pos $a)
  | _, _, _ => throwError "not NNRat.den"

variable {q : ℚ≥0}

set_option trace.Tactic.positivity true
set_option trace.Tactic.positivity.failure true

example (hq : 0 < q) : 0 < q.num := by positivity
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.den := by positivity

end NNRat

open Rat

set_option backward.privateInPublic true in
private alias ⟨_, num_pos_of_pos⟩ := num_pos
set_option backward.privateInPublic true in
private alias ⟨_, num_nonneg_of_nonneg⟩ := num_nonneg
set_option backward.privateInPublic true in
private alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `Rat.num a`,
such that `positivity` successfully recognises `a`. -/
@[positivity Rat.num _]
meta def evalRatNum : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(Rat.num $a) =>
    let zα : Q(Zero ℚ) := q(inferInstance)
    let pα : Q(PartialOrder ℚ) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      assumeInstancesCommute
      pure <| .positive q(num_pos_of_pos $pa)
    | .nonnegative pa =>
      assumeInstancesCommute
      pure <| .nonnegative q(num_nonneg_of_nonneg $pa)
    | .nonzero pa => pure <| .nonzero q(num_ne_zero_of_ne_zero $pa)
    | .none => pure .none
  | _, _ => throwError "not Rat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity Rat.den _]
meta def evalRatDen : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Rat.den $a) =>
    assumeInstancesCommute
    pure <| .positive q(den_pos $a)
  | _, _ => throwError "not Rat.num"

/-- Extension for `posPart`. `a⁺` is always nonnegative, and positive if `a` is. -/
@[positivity _⁺]
meta def evalPosPart : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@posPart _ $instαpospart $a) =>
    let _instαlat ← synthInstanceQ q(Lattice $α)
    let _instαgrp ← synthInstanceQ q(AddGroup $α)
    assertInstancesCommute
    -- FIXME: There seems to be a bug in `Positivity.core` that makes it fail (instead of returning
    -- `.none`) here sometimes. See e.g. the first test for `posPart`. This is why we need
    -- `catchNone`
    match ← catchNone (core zα pα a) with
    | .positive pf =>
      assumeInstancesCommute
      return .positive q(posPart_pos $pf)
    | _ => return .nonnegative q(posPart_nonneg $a)
  | _ => throwError "not `posPart`"

/-- Extension for `negPart`. `a⁻` is always nonnegative. -/
@[positivity _⁻]
meta def evalNegPart : PositivityExt where eval {u α} _ _ e := do
  match e with
  | ~q(@negPart _ $instαnegpart $a) =>
    let _instαlat ← synthInstanceQ q(Lattice $α)
    let _instαgrp ← synthInstanceQ q(AddGroup $α)
    assertInstancesCommute
    return .nonnegative q(negPart_nonneg $a)
  | _ => throwError "not `negPart`"

/-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
@[positivity DFunLike.coe _ _]
meta def evalMap : PositivityExt where eval {_ β} _ _ e := do
  let .app (.app _ f) a ← whnfR e
    | throwError "not ↑f · where f is of NonnegHomClass"
  let some pβ := pβ? | throwError "not PartialOrder"
  let pa ← mkAppOptM ``apply_nonneg #[none, none, β, none, none, none, none, f, a]
  pure (.nonnegative (leα := pβ) pa)

end Positivity

end Meta

end Mathlib
