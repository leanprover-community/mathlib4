/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.Positivity.Core
import Qq

/-!
## `positivity` core extensions

This file sets up the basic `positivity` extensions tagged with the `@[positivity]` attribute.
-/

set_option autoImplicit true

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section ite
variable [Zero α] (p : Prop) [Decidable p] {a b : α}

private lemma ite_pos [LT α] (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by
  by_cases p <;> simp [*]

private lemma ite_nonneg [LE α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by
  by_cases p <;> simp [*]

private lemma ite_nonneg_of_pos_of_nonneg [Preorder α] (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ ite p a b :=
  ite_nonneg _ ha.le hb

private lemma ite_nonneg_of_nonneg_of_pos [Preorder α] (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ ite p a b :=
  ite_nonneg _ ha hb.le

private lemma ite_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by by_cases p <;> simp [*]

private lemma ite_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) :
    ite p a b ≠ 0 :=
  ite_ne_zero _ ha.ne' hb

private lemma ite_ne_zero_of_ne_zero_of_pos [Preorder α] (ha : a ≠ 0) (hb : 0 < b) :
    ite p a b ≠ 0 :=
  ite_ne_zero _ ha hb.ne'

end ite

/-- The `positivity` extension which identifies expressions of the form `ite p a b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity ite _ _ _] def evalIte : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (.app (.app f (p : Q(Prop))) (_ : Q(Decidable $p))) (a : Q($α))) (b : Q($α))
    ← withReducible (whnf e) | throwError "not ite"
  haveI' : $e =Q ite $p $a $b := ⟨⟩
  let ra ← core zα pα a; let rb ← core zα pα b
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(ite (α := $α))
  match ra, rb with
  | .positive pa, .positive pb =>
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
variable [LinearOrder R] {a b c : R}

private lemma le_min_of_lt_of_le (ha : a < b) (hb : a ≤ c) : a ≤ min b c := le_min ha.le hb
private lemma le_min_of_le_of_lt (ha : a ≤ b) (hb : a < c) : a ≤ min b c := le_min ha hb.le
private lemma min_ne (ha : a ≠ c) (hb : b ≠ c) : min a b ≠ c := by
  rw [min_def]; split_ifs <;> assumption

private lemma min_ne_of_ne_of_lt (ha : a ≠ c) (hb : c < b) : min a b ≠ c := min_ne ha hb.ne'
private lemma min_ne_of_lt_of_ne (ha : c < a) (hb : b ≠ c) : min a b ≠ c := min_ne ha.ne' hb

private lemma max_ne (ha : a ≠ c) (hb : b ≠ c) : max a b ≠ c := by
  rw [max_def]; split_ifs <;> assumption

end LinearOrder

/-- The `positivity` extension which identifies expressions of the form `min a b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity min _ _] def evalMin : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not min"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ (q(LinearOrder $α) : Q(Type u))
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(min)
  match ← core zα pα a, ← core zα pα b with
  | .positive pa, .positive pb => pure (.positive q(lt_min $pa $pb))
  | .positive pa, .nonnegative pb => pure (.nonnegative q(le_min_of_lt_of_le $pa $pb))
  | .nonnegative pa, .positive pb => pure (.nonnegative q(le_min_of_le_of_lt $pa $pb))
  | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(le_min $pa $pb))
  | .positive pa, .nonzero pb => pure (.nonzero q(min_ne_of_lt_of_ne $pa $pb))
  | .nonzero pa, .positive pb => pure (.nonzero q(min_ne_of_ne_of_lt $pa $pb))
  | .nonzero pa, .nonzero pb => pure (.nonzero q(min_ne $pa $pb))
  | _, _ => pure .none

/-- Extension for the `max` operator. The `max` of two numbers is nonnegative if at least one
is nonnegative, strictly positive if at least one is positive, and nonzero if both are nonzero. -/
@[positivity max _ _] def evalMax : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not max"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ (q(LinearOrder $α) : Q(Type u))
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(max)
  let result : Strictness zα pα e ← catchNone do
    let ra ← core zα pα a
    match ra with
    | .positive pa => pure (.positive q(lt_max_of_lt_left $pa))
    | .nonnegative pa => pure (.nonnegative q(le_max_of_le_left $pa))
    -- If `a ≠ 0`, we might prove `max a b ≠ 0` if `b ≠ 0` but we don't want to evaluate
    -- `b` before having ruled out `0 < a`, for performance. So we do that in the second branch
    -- of the `orElse'`.
    | _ => pure .none
  orElse result do
    let rb ← core zα pα b
    match rb with
    | .positive pb => pure (.positive q(lt_max_of_lt_right $pb))
    | .nonnegative pb => pure (.nonnegative q(le_max_of_le_right $pb))
    | .nonzero pb => do
      match ← core zα pα a with
      | .nonzero pa => pure (.nonzero q(max_ne $pa $pb))
      | _ => pure .none
    | _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a + b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ + _] def evalAdd : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not +"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ (q(AddZeroClass $α) : Q(Type u))
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(HAdd.hAdd)
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (·+·) (·<·)) : Q(Prop))
    pure (.positive q(add_pos $pa $pb))
  | .positive pa, .nonnegative pb =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (swap (·+·)) (·<·)) : Q(Prop))
    pure (.positive q(lt_add_of_pos_of_le $pa $pb))
  | .nonnegative pa, .positive pb =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (·+·) (·<·)) : Q(Prop))
    pure (.positive q(lt_add_of_le_of_pos $pa $pb))
  | .nonnegative pa, .nonnegative pb =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (·+·) (·≤·)) : Q(Prop))
    pure (.nonnegative q(add_nonneg $pa $pb))
  | _, _ => failure

private theorem mul_nonneg_of_pos_of_nonneg [OrderedSemiring α] {a b : α}
    (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg ha.le hb

private theorem mul_nonneg_of_nonneg_of_pos [OrderedSemiring α] {a b : α}
    (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b :=
  mul_nonneg ha hb.le

private theorem mul_ne_zero_of_ne_zero_of_pos [OrderedSemiring α] [NoZeroDivisors α]
    {a b : α} (ha : a ≠ 0) (hb : 0 < b) : a * b ≠ 0 :=
  mul_ne_zero ha (ne_of_gt hb)

private theorem mul_ne_zero_of_pos_of_ne_zero [OrderedSemiring α] [NoZeroDivisors α]
    {a b : α} (ha : 0 < a) (hb : b ≠ 0) : a * b ≠ 0 :=
  mul_ne_zero (ne_of_gt ha) hb

/-- The `positivity` extension which identifies expressions of the form `a * b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ * _] def evalMul : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not *"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ q(StrictOrderedSemiring $α)
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(HMul.hMul)
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb => pure (.positive q(mul_pos $pa $pb))
  | .positive pa, .nonnegative pb => pure (.nonnegative q(mul_nonneg_of_pos_of_nonneg $pa $pb))
  | .nonnegative pa, .positive pb => pure (.nonnegative q(mul_nonneg_of_nonneg_of_pos $pa $pb))
  | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(mul_nonneg $pa $pb))
  | .positive pa, .nonzero pb =>
    let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
    pure (.nonzero q(mul_ne_zero_of_pos_of_ne_zero $pa $pb))
  | .nonzero pa, .positive pb =>
    let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
    pure (.nonzero q(mul_ne_zero_of_ne_zero_of_pos $pa $pb))
  | .nonzero pa, .nonzero pb =>
    let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
    pure (.nonzero q(mul_ne_zero $pa $pb))
  | _, _ => pure .none


private lemma int_div_self_pos {a : ℤ} (ha : 0 < a) : 0 < a / a := by
  rw [Int.ediv_self ha.ne']; exact zero_lt_one

private lemma int_div_nonneg_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha.le hb

private lemma int_div_nonneg_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha hb.le

private lemma int_div_nonneg_of_pos_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.ediv_nonneg ha.le hb.le

/-- The `positivity` extension which identifies expressions of the form `a / b`,
where `a` and `b` are integers. -/
@[positivity (_ : ℤ) / (_ : ℤ)] def evalIntDiv : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q($a / $b) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    let rb ← core q(inferInstance) q(inferInstance) b
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

private theorem pow_zero_pos [OrderedSemiring α] [Nontrivial α] (a : α) : 0 < a ^ 0 :=
  zero_lt_one.trans_le (pow_zero a).ge

/-- The `positivity` extension which identifies expressions of the form `a ^ (0:ℕ)`.
This extension is run in addition to the general `a ^ b` extension (they are overlapping). -/
@[positivity (_ : α) ^ (0:ℕ)]
def evalPowZeroNat : PositivityExt where eval {u α} _zα _pα e := do
  let .app (.app _ (a : Q($α))) _ ← withReducible (whnf e) | throwError "not ^"
  _ ← synthInstanceQ (q(OrderedSemiring $α) : Q(Type u))
  _ ← synthInstanceQ (q(Nontrivial $α) : Q(Prop))
  pure (.positive (q(pow_zero_pos $a) : Expr))

set_option linter.deprecated false in
/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℕ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity (_ : α) ^ (_ : ℕ)]
def evalPow : PositivityExt where eval {u α} zα pα e := do
  let .app (.app _ (a : Q($α))) (b : Q(ℕ)) ← withReducible (whnf e) | throwError "not ^"
  let result ← catchNone do
    let .true := b.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ n where n is a literal"
    let some n := (b.getRevArg! 1).rawNatLit? | throwError "not a ^ n where n is a literal"
    guard (n % 2 = 0)
    have m : Q(ℕ) := mkRawNatLit (n / 2)
    haveI' : $b =Q bit0 $m := ⟨⟩
    let _a ← synthInstanceQ q(LinearOrderedRing $α)
    haveI' : $e =Q $a ^ $b := ⟨⟩
    assumeInstancesCommute
    pure (.nonnegative q(pow_bit0_nonneg $a $m))
  orElse result do
    let ra ← core zα pα a
    let ofNonneg (pa : Q(0 ≤ $a)) (_oα : Q(OrderedSemiring $α)) : MetaM (Strictness zα pα e) := do
      haveI' : $e =Q $a ^ $b := ⟨⟩
      assumeInstancesCommute
      pure (.nonnegative q(pow_nonneg $pa $b))
    let ofNonzero (pa : Q($a ≠ 0)) (_oα : Q(OrderedSemiring $α)) : MetaM (Strictness zα pα e) := do
      haveI' : $e =Q $a ^ $b := ⟨⟩
      assumeInstancesCommute
      let _a ← synthInstanceQ q(NoZeroDivisors $α)
      pure (.nonzero q(pow_ne_zero $b $pa))
    match ra with
    | .positive pa =>
      try
        let _a ← synthInstanceQ (q(StrictOrderedSemiring $α) : Q(Type u))
        haveI' : $e =Q $a ^ $b := ⟨⟩
        assumeInstancesCommute
        pure (.positive q(pow_pos $pa $b))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let oα ← synthInstanceQ q(OrderedSemiring $α)
        orElse (← catchNone (ofNonneg q(le_of_lt $pa) oα)) (ofNonzero q(ne_of_gt $pa) oα)
    | .nonnegative pa => ofNonneg pa (← synthInstanceQ (_ : Q(Type u)))
    | .nonzero pa => ofNonzero pa (← synthInstanceQ (_ : Q(Type u)))
    | .none => pure .none

private theorem abs_pos_of_ne_zero {α : Type*} [AddGroup α] [LinearOrder α]
    [CovariantClass α α (·+·) (·≤·)] {a : α} : a ≠ 0 → 0 < |a| := abs_pos.mpr

/-- The `positivity` extension which identifies expressions of the form `|a|`. -/
@[positivity |(_ : α)|]
def evalAbs : PositivityExt where eval {u} (α : Q(Type u)) zα pα (e : Q($α)) := do
  let ~q(@abs _ (_) (_) $a) := e | throwError "not |·|"
  try
    match ← core zα pα a with
    | .positive pa =>
      let pa' ← mkAppM ``abs_pos_of_pos #[pa]
      pure (.positive pa')
    | .nonzero pa =>
      let pa' ← mkAppM ``abs_pos_of_ne_zero #[pa]
      pure (.positive pa')
    | _ => pure .none
  catch _ => do
    let pa' ← mkAppM ``abs_nonneg #[a]
    pure (.nonnegative pa')

private theorem int_natAbs_pos {n : ℤ} (hn : 0 < n) : 0 < n.natAbs :=
  Int.natAbs_pos.mpr hn.ne'

/-- Extension for the `positivity` tactic: `Int.natAbs` is positive when its input is.
Since the output type of `Int.natAbs` is `ℕ`, the nonnegative case is handled by the default
`positivity` tactic.
-/
@[positivity Int.natAbs _]
def evalNatAbs : PositivityExt where eval {u α} _zα _pα e := do
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
def evalNatCast : PositivityExt where eval {u α} _zα _pα e := do
  let ~q(@Nat.cast _ (_) ($a : ℕ)) := e | throwError "not Nat.cast"
  let zα' : Q(Zero Nat) := q(inferInstance)
  let pα' : Q(PartialOrder Nat) := q(inferInstance)
  let (_oα : Q(OrderedSemiring $α)) ← synthInstanceQ q(OrderedSemiring $α)
  assumeInstancesCommute
  match ← core zα' pα' a with
  | .positive pa =>
    let _nt ← synthInstanceQ q(Nontrivial $α)
    pure (.positive q(Nat.cast_pos.mpr $pa))
  | _ =>
    pure (.nonnegative q(Nat.cast_nonneg _))

/-- Extension for the `positivity` tactic: `Int.cast` is positive (resp. non-negative)
if its input is. -/
@[positivity Int.cast _]
def evalIntCast : PositivityExt where eval {u α} _zα _pα e := do
  let ~q(@Int.cast _ (_) ($a : ℤ)) := e | throwError "not Int.cast"
  let zα' : Q(Zero Int) := q(inferInstance)
  let pα' : Q(PartialOrder Int) := q(inferInstance)
  let ra ← core zα' pα' a
  match ra with
  | .positive pa =>
    let _oα ← synthInstanceQ (q(OrderedRing $α) : Q(Type u))
    let _nt ← synthInstanceQ q(Nontrivial $α)
    assumeInstancesCommute
    pure (.positive q(Int.cast_pos.mpr $pa))
  | .nonnegative pa =>
    let _oα ← synthInstanceQ q(OrderedRing $α)
    let _nt ← synthInstanceQ q(Nontrivial $α)
    assumeInstancesCommute
    pure (.nonnegative q(Int.cast_nonneg.mpr $pa))
  | .nonzero pa =>
    let _oα ← synthInstanceQ (q(AddGroupWithOne $α) : Q(Type $u))
    let _nt ← synthInstanceQ (q(CharZero $α) : Q(Prop))
    assumeInstancesCommute
    pure (.nonzero q(Int.cast_ne_zero.mpr $pa))
  | .none =>
    pure .none

/-- Extension for `Nat.succ`. -/
@[positivity Nat.succ _]
def evalNatSucc : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.succ $a) =>
    assertInstancesCommute
    pure (.positive q(Nat.succ_pos $a))
  | _, _, _ => throwError "not Nat.succ"

/-- Extension for `PNat.val`. -/
@[positivity PNat.val _]
def evalPNatVal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(PNat.val $a) =>
    assertInstancesCommute
    pure (.positive q(PNat.pos $a))
  | _, _, _ => throwError "not PNat.val"

/-- Extension for `Nat.factorial`. -/
@[positivity Nat.factorial _]
def evalFactorial : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.factorial $a) =>
    assertInstancesCommute
    pure (.positive q(Nat.factorial_pos $a))
  | _, _, _ => throwError "failed to match Nat.factorial"

/-- Extension for `Nat.ascFactorial`. -/
@[positivity Nat.ascFactorial _ _]
def evalAscFactorial : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.ascFactorial ($n + 1) $k) =>
    assertInstancesCommute
    pure (.positive q(Nat.ascFactorial_pos $n $k))
  | _, _, _ => throwError "failed to match Nat.ascFactorial"

section NNRat
open NNRat

private alias ⟨_, NNRat.num_pos_of_pos⟩ := num_pos
private alias ⟨_, NNRat.num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `NNRat.num q`,
such that `positivity` successfully recognises `q`. -/
@[positivity NNRat.num _]
def evalNNRatNum : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(NNRat.num $a) =>
    let zα : Q(Zero ℚ≥0) := q(inferInstance)
    let pα : Q(PartialOrder ℚ≥0) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => return .positive q(NNRat.num_pos_of_pos $pa)
    | .nonzero pa => return .nonzero q(NNRat.num_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not NNRat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity NNRat.den _]
def evalNNRatDen : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(NNRat.den $a) =>
    assumeInstancesCommute
    return .positive q(den_pos $a)
  | _, _, _ => throwError "not NNRat.den"

variable {q : ℚ≥0}

example (hq : 0 < q) : 0 < q.num := by positivity
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.den := by positivity

end NNRat

open Rat

private alias ⟨_, num_pos_of_pos⟩ := num_pos
private alias ⟨_, num_nonneg_of_nonneg⟩ := num_nonneg
private alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `Rat.num a`,
such that `positivity` successfully recognises `a`. -/
@[positivity Rat.num _]
def evalRatNum : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(Rat.num $a) =>
    let zα : Q(Zero ℚ) := q(inferInstance)
    let pα : Q(PartialOrder ℚ) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure $ .positive q(num_pos_of_pos $pa)
    | .nonnegative pa => pure $ .nonnegative q(num_nonneg_of_nonneg $pa)
    | .nonzero pa => pure $ .nonzero q(num_ne_zero_of_ne_zero $pa)
    | .none => pure .none
  | _, _ => throwError "not Rat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity Rat.den _]
def evalRatDen : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Rat.den $a) =>
    assumeInstancesCommute
    pure $ .positive q(den_pos $a)
  | _, _ => throwError "not Rat.num"

/-- Extension for `posPart`. `a⁺` is always nonegative, and positive if `a` is. -/
@[positivity _⁺]
def evalPosPart : PositivityExt where eval zα pα e := do
  match e with
  | ~q(@posPart _ $instαlat $instαgrp $a) =>
    assertInstancesCommute
    -- FIXME: There seems to be a bug in `Positivity.core` that makes it fail (instead of returning
    -- `.none`) here sometimes. See eg the first test for `posPart`. This is why we need `catchNone`
    match ← catchNone (core zα pα a) with
    | .positive pf => return .positive q(posPart_pos $pf)
    | _ => return .nonnegative q(posPart_nonneg $a)
  | _ => throwError "not `posPart`"

/-- Extension for `negPart`. `a⁻` is always nonegative. -/
@[positivity _⁻]
def evalNegPart : PositivityExt where eval _ _ e := do
  match e with
  | ~q(@negPart _ $instαlat $instαgrp $a) =>
    assertInstancesCommute
    return .nonnegative q(negPart_nonneg $a)
  | _ => throwError "not `negPart`"
