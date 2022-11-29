/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
import Std.Lean.Parser
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Clear!
import Mathlib.Logic.Nontrivial
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring
import Mathlib.Algebra.Order.Ring.Lemmas
import Qq.Match

/-!
## `positivity` core extensions

This file sets up the basic `positivity` extensions tagged with the `@[positivity]` attribute.
-/

section Nonsense
open Function
-- TODO: these classes are mostly nonsense stubs which should be replaced by the real things
-- when the theory files are ready

instance [OrderedSemiring α] : PosMulMono α :=
  ⟨fun ⟨_, ha⟩ _ _ h => OrderedSemiring.mul_le_mul_of_nonneg_left _ _ _ h ha⟩

instance [StrictOrderedSemiring α] : PosMulStrictMono α :=
  ⟨fun ⟨_, ha⟩ _ _ h => StrictOrderedSemiring.mul_lt_mul_of_pos_left _ _ _ h ha⟩

theorem mul_nonneg_of_pos_of_nonneg [OrderedSemiring α] {a b : α}
    (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg ha.le hb
theorem mul_nonneg_of_nonneg_of_pos [OrderedSemiring α] {a b : α}
    (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b :=
  mul_nonneg ha hb.le

class OrderedMonoidWithZero (α : Type _) extends PartialOrder α, MonoidWithZero α where
  /-- In an ordered monoid with zero, `0 ≤ 1`. -/
  zero_le_one : (0 : α) ≤ 1

lemma pow_zero_pos [OrderedMonoidWithZero α] [Nontrivial α] (a : α) : 0 < a ^ 0 :=
  (OrderedMonoidWithZero.zero_le_one.lt_of_ne (zero_ne_one (α := α))).trans_le (pow_zero a).ge

theorem pow_bit0_nonneg [LinearOrderedRing α] (a : α) (n : ℕ) : 0 ≤ a ^ (2 * n) := by
  have : 2 = 1 + 1 := rfl
  have mul_nonneg_of_nonpos_of_nonpos : ∀ a b : α, a ≤ 0 → b ≤ 0 → (0 : α) ≤ a * b :=
    fun a b ha hb => by
      rcases ha.eq_or_lt with rfl|ha
      · simp
      rcases hb.eq_or_lt with rfl|hb
      · simp
      · rw [←Left.neg_pos_iff] at ha hb
        simpa using (mul_pos ha hb).le
  have mul_self_nonneg : ∀ a : α, (0 : α) ≤ a * a := fun a => (le_total 0 a).elim
    (fun h => mul_nonneg h h)
    (fun h => mul_nonneg_of_nonpos_of_nonpos _ _ h h)
  rw [this, add_mul, one_mul, pow_add]
  exact mul_self_nonneg _

instance [StrictOrderedSemiring α] : OrderedMonoidWithZero α :=
  { __ := inferInstanceAs (StrictOrderedSemiring α) }

instance [StrictOrderedSemiring α] : MulPosStrictMono α :=
  ⟨fun ⟨_, ha⟩ _ _ h => StrictOrderedSemiring.mul_lt_mul_of_pos_right _ _ _ h ha⟩

theorem pow_pos [StrictOrderedSemiring α] {a : α} (H : 0 < a) (n : ℕ) : 0 < a ^ n := by
  have : Nontrivial α := ⟨_, _, H.ne⟩
  induction' n with n IH
  · exact pow_zero_pos _
  · rw [pow_succ, ←zero_mul (a ^ n)]
    exact mul_lt_mul_of_pos_right H IH

theorem pow_nonneg [OrderedSemiring α] {a : α} (H : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n := by
  induction' n with n IH
  · simpa using OrderedSemiring.zero_le_one (α := α)
  · rw [pow_succ]
    exact mul_nonneg H IH

theorem pow_ne_zero [MonoidWithZero M] [NoZeroDivisors M] {a : M} (n : ℕ) (h : a ≠ 0) :
    a ^ n ≠ 0 := by
  refine mt (fun H => ?_) h
  induction' n with n IH
  · rw [pow_zero] at H
    rw [←mul_one a, H, mul_zero]
  · rw [pow_succ, mul_eq_zero] at H
    exact H.casesOn id IH

lemma mul_ne_zero_of_ne_zero_of_pos [Zero α] [Mul α] [PartialOrder α] [NoZeroDivisors α]
    {a b : α} (ha : a ≠ 0) (hb : 0 < b) : a * b ≠ 0 :=
  mul_ne_zero ha (ne_of_gt hb)

lemma mul_ne_zero_of_pos_of_ne_zero [Zero α] [Mul α] [PartialOrder α] [NoZeroDivisors α]
    {a b : α} (ha : 0 < a) (hb : b ≠ 0) : a * b ≠ 0 :=
  mul_ne_zero (ne_of_gt ha) hb

end Nonsense

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- The `positivity` extension which identifies expressions of the form `a + b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ + _, Add.add _ _] def evalAdd : PositivityExt where eval {u α} zα pα e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | throwError "not +"
  let ra ← core zα pα a; let rb ← core zα pα b
  let _a ← synthInstanceQ (q(AddZeroClass $α) : Q(Type u))
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HAdd.hAdd (α := $α))
  match ra, rb with
  | .positive (pa : Q(@Zero.zero _ AddZeroClass.toZero < $a)),
    .positive (pb : Q(@Zero.zero _ AddZeroClass.toZero < $b)) =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (·+·) (·<·)) : Q(Prop))
    pure (.positive (q(add_pos $pa $pb) : Expr))
  | .positive (pa : Q(@Zero.zero _ AddZeroClass.toZero < $a)),
    .nonnegative (pb : Q(@Zero.zero _ AddZeroClass.toZero ≤ $b)) =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (swap (·+·)) (·<·)) : Q(Prop))
    pure (.positive (q(lt_add_of_pos_of_le $pa $pb) : Expr))
  | .nonnegative (pa : Q(@Zero.zero _ AddZeroClass.toZero ≤ $a)),
    .positive (pb : Q(@Zero.zero _ AddZeroClass.toZero < $b)) =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (·+·) (·<·)) : Q(Prop))
    pure (.positive (q(lt_add_of_le_of_pos $pa $pb) : Expr))
  | .nonnegative (pa : Q(@Zero.zero _ AddZeroClass.toZero ≤ $a)),
    .nonnegative (pb : Q(@Zero.zero _ AddZeroClass.toZero ≤ $b)) =>
    let _a ← synthInstanceQ (q(CovariantClass $α $α (·+·) (·≤·)) : Q(Prop))
    pure (.nonnegative (q(add_nonneg $pa $pb) : Expr))
  | _, _ => failure

/-- The `positivity` extension which identifies expressions of the form `a * b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ * _, Mul.mul _ _] def evalMul : PositivityExt where eval {u α} zα pα e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← withReducible (whnf e) | throwError "not *"
  let ra ← core zα pα a; let rb ← core zα pα b
  let _a ← synthInstanceQ (q(StrictOrderedSemiring $α) : Q(Type u))
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HMul.hMul (α := $α))
  -- FIXME: this code is pretty horrible, we should improve Qq or something
  match ra, rb with
  | .positive pa, .positive pb =>
    have pa' : Q(by clear! «$zα» «$pα»; exact 0 < $a) := pa
    have pb' : Q(by clear! «$zα» «$pα»; exact 0 < $b) := pb
    pure (.positive (by clear! zα pα; exact q(@mul_pos $α _ _ _ _ _ $pa' $pb') : Expr))
  | .positive pa, .nonnegative pb =>
    have pa' : Q(by clear! «$zα» «$pα»; exact 0 < $a) := pa
    have pb' : Q(by clear! «$zα» «$pα»; exact 0 ≤ $b) := pb
    pure (.nonnegative (q(mul_nonneg_of_pos_of_nonneg $pa' $pb') : Expr))
  | .nonnegative pa, .positive pb =>
    have pa' : Q(by clear! «$zα» «$pα»; exact 0 ≤ $a) := pa
    have pb' : Q(by clear! «$zα» «$pα»; exact 0 < $b) := pb
    pure (.nonnegative (q(mul_nonneg_of_nonneg_of_pos $pa' $pb') : Expr))
  | .nonnegative pa, .nonnegative pb =>
    have pa' : Q(by clear! «$zα» «$pα»; exact 0 ≤ $a) := pa
    have pb' : Q(by clear! «$zα» «$pα»; exact 0 ≤ $b) := pb
    pure (.nonnegative (by clear! zα pα; exact q(mul_nonneg $pa' $pb') : Expr))
  | .positive pa, .nonzero pb =>
    let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
    pure (.nonzero (q(mul_ne_zero_of_pos_of_ne_zero $pa $pb) : Expr))
  | .nonzero pa, .positive pb =>
    let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
    pure (.nonzero (q(mul_ne_zero_of_ne_zero_of_pos $pa $pb) : Expr))
  | .nonzero pa, .nonzero pb =>
    let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
    pure (.nonzero (q(mul_ne_zero $pa $pb) : Expr))
  | _, _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a ^ 0`.
This extension is run in addition to the general `a ^ b` extension (they are overlapping). -/
@[positivity (_ : α) ^ 0, Pow.pow _ 0]
def evalPowZero : PositivityExt where eval {u α} _zα _pα e := do
  let .app (.app _ (a : Q($α))) _ ← withReducible (whnf e) | throwError "not ^"
  _ ← synthInstanceQ (q(OrderedMonoidWithZero $α) : Q(Type u))
  _ ← synthInstanceQ (q(Nontrivial $α) : Q(Prop))
  pure (.positive (q(pow_zero_pos $a) : Expr))

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℕ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : PositivityExt where eval {u α} zα pα e := do
  let .app (.app _ (a : Q($α))) (b : Q(ℕ)) ← withReducible (whnf e) | throwError "not ^"
  let result ← catchNone do
    let .true := b.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ n where n is a literal"
    let some n := (b.getRevArg! 1).natLit? | throwError "not a ^ n where n is a literal"
    guard (n % 2 = 0)
    let m : Q(ℕ) := mkRawNatLit (n / 2)
    let _a ← synthInstanceQ (q(LinearOrderedRing $α) : Q(Type u))
    pure (.nonnegative (q(pow_bit0_nonneg $a $m) : Expr))
  orElse result do
    let ra ← core zα pα a
    let ofNonneg pa (oα : Q(OrderedSemiring $α)) : MetaM (Strictness zα pα e) := do
      have pa' : Q(by clear! «$zα» «$pα»; exact 0 ≤ $a) := pa
      pure (.nonnegative (q(pow_nonneg $pa' $b) : Expr))
    let ofNonzero pa (oα : Q(OrderedSemiring $α)) : MetaM (Strictness zα pα e) := do
      have pa' : Q(by clear! «$zα» «$pα»; exact $a ≠ 0) := pa
      let _a ← synthInstanceQ (q(by clear! «$zα» «$pα»; exact NoZeroDivisors $α) : Q(Prop))
      pure (.nonzero (q(pow_ne_zero $b $pa') : Expr))
    match ra with
    | .positive pa =>
      try
        let _a ← synthInstanceQ (q(StrictOrderedSemiring $α) : Q(Type u))
        have pa' : Q(by clear! «$zα» «$pα»; exact 0 < $a) := pa
        pure (.positive (q(pow_pos $pa' $b) : Expr))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let oα ← synthInstanceQ (q(OrderedSemiring $α) : Q(Type u))
        orElse (← catchNone (ofNonneg q(le_of_lt $pa) oα)) (ofNonzero q(ne_of_gt $pa) oα)
    | .nonnegative pa => ofNonneg pa (← synthInstanceQ (_ : Q(Type u)))
    | .nonzero pa => ofNonzero pa (← synthInstanceQ (_ : Q(Type u)))
    | .none => pure .none
