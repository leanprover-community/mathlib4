/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.IntervalArithmetic.Dyadic

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.IntervalArithmetic.Core
public import Mathlib.Tactic.IntervalArithmetic.Dyadic
public import Mathlib.Tactic.IntervalArithmetic.Interval

/-!
## `dyadic_interval` tactic

This file impliments the `dyadic_interval` tactics for solving real inequalities and interval
containment goals using interval arithmetic (with dyadic approximations).

-/

@[expose] public section


open Nat

namespace IntervalArithmetic

meta section Elab

instance : Repr Dyadic where
  reprPrec d := reprPrec d.toRat
open Lean Expr Meta Elab Command Tactic

syntax (name := dyadic_interval) "dyadic_interval" ("[" interval_setting,*"]")? : tactic

@[tactic dyadic_interval]
def DyadicInterval : Tactic
  | `(tactic| dyadic_interval $[[$settings?:interval_setting,*]]?) => withMainContext do
    let default := 0
    let (opConfig, approxParam) := ← do
      if let some settings := settings? then
        let (opConfig, n?) ← intervalSettingParser `DyadicReal settings.getElems
        let approxParam := if let some n := n? then n else default
        return (opConfig, approxParam)
      else
        return ({}, default)
    intervalTactic Dyadic `DyadicReal opConfig approxParam
  | _ => throwUnsupportedSyntax

end Elab

namespace DyadicReal

def dyadicToReal : Dyadic → ℝ := fun x ↦ x.toRat

@[interval_arithmetic_decl DyadicReal]
theorem strictMono_dyadic_to_real : StrictMono dyadicToReal := by
  intro x y hxy
  simp [dyadicToReal, hxy]

/- ## Numerals -/

open Interval Dyadic

@[interval_op DyadicReal NatCast]
theorem nat_cast_mem_singleton_cast_toSet (n : ℕ) : ↑n ∈ (singleton ↑n).toSet dyadicToReal := by
  simp [mem_toSet, LowerBound.Bounds, UpperBound.Bounds, dyadicToReal, Interval.singleton,
    Dyadic.toRat_natCast]

@[interval_op DyadicReal OfNat]
theorem ofNat_mem_singleton_cast_toSet (n : ℕ) :
    (OfNat.ofNat n) ∈ (singleton ↑n).toSet dyadicToReal := by
  simp [mem_toSet, LowerBound.Bounds, UpperBound.Bounds, dyadicToReal, Interval.singleton,
    Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat]

@[interval_op DyadicReal IntCast]
theorem intCast_mem_singleton_cast_toSet (z : ℤ) : ↑z ∈ (singleton ↑z).toSet dyadicToReal := by
  simp [mem_toSet, LowerBound.Bounds, UpperBound.Bounds, dyadicToReal, Interval.singleton,
     Dyadic.toRat_intCast]

def ratApprox (approxParam : ℕ) (q : ℚ) : Interval Dyadic :=
  ⟨some ⟨true, q.toDyadic approxParam⟩,
   some ⟨false, q.toDyadic approxParam + ofIntWithPrec 1 approxParam⟩⟩

@[interval_op DyadicReal RatCast]
theorem ratCast_mem_ratApprox_toSet (approxParam : ℕ) (q : ℚ) :
    ↑q ∈ (ratApprox approxParam q).toSet dyadicToReal := by
  simp [mem_toSet, LowerBound.Bounds, UpperBound.Bounds, ratApprox, dyadicToReal,
    Rat.toRat_toDyadic_le,  Rat.lt_toRat_toDyadic_add, - Rat.cast_add, - toRat_add]

@[interval_op DyadicReal OfScientific]
theorem ofScientific_mem_ofScientific_toSet (approxParam : ℕ) (m : ℕ) (s : Bool) (e : ℕ) :
    ↑(OfScientific.ofScientific (α := ℝ) m s e)
      ∈ (ratApprox approxParam (Rat.ofScientific m s e)).toSet dyadicToReal := by
  exact ratCast_mem_ratApprox_toSet _ _

/- ## Exact Operations -/

def add (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩

@[interval_op DyadicReal Add]
theorem dyadic_add_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadicToReal) (hsy : s ∈ y.toSet dyadicToReal) :
    (r + s) ∈ (add x y).toSet dyadicToReal := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, add,
    dyadicToReal] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.lb
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;> simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.ub
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;> simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp

def sub (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩

@[interval_op DyadicReal Sub]
theorem dyadic_sub_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadicToReal) (hsy : s ∈ y.toSet dyadicToReal) :
    (r - s) ∈ (sub x y).toSet dyadicToReal := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, sub,
    dyadicToReal] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.ub
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.lb
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp

def neg (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.ub with
    | ⊤ => ⊥
    | some ⟨c, a⟩ => some ⟨c, -a⟩
  ub := match x.lb with
    | ⊥ => ⊤
    | some ⟨c, a⟩ => some ⟨c, -a⟩

@[interval_op DyadicReal Neg]
theorem neg_inclusion {r : ℝ} (x : Interval Dyadic) (hrx : r ∈ x.toSet dyadicToReal) :
    -r ∈ ((neg x).toSet dyadicToReal) := by
  simp only [neg, Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds,
    dyadicToReal] at hrx ⊢
  constructor
  · cases hx : x.ub <;> simp [hx] at hrx ⊢; grind
  · cases hx : x.lb <;> simp [hx] at hrx ⊢; grind

section Mul

inductive IntervalSignClass where
  | nonneg
  | nonpos
  | mixed

def toIntervalSignClass (x : Interval Dyadic) : IntervalSignClass :=
  let zero_lb : LowerBound Dyadic := some ⟨true, 0⟩
  let zero_ub : UpperBound Dyadic := some ⟨true, 0⟩
  if zero_lb ≤ x.lb then .nonneg
  else if x.ub ≤ zero_ub then .nonpos
  else .mixed

def LowerBound.mul (lb₁ lb₂ : LowerBound Dyadic) : LowerBound Dyadic :=
  match lb₁, lb₂ with
  | ⊥, ⊥ => ⊥
  | some ⟨c, a⟩, ⊥ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | ⊥, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def UpperBound.mul (ub₁ ub₂ : UpperBound Dyadic) : UpperBound Dyadic :=
  match ub₁, ub₂ with
  | ⊤, ⊤ => ⊤
  | ⊤, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c, a⟩, ⊤ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def mul (x y : Interval Dyadic) : Interval Dyadic :=
  match toIntervalSignClass x, toIntervalSignClass y with
  | .nonneg, .nonneg =>
      ⟨LowerBound.mul x.lb y.lb, UpperBound.mul x.ub y.ub⟩
  | .nonneg, .nonpos =>
      ⟨LowerBound.mul x.ub.toLowerBound y.lb, UpperBound.mul x.lb.toUpperBound y.ub⟩
  | .nonneg, .mixed =>
      ⟨LowerBound.mul x.ub.toLowerBound y.lb, UpperBound.mul x.ub y.ub⟩
  | .nonpos, .nonneg =>
      ⟨LowerBound.mul x.lb y.ub.toLowerBound, UpperBound.mul x.ub y.lb.toUpperBound⟩
  | .nonpos, .nonpos =>
      ⟨(UpperBound.mul x.ub y.ub).toLowerBound, (LowerBound.mul x.lb y.lb).toUpperBound⟩
  | .nonpos, .mixed =>
      ⟨LowerBound.mul x.lb y.ub.toLowerBound, (LowerBound.mul x.lb y.lb).toUpperBound⟩
  | .mixed, .nonneg =>
      ⟨LowerBound.mul x.lb y.ub.toLowerBound, UpperBound.mul x.ub y.ub⟩
  | .mixed, .nonpos =>
      ⟨LowerBound.mul x.ub.toLowerBound y.lb, (LowerBound.mul x.lb y.lb).toUpperBound⟩
  | .mixed, .mixed =>
      ⟨min (LowerBound.mul x.lb y.ub.toLowerBound) (LowerBound.mul x.ub.toLowerBound y.lb),
       max ((LowerBound.mul x.lb y.lb).toUpperBound) (UpperBound.mul x.ub y.ub)⟩

@[interval_op DyadicReal Mul]
theorem mul_mem_mul_toSet {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadicToReal) (hsy : s ∈ y.toSet dyadicToReal) :
    r * s ∈ (mul x y).toSet dyadicToReal := by
  sorry

end Mul

section Pow

def pow (x : Interval Dyadic) (n : ℕ) : Interval Dyadic :=
  let zero_lb : LowerBound Dyadic := some ⟨true, 0⟩
  let zero_ub : UpperBound Dyadic := some ⟨true, 0⟩
  if n = 0 then singleton 1
  else if zero_lb ≤ x.lb || n % 2 = 1 then
    let lb := match x.lb with | ⊥ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.ub with | ⊤ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else if x.ub ≤ zero_ub then
    let lb := match x.ub with | ⊤ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.lb with | ⊥ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else
    let ub := match x.lb, x.ub with
    | some ⟨c₁, q₁⟩, some ⟨c₂, q₂⟩ =>
      let q₁' := if 0 ≤ q₁ then q₁ else -q₁
      if q₁' < q₂ then some ⟨c₂, q₂ ^ n⟩
      else if q₁' = q₂ then some ⟨c₁ || c₂, q₂ ^ n⟩
      else some ⟨c₁, q₁' ^ n⟩
    | _, _ => ⊤
    ⟨zero_lb, ub⟩


@[interval_op DyadicReal Pow]
theorem rat_pow_inclusion {r : ℝ} {x : Interval Dyadic} (n : ℕ) (hrx : r ∈ x.toSet dyadicToReal) :
    (r ^ n) ∈ (pow x n).toSet dyadicToReal := by
  sorry

end Pow

section Div

def divLb (approxParam : ℕ) (d₁ d₂ : Dyadic) : Dyadic :=
  match d₁, d₂ with
  | .zero, _ => 0
  | _, .zero => 0
  | .ofOdd n₁ k₁ _, .ofOdd n₂ k₂ _ =>
      let shift : Int := k₂ - k₁ + approxParam
      let num : Int := if n₂ < 0 then -n₁ else n₁
      let den : Int := if n₂ < 0 then -n₂ else n₂
      let q : Int :=
        match shift with
        | Int.ofNat s => Int.fdiv (num <<< s) den
        | Int.negSucc s => Int.fdiv num (den <<< (s + 1))
      Dyadic.ofIntWithPrec q prec

end Div

/- ## Transcendental Functions -/

section Exp

end Exp

end DyadicReal

end IntervalArithmetic
