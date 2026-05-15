/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module


public meta import Mathlib.Tactic.IntervalArithmetic.Core
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

public import Mathlib.Tactic.IntervalArithmetic.Interval
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.Rify

/-!
## `exact_interval` tactic

This file impliments the `exact_interval` tactics for solving real inequalities and interval
containment goals using interval arithmetic (with rationals).

-/

@[expose] public section

open Nat

namespace IntervalArithmetic

meta section Elab

open Lean Expr Meta Elab Command Tactic

instance : Repr Dyadic where
  reprPrec d := reprPrec d.toRat

syntax (name := exact_interval) "exact_interval" ("[" interval_setting,*"]")? : tactic

@[tactic exact_interval]
def ExactInterval : Tactic
  | `(tactic| exact_interval $[[$settings?:interval_setting,*]]?) => withMainContext do
    let default := 0
    let (opConfig, approxParam) := ← do
      if let some settings := settings? then
        let (opConfig, n?) ← intervalSettingParser `ExactRatReal settings.getElems
        let approxParam := if let some n := n? then n else default
        return (opConfig, approxParam)
      else
        return ({}, default)
    intervalTactic Rat `ExactRatReal opConfig approxParam
  | _ => throwUnsupportedSyntax

end Elab

namespace ExactRatReal

def ratToReal : ℚ → ℝ := fun x ↦ x

@[interval_arithmetic_decl ExactRatReal]
theorem strictMono_ratToReal : StrictMono ratToReal := by
  intro x y hxy
  simp [ratToReal, hxy]

/- ## Numerals -/

open Interval

@[interval_op ExactRatReal NatCast]
theorem nat_cast_mem_singleton_cast_toSet (n : ℕ) : ↑n ∈ (singleton ↑n).toSet ratToReal := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.singleton, ratToReal]

@[interval_op ExactRatReal OfNat]
theorem ofNat_mem_singleton_cast_toSet (n : ℕ) :
    (OfNat.ofNat n) ∈ (singleton ↑n).toSet ratToReal := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.singleton, ratToReal,
    Semiring.toGrindSemiring_ofNat ℝ n]

@[interval_op ExactRatReal IntCast]
theorem intCast_mem_singleton_cast_toSet (z : ℤ) : ↑z ∈ (singleton ↑z).toSet ratToReal := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.singleton, ratToReal]

@[interval_op ExactRatReal RatCast]
def ratCast_mem_singleton_cast_toSet (q : ℚ) : ↑q ∈ (singleton q).toSet ratToReal := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.singleton, ratToReal]

@[interval_op ExactRatReal OfScientific]
theorem ofScientific_mem_singleton_ofScientific_toSet (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e) ∈ (singleton (Rat.ofScientific m s e)).toSet ratToReal := by
  exact ratCast_mem_singleton_cast_toSet _

/- ## Arithmetic Operations -/

def add (x y : Interval ℚ) : Interval ℚ where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩

@[interval_op ExactRatReal Add]
theorem add_mem_add_toSet {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet ratToReal) (hsy : s ∈ y.toSet ratToReal) :
    (r + s) ∈ (add x y).toSet ratToReal := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, add, ratToReal] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.lb
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.ub
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp

def sub (x y : Interval ℚ) : Interval ℚ where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩

@[interval_op ExactRatReal Sub]
theorem sub_mem_sub_toSet {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet ratToReal) (hsy : s ∈ y.toSet ratToReal) :
    (r - s) ∈ (sub x y).toSet ratToReal := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, sub, ratToReal] at hrx hsy ⊢
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

def neg (x : Interval ℚ) : Interval ℚ where
  lb := match x.ub with
    | ⊤ => ⊥
    | some ⟨c, a⟩ => some ⟨c, -a⟩
  ub := match x.lb with
    | ⊥ => ⊤
    | some ⟨c, a⟩ => some ⟨c, -a⟩

@[interval_op ExactRatReal Neg]
theorem neg_mem_neg_toSet {r : ℝ} (x : Interval ℚ) (hrx : r ∈ x.toSet ratToReal) :
    -r ∈ ((neg x).toSet ratToReal) := by
  simp only [neg, Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, ratToReal] at hrx ⊢
  constructor
  · cases hx : x.ub <;> simp [hx] at hrx ⊢; grind
  · cases hx : x.lb <;> simp [hx] at hrx ⊢; grind

section Mul

inductive IntervalSignClass where
  | nonneg
  | nonpos
  | mixed

def LowerBound.zero : LowerBound ℚ := some ⟨true, 0⟩
def UpperBound.zero : UpperBound ℚ := some ⟨true, 0⟩

def toIntervalSignClass (x : Interval ℚ) : IntervalSignClass :=
  if LowerBound.zero ≤ x.lb then .nonneg
  else if x.ub ≤ UpperBound.zero then .nonpos
  else .mixed

lemma lb_eq_of_intervalSignClass_nonneg {x : Interval ℚ}
    (hx : toIntervalSignClass x = .nonneg) : ∃ c, ∃ a ≥ 0, x.lb = some ⟨c, a⟩ := by
  by_cases! h_le : LowerBound.zero ≤ x.lb
  · match hlb : x.lb with
    | ⊥ => simp [LowerBound.zero, hlb] at h_le; simpa using le_bot_iff.mp h_le
    | some ⟨c, a⟩ => sorry
  · grind [toIntervalSignClass]

lemma ub_eq_of_intervalSignClass_nonpos {x : Interval ℚ}
    (hx : toIntervalSignClass x = .nonpos) : ∃ c, ∃ a ≤ 0, x.ub = some ⟨c, a⟩ := by
  by_cases! h_le : x.ub ≤ UpperBound.zero
  · match hub : x.ub with
    | ⊤ => simp [UpperBound.zero, hub] at h_le; simpa using top_le_iff.mp h_le
    | some ⟨c, a⟩ => sorry
  · grind [toIntervalSignClass]

lemma nonneg_of_mem_nonneg_toSet {r : ℝ} {x : Interval ℚ}
    (hx : toIntervalSignClass x = .nonneg) (hrx : r ∈ x.toSet ratToReal) : 0 ≤ r := by
  obtain ⟨c, a, h⟩ := lb_eq_of_intervalSignClass_nonneg hx
  cases c <;> simp [mem_toSet, h, LowerBound.Bounds, ratToReal] at hrx <;> rify at h <;> linarith

lemma nonpos_of_mem_nonpos_toSet {r : ℝ} {x : Interval ℚ}
    (hx : toIntervalSignClass x = .nonpos) (hrx : r ∈ x.toSet ratToReal) : r ≤ 0 := by
  obtain ⟨c, a, h⟩ := ub_eq_of_intervalSignClass_nonpos hx
  cases c <;> simp [mem_toSet, h, UpperBound.Bounds, ratToReal] at hrx <;> rify at h <;> linarith

lemma UpperBound.max_bounds {r : ℝ} {ub₁ ub₂ : UpperBound ℚ}
    (h : ub₁.Bounds ratToReal r ∨ ub₂.Bounds ratToReal r) : (max ub₁ ub₂).Bounds ratToReal r := by
  obtain (h | h) := h
  · exact UpperBound.bounds_of_bounds strictMono_ratToReal (le_max_left _ _) h
  · exact UpperBound.bounds_of_bounds strictMono_ratToReal (le_max_right _ _) h

def LowerBound.mul (lb₁ lb₂ : LowerBound ℚ) : LowerBound ℚ :=
  match lb₁, lb₂ with
  | ⊥, ⊥ => ⊥
  | some ⟨c, a⟩, ⊥ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | ⊥, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def UpperBound.mul (ub₁ ub₂ : UpperBound ℚ) : UpperBound ℚ :=
  match ub₁, ub₂ with
  | ⊤, ⊤ => ⊤
  | ⊤, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c, a⟩, ⊤ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def mul (x y : Interval ℚ) : Interval ℚ :=
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

theorem mul_mem_mul_toSet_of_nonneg_nonneg {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet ratToReal) (hsy : s ∈ y.toSet ratToReal)
    (hx : toIntervalSignClass x = .nonneg) (hy : toIntervalSignClass y = .nonneg) :
    r * s ∈ (mul x y).toSet ratToReal := by
  constructor
  · obtain ⟨c₁, a₁, ha₁, hxlb⟩ := lb_eq_of_intervalSignClass_nonneg hx
    obtain ⟨c₂, a₂, ha₂, hylb⟩ := lb_eq_of_intervalSignClass_nonneg hy
    cases hc₁ : c₁ <;> cases hc₂ : c₂
    <;> (by_cases! ha₁zero : a₁ = 0; swap; have : 0 < (a₁ : ℝ) := by simpa using lt_of_le_of_ne ha₁ ha₁zero.symm)
    <;> (by_cases! ha₂zero : a₂ = 0; swap; have : 0 < (a₂ : ℝ) := by simpa using lt_of_le_of_ne ha₂ ha₂zero.symm)
    <;> simp [mem_toSet, LowerBound.Bounds, mul, hx, hy, LowerBound.mul, hxlb, hylb, hc₁, hc₂,
      ratToReal, ha₁zero, ha₂zero] at hrx hsy ⊢ <;> rify at ha₁ ha₂
    <;> grind [mul_pos, mul_nonneg, mul_lt_mul, mul_le_mul, mul_lt_mul']
  · sorry

@[interval_op ExactRatReal Mul]
theorem mul_mem_mul_toSet {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet ratToReal) (hsy : s ∈ y.toSet ratToReal) :
    r * s ∈ (mul x y).toSet ratToReal := by
  sorry

end Mul

-- div

-- inv

-- pow

section Pow

def pow (x : Interval ℚ) (n : ℕ) : Interval ℚ :=
  if n = 0 then singleton 1
  else if LowerBound.zero ≤ x.lb || n % 2 = 1 then
    let lb := match x.lb with | ⊥ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.ub with | ⊤ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else if x.ub ≤ UpperBound.zero then
    let lb := match x.ub with | ⊤ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.lb with | ⊥ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else
    let ub := match x.lb, x.ub with
    | some ⟨c₁, q₁⟩, some ⟨c₂, q₂⟩ =>
      let q₁' := |q₁|
      if q₁' < q₂ then some ⟨c₂, q₂ ^ n⟩
      else if q₁' = q₂ then some ⟨c₁ || c₂, q₂ ^ n⟩
      else some ⟨c₁, q₁' ^ n⟩
    | _, _ => ⊤
    ⟨LowerBound.zero, ub⟩

@[interval_op ExactRatReal Pow]
theorem rat_pow_inclusion {r : ℝ} {x : Interval ℚ} (n : ℕ) (hrx : r ∈ x.toSet ratToReal) :
    (r ^ n) ∈ (pow x n).toSet ratToReal := by
  sorry

end Pow

section Abs

def LowerBound.flip (lb : LowerBound ℚ) : UpperBound ℚ :=
  match lb with
  | ⊥ => ⊤
  | some ⟨c, a⟩ => some ⟨c, -a⟩

def UpperBound.flip (ub : UpperBound ℚ) : LowerBound ℚ :=
  match ub with
  | ⊤ => ⊥
  | some ⟨c, a⟩ => some ⟨c, -a⟩

lemma LowerBound.flip_bounds {r : ℝ} {lb : LowerBound ℚ} :
    lb.Bounds ratToReal r ↔ (LowerBound.flip lb).Bounds ratToReal (-r) := by
  match lb with
  | ⊥ => simp [flip]
  | some ⟨c, a⟩ => cases c <;> simp [LowerBound.Bounds, UpperBound.Bounds, flip, ratToReal]

lemma UpperBound.flip_bounds {r : ℝ} {ub : UpperBound ℚ} :
    ub.Bounds ratToReal r ↔ (UpperBound.flip ub).Bounds ratToReal (-r) := by
  match ub with
  | ⊤ => simp [flip]
  | some ⟨c, a⟩ => cases c <;> simp [LowerBound.Bounds, UpperBound.Bounds, flip, ratToReal]

def abs (x : Interval ℚ) : Interval ℚ :=
  match toIntervalSignClass x with
  | .nonneg => ⟨x.lb, x.ub⟩
  | .nonpos => ⟨UpperBound.flip x.ub, LowerBound.flip x.lb⟩
  | .mixed => ⟨some ⟨true, 0⟩, max (LowerBound.flip x.lb) x.ub⟩

@[interval_op ExactRatReal Abs]
theorem abs_mem_abs_toSet {r : ℝ} {x : Interval ℚ} (hrx : r ∈ x.toSet ratToReal) :
    |r| ∈ (abs x).toSet ratToReal := by
  simp only [Interval.mem_toSet, abs] at hrx ⊢
  match hx : toIntervalSignClass x with
  | .nonneg =>
      have hr : |r| = r := abs_of_nonneg (nonneg_of_mem_nonneg_toSet hx hrx)
      simp [hr, hrx]
  | .nonpos =>
      have hr : |r| = -r := abs_of_nonpos (nonpos_of_mem_nonpos_toSet hx hrx)
      simp [hr, ← LowerBound.flip_bounds, ← UpperBound.flip_bounds, hrx]
  | .mixed =>
      constructor
      · exact LowerBound.bounds_of_le (abs_nonneg _) (by simp [LowerBound.Bounds, ratToReal])
      · apply UpperBound.max_bounds
        obtain (⟨h, _⟩| ⟨h, _⟩) := abs_cases r
        · simp [h, hrx.2]
        · simp [h, ← LowerBound.flip_bounds, hrx.1]

end Abs


end ExactRatReal

end IntervalArithmetic
