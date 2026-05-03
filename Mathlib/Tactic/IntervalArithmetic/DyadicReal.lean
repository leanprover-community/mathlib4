module

public meta import Mathlib.Tactic.IntervalArithmetic.Dyadic
public import Mathlib.Tactic.IntervalArithmetic.Dyadic
public import Mathlib.Tactic.IntervalArithmetic.Core
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.IntervalArithmetic.Interval

set_option linter.style.header false

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

def dyadic_to_real : Dyadic → ℝ := fun x ↦ x.toRat

@[interval_arithmetic_decl DyadicReal]
theorem strictMono_dyadic_to_real : StrictMono dyadic_to_real := by
  intro x y hxy
  simp [dyadic_to_real, hxy]

/- Numerals -/

def nat_const (n : ℕ) : Interval Dyadic :=
  ⟨some ⟨true, (n : Dyadic)⟩, some ⟨true, (n : Dyadic)⟩⟩

@[interval_op DyadicReal NatCast]
theorem nat_cast_inclusion (n : ℕ) : ↑n ∈ (nat_const n).toSet dyadic_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, nat_const, Dyadic.toRat_natCast,
    dyadic_to_real]

@[interval_op DyadicReal OfNat]
theorem of_nat_inclusion (n : ℕ) : (OfNat.ofNat n) ∈ (nat_const n).toSet dyadic_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, nat_const, Dyadic.toRat_natCast,
    Semiring.toGrindSemiring_ofNat, dyadic_to_real]

def int_const (z : ℤ) : Interval Dyadic :=
  ⟨some ⟨true, (z : Dyadic)⟩, some ⟨true, (z : Dyadic)⟩⟩

@[interval_op DyadicReal IntCast]
theorem int_const_inclusion (z : ℤ) : ↑z ∈ (int_const z).toSet dyadic_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, int_const, Dyadic.toRat_intCast,
    dyadic_to_real]

def rat_const (approx_param : ℕ) (q : ℚ) : Interval Dyadic :=
  ⟨some ⟨true, q.toDyadic approx_param⟩, some ⟨true, -(-q).toDyadic approx_param⟩⟩

@[interval_op DyadicReal RatCast]
def rat_const_inclusion (approx_param : ℕ) (q : ℚ) :
    ↑q ∈ (rat_const approx_param q).toSet dyadic_to_real := by
  sorry

@[interval_op DyadicReal OfScientific]
def rat_of_scientific_inclusion (approx_param : ℕ) (m : ℕ) (s : Bool) (e : ℕ) :
    ↑(OfScientific.ofScientific (α := ℝ) m s e)
      ∈ (rat_const approx_param (Rat.ofScientific m s e)).toSet dyadic_to_real := by
  sorry

/- Exact Operations -/

def Interval.add (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩

@[interval_op DyadicReal Add]
theorem dyadic_add_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    (r + s) ∈ (x.add y).toSet dyadic_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.add,
    dyadic_to_real] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.lb
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;> simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.ub
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;> simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp

def Interval.sub (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩

@[interval_op DyadicReal Sub]
theorem dyadic_sub_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    (r - s) ∈ (x.sub y).toSet dyadic_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.sub,
    dyadic_to_real] at hrx hsy ⊢
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

def Interval.neg (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.ub with
    | ⊤ => ⊥
    | some ⟨c, a⟩ => some ⟨c, -a⟩
  ub := match x.lb with
    | ⊥ => ⊤
    | some ⟨c, a⟩ => some ⟨c, -a⟩

@[interval_op DyadicReal Neg]
theorem neg_inclusion {r : ℝ} (x : Interval Dyadic) (hrx : r ∈ x.toSet dyadic_to_real) :
    -r ∈ (x.neg.toSet dyadic_to_real) := by
  simp only [Interval.neg, Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds,
    dyadic_to_real] at hrx ⊢
  constructor
  · cases hx : x.ub <;> simp [hx] at hrx ⊢; grind
  · cases hx : x.lb <;> simp [hx] at hrx ⊢; grind

section Mul

inductive IntervalSignClass
  | nonneg
  | nonpos
  | mixed

def Interval.toIntervalSignClass (x : Interval Dyadic) : IntervalSignClass :=
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

def Interval.mul (x y : Interval Dyadic) : Interval Dyadic :=
  match x.toIntervalSignClass, y.toIntervalSignClass with
  | .nonneg, .nonneg => ⟨x.lb.mul y.lb, x.ub.mul y.ub⟩
  | .nonneg, .nonpos => ⟨x.ub.toLowerBound.mul y.lb, x.lb.toUpperBound.mul y.ub⟩
  | .nonneg, .mixed => ⟨x.ub.toLowerBound.mul y.lb, x.ub.mul y.ub⟩
  | .nonpos, .nonneg => ⟨x.lb.mul y.ub.toLowerBound, x.ub.mul y.lb.toUpperBound⟩
  | .nonpos, .nonpos => ⟨x.ub.mul y.ub |>.toLowerBound, x.lb.mul y.lb |>.toUpperBound⟩
  | .nonpos, .mixed => ⟨x.lb.mul y.ub.toLowerBound, x.lb.mul y.lb |>.toUpperBound⟩
  | .mixed, .nonneg => ⟨x.lb.mul y.ub.toLowerBound, x.ub.mul y.ub⟩
  | .mixed, .nonpos => ⟨x.ub.toLowerBound.mul y.lb, x.lb.mul y.lb |>.toUpperBound⟩
  | .mixed, .mixed =>
      ⟨min (x.lb.mul y.ub.toLowerBound) (x.ub.toLowerBound.mul y.lb),
       max (x.lb.mul y.lb |>.toUpperBound) (x.ub.mul y.ub)⟩

@[interval_op DyadicReal Mul]
theorem Interval.rat_mul_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    r * s ∈ (x.mul y).toSet dyadic_to_real := by
  sorry

end Mul

section Pow

section Pow

def Interval.pow (x : Interval Dyadic) (n : ℕ) : Interval Dyadic :=
  let zero_lb : LowerBound Dyadic := some ⟨true, 0⟩
  let zero_ub : UpperBound Dyadic := some ⟨true, 0⟩
  if n = 0 then nat_const 1
  else if zero_lb ≤ x.lb || n % 2 = 1 then
    let lb := match x.lb with | ⊥ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.ub with | ⊤ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else if decide (x.ub ≤ zero_ub) then
    let lb := match x.ub with | ⊤ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.lb with | ⊥ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else
    let ub := match x.lb, x.ub with
    | some ⟨c₁, q₁⟩, some ⟨c₂, q₂⟩ =>
      let q₁' := if 0 ≤ q₁ then q₁ else -q₁ -- q₁.abs
      if q₁' < q₂ then some ⟨c₂, q₂ ^ n⟩
      else if q₁' = q₂ then some ⟨c₁ || c₂, q₂ ^ n⟩
      else some ⟨c₁, q₁' ^ n⟩
    | _, _ => ⊤
    ⟨zero_lb, ub⟩


@[interval_op DyadicReal Pow]
theorem rat_pow_inclusion {r : ℝ} {x : Interval Dyadic} (n : ℕ) (hrx : r ∈ x.toSet dyadic_to_real) :
    (r ^ n) ∈ (x.pow n).toSet dyadic_to_real := by
  sorry

end Pow

end Pow

-- # CHATGPT AFTER THIS POINT:

section Div

namespace Dyadic

/--
`divDown approxParam a b` is the dyadic approximation of `a / b` rounded downward
to precision `approxParam`.

This avoids constructing an intermediate `Rat`.
-/
def divDown (approxParam : ℕ) (a b : Dyadic) : Dyadic :=
  match a, b with
  | zero, _ => 0
  | _, zero => 0
  | .ofOdd n₁ k₁ _, .ofOdd n₂ k₂ _ =>
      let prec : Int := approxParam
      let shift : Int := k₂ - k₁ + prec
      let num : Int := if n₂ < 0 then -n₁ else n₁
      let den : Int := if n₂ < 0 then -n₂ else n₂
      let q : Int :=
        match shift with
        | Int.ofNat s => Int.fdiv (num <<< s) den
        | Int.negSucc s => Int.fdiv num (den <<< (s + 1))
      Dyadic.ofIntWithPrec q prec

/--
`divUp approxParam a b` is the dyadic approximation of `a / b` rounded upward
to precision `approxParam`.
-/
def divUp (approxParam : ℕ) (a b : Dyadic) : Dyadic :=
  - divDown approxParam (-a) b

end Dyadic

def LowerBound.dyadic_div
    (approxParam : ℕ) (lb₁ : LowerBound Dyadic) (ub₂ : UpperBound Dyadic)
    (lb₂ : LowerBound Dyadic) :
    LowerBound Dyadic :=
  match lb₁, ub₂ with
  | ⊥, ⊤ => ⊥
  | ⊥, some ⟨c, a⟩ =>
      if a = 0 ∧ c ∧ lb₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        ⊥
  | some ⟨c, a⟩, ⊤ =>
      if lb₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨a = 0 ∧ c, 0⟩
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then
        some ⟨true, 0⟩
      else if a₂ = 0 then
        if lb₂ = some ⟨true, 0⟩ then
          some ⟨true, 0⟩
        else
          ⊥
      else if lb₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨c₁ && c₂, Dyadic.divDown approxParam a₁ a₂⟩

def UpperBound.dyadic_div
    (approxParam : ℕ) (ub₁ : UpperBound Dyadic) (lb₂ : LowerBound Dyadic)
    (ub₂ : UpperBound Dyadic) :
    UpperBound Dyadic :=
  match ub₁, lb₂ with
  | ⊤, ⊥ => ⊤
  | ⊤, some ⟨c, a⟩ =>
      if a = 0 ∧ c ∧ ub₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        ⊤
  | some ⟨c, a⟩, ⊥ =>
      if ub₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨a = 0 ∧ c, 0⟩
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then
        some ⟨true, 0⟩
      else if a₂ = 0 then
        if ub₂ = some ⟨true, 0⟩ then
          some ⟨true, 0⟩
        else
          ⊤
      else if ub₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨c₁ && c₂, Dyadic.divUp approxParam a₁ a₂⟩

def Interval.dyadic_div (approxParam : ℕ) (x y : Interval Dyadic) : Interval Dyadic :=
  match x.toIntervalSignClass, y.toIntervalSignClass with
  | .nonneg, .nonneg =>
      ⟨x.lb.dyadic_div approxParam y.ub y.lb,
       x.ub.dyadic_div approxParam y.lb y.ub⟩

  | .nonpos, .nonpos =>
      ⟨(x.ub.dyadic_div approxParam y.lb y.ub).toLowerBound,
       (x.lb.dyadic_div approxParam y.ub y.lb).toUpperBound⟩

  | .nonpos, .nonneg =>
      ⟨x.lb.dyadic_div approxParam y.lb.toUpperBound y.ub.toLowerBound,
       x.ub.dyadic_div approxParam y.ub.toLowerBound y.lb.toUpperBound⟩

  | .nonneg, .nonpos =>
      ⟨x.ub.toLowerBound.dyadic_div approxParam y.ub y.lb,
       x.lb.toUpperBound.dyadic_div approxParam y.lb y.ub⟩

  | .mixed, .nonneg =>
      ⟨x.lb.dyadic_div approxParam y.lb.toUpperBound y.ub.toLowerBound,
       x.ub.dyadic_div approxParam y.lb y.ub⟩

  | .mixed, .nonpos =>
      ⟨x.ub.toLowerBound.dyadic_div approxParam y.ub y.lb,
       (x.lb.dyadic_div approxParam y.ub y.lb).toUpperBound⟩

  | .nonneg, .mixed =>
      if x = ⟨some ⟨true, 0⟩, some ⟨true, 0⟩⟩ then
        x
      else
        ⟨⊥, ⊤⟩

  | .nonpos, .mixed =>
      ⟨⊥, ⊤⟩

  | .mixed, .mixed =>
      ⟨⊥, ⊤⟩

@[interval_op DyadicReal Div]
theorem Interval.dyadic_div_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (approxParam : ℕ)
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    r / s ∈ (x.dyadic_div approxParam y).toSet dyadic_to_real := by
  sorry

end Div

section Sqrt

namespace Dyadic

/--
`sqrtFloorAndExact approxParam q` returns `(m, exact)` where

* `m / 2^approxParam ≤ sqrt q`;
* `exact = true` iff `m / 2^approxParam = sqrt q`.

For negative `q` we return `(0, true)`, matching `Real.sqrt`'s behavior on negative inputs.
-/
def sqrtFloorAndExact (approx_param : ℕ) (q : Dyadic) : Int × Bool :=
  match q with
  | zero => (0, true)
  | .ofOdd n k _ =>
      if n < 0 then
        (0, true)
      else
        let N : Nat := n.natAbs
        let shift : Int := 2 * (approx_param : Int) - k
        match shift with
        | Int.ofNat s =>
            let scaled : Nat := N <<< s
            let m : Nat := Nat.sqrt scaled
            ((m : Int), if m * m = scaled then true else false)
        | Int.negSucc s =>
            let t : Nat := s + 1
            let denom : Nat := (1 : Nat) <<< t
            let scaledFloor : Nat := N / denom
            let m : Nat := Nat.sqrt scaledFloor
            ((m : Int), if (m * m) * denom = N then true else false)

/-- Dyadic lower approximation to `sqrt q`. -/
def sqrtDown (approx_param : ℕ) (q : Dyadic) : Dyadic :=
  let r := sqrtFloorAndExact approx_param q
  Dyadic.ofIntWithPrec r.1 approx_param

/-- Dyadic upper approximation to `sqrt q`. -/
def sqrtUp (approx_param : ℕ) (q : Dyadic) : Dyadic :=
  let r := sqrtFloorAndExact approx_param q
  let m := r.1
  let exact := r.2
  Dyadic.ofIntWithPrec (if exact then m else m + 1) approx_param

/-- Whether `sqrt q` is exactly representable at precision `approxParam`. -/
def sqrtExact (approx_param : ℕ) (q : Dyadic) : Bool :=
  (sqrtFloorAndExact approx_param q).2

end Dyadic

def Interval.dyadic_sqrt (approx_param : ℕ) (x : Interval Dyadic) : Interval Dyadic where
  lb :=
    match x.lb with
    | ⊥ => some ⟨true, 0⟩
    | some ⟨c, a⟩ =>
        if a < 0 then
          some ⟨true, 0⟩
        else
          let r := Dyadic.sqrtFloorAndExact approx_param a
          some ⟨c && r.2, Dyadic.ofIntWithPrec r.1 approx_param⟩
  ub :=
    match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ =>
        if a ≤ 0 then
          some ⟨true, 0⟩
        else
          let r := Dyadic.sqrtFloorAndExact approx_param a
          let m := if r.2 then r.1 else r.1 + 1
          some ⟨c && r.2, Dyadic.ofIntWithPrec m approx_param⟩

@[interval_op DyadicReal Sqrt]
theorem Interval.dyadic_sqrt_inclusion {r : ℝ} {x : Interval Dyadic} (approx_param : ℕ)
    (hrx : r ∈ x.toSet dyadic_to_real) :
    √ r ∈ (x.dyadic_sqrt approx_param).toSet dyadic_to_real := by
  sorry

end Sqrt

section Exp

def bitLenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n = 0 then
        0
      else
        1 + bitLenAux fuel (n / 2)

def _root_.Nat.bitLen (n : ℕ) : ℕ :=
  bitLenAux n n

def _root_.Dyadic.divPowTwo (x : Dyadic) (k : ℕ) : Dyadic :=
  match x with
  | zero => 0
  | .ofOdd n e _ => Dyadic.ofIntWithPrec n (e + k)

def squareIter : ℕ → Dyadic → Dyadic
  | 0, x => x
  | k + 1, x => squareIter k (x * x)

def expReductionSteps (x : Dyadic) : ℕ :=
  match x with
  | zero => 0
  | .ofOdd n e _ =>
      let L := n.natAbs.bitLen
      match e with
      | Int.ofNat eNat => L - eNat
      | Int.negSucc s => L + (s + 1)

def expTaylorLowerAux (prec : ℕ) (x : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic
  | 0, _k, _term, sum => sum
  | n + 1, k, term, sum =>
      let next := Dyadic.divDown prec (term * x) ((k + 1 : ℕ) : Dyadic)
      expTaylorLowerAux prec x n (k + 1) next (sum + next)

def expTaylorLower (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  expTaylorLowerAux prec x terms 0 1 1

def expTaylorUpperAux (prec : ℕ) (x : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic × Dyadic × ℕ
  | 0, k, term, sum =>
      let next := Dyadic.divUp prec (term * x) ((k + 1 : ℕ) : Dyadic)
      (sum, next, k + 1)
  | n + 1, k, term, sum =>
      let next := Dyadic.divUp prec (term * x) ((k + 1 : ℕ) : Dyadic)
      expTaylorUpperAux prec x n (k + 1) next (sum + next)

def expTaylorUpper (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let st := expTaylorUpperAux prec x terms 0 1 1
  let sum := st.1
  let next := st.2.1
  let k := st.2.2
  let K : Dyadic := ((k + 1 : ℕ) : Dyadic)
  sum + Dyadic.divUp prec (next * K) (K - x)

/-- Lower approximation for `exp x`, intended for `0 ≤ x`. -/
def expNonnegDown (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let k := expReductionSteps x
  let x' := x.divPowTwo k
  squareIter k (expTaylorLower prec terms x')

/-- Upper approximation for `exp x`, intended for `0 ≤ x`. -/
def expNonnegUp (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let k := expReductionSteps x
  let x' := x.divPowTwo k
  squareIter k (expTaylorUpper prec terms x')

def expDown (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  if x < 0 then
    Dyadic.divDown prec 1 (expNonnegUp prec terms (-x))
  else
    expNonnegDown prec terms x

def expUp (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  if x < 0 then
    Dyadic.divUp prec 1 (expNonnegDown prec terms (-x))
  else
    expNonnegUp prec terms x


def Interval.dyadic_exp (approx_param : ℕ) (x : Interval Dyadic) : Interval Dyadic where
  lb :=
    match x.lb with
    | ⊥ => some ⟨false, 0⟩
    | some ⟨c, a⟩ =>
        some ⟨c, expDown approx_param approx_param a⟩
  ub :=
    match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ =>
        some ⟨c, expUp approx_param approx_param a⟩

@[interval_op DyadicReal Exp]
theorem Interval.dyadic_exp_inclusion {r : ℝ} {x : Interval Dyadic} (approx_param : ℕ)
    (hrx : r ∈ x.toSet dyadic_to_real) :
    Real.exp r ∈ (x.dyadic_exp approx_param).toSet dyadic_to_real := by
  sorry

end Exp

section Pi

namespace Dyadic

/--
Number of arctan terms to use for a given dyadic precision.

For `atan (1 / 5)`, each two-step reduction gains roughly `log₂ 25 ≈ 4.64` bits,
so `prec / 4 + 4` is conservative. This is just for sharpness, not soundness:
any number of terms gives valid alternating-series bounds.
-/
def atanTerms (prec : ℕ) : ℕ :=
  prec / 4 + 4

/--
Computes lower and upper approximations to the alternating arctangent partial sum.

If `q ≥ 0`, this processes terms

`q - q^3 / 3 + q^5 / 5 - ...`

The pair `(lo, hi)` satisfies:
* `lo ≤` the exact partial sum,
* the exact partial sum `≤ hi`.

Positive terms are rounded outward as:
* lower sum adds lower term bound,
* upper sum adds upper term bound.

Negative terms are rounded outward as:
* lower sum subtracts upper term bound,
* upper sum subtracts lower term bound.
-/
def atanBoundsAux (prec : ℕ) (qSq : Dyadic) :
    ℕ → ℕ → Bool → Dyadic → Dyadic → Dyadic → Dyadic → Dyadic × Dyadic
  | 0, _d, _pos, _termLo, _termHi, lo, hi => (lo, hi)
  | n + 1, d, pos, termLo, termHi, lo, hi =>
      let lo' := if pos then lo + termLo else lo - termHi
      let hi' := if pos then hi + termHi else hi - termLo
      let d' := d + 2
      let termLo' := Dyadic.divDown prec (termLo * qSq * (d : Dyadic)) (d' : Dyadic)
      let termHi' := Dyadic.divUp prec (termHi * qSq * (d : Dyadic)) (d' : Dyadic)
      atanBoundsAux prec qSq n d' (!pos) termLo' termHi' lo' hi'

/--
Bounds for the partial arctangent sum through term `n`.

The term index convention matches:

* `n = 0`: `q`
* `n = 1`: `q - q^3 / 3`
* `n = 2`: `q - q^3 / 3 + q^5 / 5`
-/
def atanBounds (prec : ℕ) (q : Dyadic) (n : ℕ) : Dyadic × Dyadic :=
  atanBoundsAux prec (q * q) (n + 1) 1 true q q 0 0

/-- Lower bound for `atan q`, using an odd partial sum. -/
def atanLower (prec : ℕ) (q : Dyadic) (n : ℕ) : Dyadic :=
  (atanBounds prec q (2 * n + 1)).1

/-- Upper bound for `atan q`, using an even partial sum. -/
def atanUpper (prec : ℕ) (q : Dyadic) (n : ℕ) : Dyadic :=
  (atanBounds prec q (2 * n)).2

end Dyadic

def Interval.dyadicPi (approxParam : ℕ) : Interval Dyadic :=
  let terms := Dyadic.atanTerms approxParam

  -- Lower/upper dyadic enclosures of the rational constants.
  let q₁Lo := Dyadic.divDown approxParam 1 (5 : Dyadic)
  let q₁Hi := Dyadic.divUp approxParam 1 (5 : Dyadic)
  let q₂Lo := Dyadic.divDown approxParam 1 (239 : Dyadic)
  let q₂Hi := Dyadic.divUp approxParam 1 (239 : Dyadic)

  -- π = 16 atan(1/5) - 4 atan(1/239)
  let lb := 16 * Dyadic.atanLower approxParam q₁Lo terms
      - 4 * Dyadic.atanUpper approxParam q₂Hi terms
  let ub := 16 * Dyadic.atanUpper approxParam q₁Hi terms
      - 4 * Dyadic.atanLower approxParam q₂Lo terms

  { lb := some ⟨false, lb⟩
    ub := some ⟨false, ub⟩ }

@[interval_op DyadicReal Pi]
theorem Interval.mem_dyadicPi (approx_param : ℕ) :
    Real.pi ∈ (Interval.dyadicPi approx_param).toSet dyadic_to_real := by
  sorry

end Pi

end IntervalArithmetic
