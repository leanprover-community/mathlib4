module

public import Mathlib.Tactic.IntervalArithmetic.Core
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.IntervalArithmetic.Definitions
public meta import Mathlib.Tactic.IntervalArithmetic.Definitions

set_option linter.style.header false

@[expose] public section

open Nat

namespace IntervalArithmetic
meta section Elab

open Lean Expr Meta Elab Command Tactic

syntax (name := rat_interval) "rat_interval" num : tactic

@[tactic rat_interval]
def RatInterval : Tactic
  | `(tactic| rat_interval $n:num) => withMainContext do
    let some decl ← IntervalArithmetic.getIntervalArithmeticDecl? `RatReal | unreachable!
    IntervalCore Rat decl n.getNat
  | _ => throwUnsupportedSyntax

end Elab

def rat_to_real : ℚ → ℝ := fun x ↦ x

@[interval_arithmetic_decl RatReal]
theorem strictMono_rat_to_real : StrictMono rat_to_real := by
  intro x y hxy
  simp [rat_to_real, hxy]

/- Numerals -/

def nat_const (n : ℕ) : Interval ℚ := ⟨some ⟨true, n⟩, some ⟨true, n⟩⟩

@[interval_op RatReal]
theorem of_nat_inclusion (n : ℕ) : (OfNat.ofNat n) ∈ (nat_const n).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, rat_to_real, nat_const,
    Semiring.toGrindSemiring_ofNat ℝ n]

@[interval_op RatReal]
theorem nat_const_inclusion (n : ℕ) : ↑n ∈ (nat_const n).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, nat_const, rat_to_real]

def int_const (z : ℤ) : Interval ℚ  := ⟨some ⟨true, z⟩, some ⟨true, z⟩⟩

@[interval_op RatReal]
theorem int_const_inclusion (z : ℤ) : ↑z ∈ (int_const z).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, int_const, rat_to_real]

def rat_const (q : ℚ) : Interval ℚ := ⟨some ⟨true, q⟩, some ⟨true,q⟩⟩

@[interval_op RatReal]
theorem rat_const_inclusion (q : ℚ) : ↑q ∈ (rat_const q).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, rat_const, rat_to_real]

@[interval_op RatReal]
theorem rat_of_scientific_inclusion' (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e)
    ∈ (rat_const (Rat.ofScientific m s e)).toSet rat_to_real := by
  exact rat_const_inclusion _

/- Exact Operations -/

def Interval.rat_add (x y : Interval ℚ) : Interval ℚ where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩

def Interval.rat_neg (x : Interval ℚ) : Interval ℚ where
  lb := match x.ub with
    | ⊤ => ⊥
    | some ⟨c, a⟩ => some ⟨c, -a⟩
  ub := match x.lb with
    | ⊥ => ⊤
    | some ⟨c, a⟩ => some ⟨c, -a⟩

@[interval_op RatReal]
theorem rat_add_inclusion {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) (hsy : s ∈ y.toSet rat_to_real) :
    (r + s) ∈ (x.rat_add y).toSet rat_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.rat_add,
    rat_to_real] at hrx hsy ⊢
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

def Interval.rat_sub (x y : Interval ℚ) : Interval ℚ where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩

@[interval_op RatReal]
theorem rat_sub_inclusion {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) (hsy : s ∈ y.toSet rat_to_real) :
    (r - s) ∈ (x.rat_sub y).toSet rat_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.rat_sub,
    rat_to_real] at hrx hsy ⊢
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

@[interval_op RatReal]
theorem rat_neg_inclusion {r : ℝ} (x : Interval ℚ) (hrx : r ∈ x.toSet rat_to_real) :
    -r ∈ (x.rat_neg.toSet rat_to_real) := by
  simp only [Interval.rat_neg, Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds,
    rat_to_real] at hrx ⊢
  constructor
  · cases hx : x.ub <;> simp [hx] at hrx ⊢; grind
  · cases hx : x.lb <;> simp [hx] at hrx ⊢; grind

section Mul

inductive IntervalSignClass where
  | nonneg
  | nonpos
  | mixed

def Interval.toIntervalSignClass (x : Interval ℚ) : IntervalSignClass :=
  let zero_lb : LowerBound ℚ := some ⟨true, 0⟩
  let zero_ub : UpperBound ℚ := some ⟨true, 0⟩
  if zero_lb ≤ x.lb then .nonneg
  else if x.ub ≤ zero_ub then .nonpos
  else .mixed

def LowerBound.rat_mul (lb₁ lb₂ : LowerBound ℚ) : LowerBound ℚ :=
  match lb₁, lb₂ with
  | ⊥, ⊥ => ⊥
  | some ⟨c, a⟩, ⊥ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | ⊥, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def UpperBound.rat_mul (ub₁ ub₂ : UpperBound ℚ) : UpperBound ℚ :=
  match ub₁, ub₂ with
  | ⊤, ⊤ => ⊤
  | ⊤, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c, a⟩, ⊤ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def Interval.rat_mul (x y : Interval ℚ) : Interval ℚ :=
  match x.toIntervalSignClass, y.toIntervalSignClass with
  | .nonneg, .nonneg => ⟨x.lb.rat_mul y.lb, x.ub.rat_mul y.ub⟩
  | .nonneg, .nonpos => ⟨x.ub.toLowerBound.rat_mul y.lb, x.lb.toUpperBound.rat_mul y.ub⟩
  | .nonneg, .mixed => ⟨x.ub.toLowerBound.rat_mul y.lb, x.ub.rat_mul y.ub⟩
  | .nonpos, .nonneg => ⟨x.lb.rat_mul y.ub.toLowerBound, x.ub.rat_mul y.lb.toUpperBound⟩
  | .nonpos, .nonpos => ⟨x.ub.rat_mul y.ub |>.toLowerBound, x.lb.rat_mul y.lb |>.toUpperBound⟩
  | .nonpos, .mixed => ⟨x.lb.rat_mul y.ub.toLowerBound, x.lb.rat_mul y.lb |>.toUpperBound⟩
  | .mixed, .nonneg => ⟨x.lb.rat_mul y.ub.toLowerBound, x.ub.rat_mul y.ub⟩
  | .mixed, .nonpos => ⟨x.ub.toLowerBound.rat_mul y.lb, x.lb.rat_mul y.lb |>.toUpperBound⟩
  | .mixed, .mixed =>
      ⟨min (x.lb.rat_mul y.ub.toLowerBound) (x.ub.toLowerBound.rat_mul y.lb),
       max (x.lb.rat_mul y.lb |>.toUpperBound) (x.ub.rat_mul y.ub)⟩

@[interval_op RatReal]
theorem Interval.rat_mul_inclusion {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) (hsy : s ∈ y.toSet rat_to_real) :
    r * s ∈ (x.rat_mul y).toSet rat_to_real := by
  sorry

end Mul

section Div

def LowerBound.rat_div (lb₁ : LowerBound ℚ) (ub₂ : UpperBound ℚ) (lb₂ : LowerBound ℚ) :
    LowerBound ℚ :=
  match lb₁, ub₂ with
  | ⊥, ⊤ => ⊥
  | ⊥, some ⟨c, a⟩ => if a = 0 ∧ c ∧ lb₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩ else ⊥
  | some ⟨c, a⟩, ⊤ => if lb₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩ else some ⟨a = 0 ∧ c, 0⟩
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 then if lb₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩ else ⊥
      else if lb₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ / a₂⟩

def UpperBound.rat_div (ub₁ : UpperBound ℚ) (lb₂ : LowerBound ℚ) (ub₂ : UpperBound ℚ) :
    UpperBound ℚ :=
  match ub₁, lb₂ with
  | ⊤, ⊥ => ⊤
  | ⊤, some ⟨c, a⟩ => if a = 0 ∧ c ∧ ub₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩ else ⊤
  | some ⟨c, a⟩, ⊥ => if ub₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩ else some ⟨a = 0 ∧ c, 0⟩
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 then if ub₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩ else ⊤
      else if ub₂ = some ⟨true, 0⟩ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ / a₂⟩

def Interval.rat_div (x y : Interval ℚ) : Interval ℚ :=
    match x.toIntervalSignClass, y.toIntervalSignClass with
  | .nonneg, .nonneg =>
    ⟨x.lb.rat_div y.ub y.lb, x.ub.rat_div y.lb y.ub⟩
  | .nonpos, .nonpos =>
    ⟨x.ub.rat_div y.lb y.ub |>.toLowerBound, x.lb.rat_div y.ub y.lb |>.toUpperBound⟩
  | .nonpos, .nonneg =>
    ⟨x.lb.rat_div y.lb.toUpperBound y.ub.toLowerBound,
     x.ub.rat_div y.ub.toLowerBound y.lb.toUpperBound⟩
  | .nonneg, .nonpos =>
    ⟨x.ub.toLowerBound.rat_div y.ub y.lb, x.lb.toUpperBound.rat_div y.lb y.ub⟩
  | .mixed, .nonneg =>
    ⟨x.lb.rat_div y.lb.toUpperBound y.ub.toLowerBound, x.ub.rat_div y.lb y.ub⟩
  | .mixed, .nonpos =>
    ⟨x.ub.toLowerBound.rat_div y.ub y.lb, x.lb.rat_div y.ub y.lb |>.toUpperBound⟩
  | .nonneg, .mixed => if x = ⟨some ⟨true, 0⟩, some ⟨true, 0⟩⟩ then x else ⟨⊥,⊤⟩
  | .nonpos, .mixed => ⟨⊥, ⊤⟩
  | .mixed, .mixed => ⟨⊥, ⊤⟩

@[interval_op RatReal]
theorem Interval.rat_div_inclusion {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) (hsy : s ∈ y.toSet rat_to_real) :
    r / s ∈ (x.rat_div y).toSet rat_to_real := by
  sorry

end Div

section Pow

def Interval.rat_pow (x : Interval ℚ) (n : ℕ) : Interval ℚ :=
  let zero_lb : LowerBound ℚ := some ⟨true, 0⟩
  let zero_ub : UpperBound ℚ := some ⟨true, 0⟩
  if n = 0 then rat_const 1
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
      let q₁' := q₁.abs
      if q₁' < q₂ then some ⟨c₂, q₂ ^ n⟩
      else if q₁' = q₂ then some ⟨c₁ || c₂, q₂ ^ n⟩
      else some ⟨c₁, q₁' ^ n⟩
    | _, _ => ⊤
    ⟨zero_lb, ub⟩


@[interval_op RatReal]
theorem rat_pow_inclusion {r : ℝ} {x : Interval ℚ} (n : ℕ) (hrx : r ∈ x.toSet rat_to_real) :
    (r ^ n) ∈ (x.rat_pow n).toSet rat_to_real := by
  sorry

end Pow

/- Approximate Operations -/

section sqrt

def rat_sqrt_ub (n : ℕ) (q : ℚ) : ℚ :=
  match n with
  | 0 => q + 1
  | n + 1 => let p := rat_sqrt_ub n q; (1 / 2) * (p + q / p)

def rat_sqrt_lb (n : ℕ) (q : ℚ) : ℚ := q / rat_sqrt_ub n q

def Interval.rat_sqrt (n : ℕ) (x : Interval ℚ) : Interval ℚ  where
  lb := match x.lb with
    | ⊥ => some ⟨true, 0⟩
    | some ⟨c, a⟩ => if a < 0 then some ⟨true, 0⟩ else some ⟨c, rat_sqrt_lb n a⟩
  ub := match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ => if a ≤ 0 then some ⟨true, 0⟩ else some ⟨c, rat_sqrt_ub n a⟩

@[interval_op RatReal]
theorem rat_sqrt_inclusion {r : ℝ} {x : Interval ℚ} (approx_param : ℕ)
    (hrx : r ∈ x.toSet rat_to_real) :
    √ r ∈ (x.rat_sqrt approx_param).toSet rat_to_real := by
  sorry

end sqrt

section exp

def exp_aux_aux (n : ℕ) (q : ℚ) (term : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
    let term := term * (q / (n - k))
    term + exp_aux_aux n q term k

-- ∑ i ∈ Finset.range (2*(n + 1) + 1), (q ^ i) / (i !)
def exp_lb_aux (n : ℕ) (q : ℚ) : ℚ := exp_aux_aux (2*(n + 1) + 1) q 1 (2*(n + 1) + 1)

-- ∑ i ∈ Finset.range (2*(n + 1)), (q ^ i) / (i !)
def exp_ub_aux (n : ℕ) (q : ℚ) : ℚ := exp_aux_aux (2*(n + 1)) q 1 (2*(n + 1))

def exp_lb_non_pos (n : ℕ) (q : ℚ) : ℚ :=
  if q < -1 then (exp_lb_aux n (q / -q.floor)) ^ (- q.floor)
  else if q < 0 then exp_lb_aux n q
  else 1

def exp_ub_non_pos (n : ℕ) (q : ℚ) : ℚ :=
  if q < -1 then (exp_ub_aux n (q / -q.floor)) ^ (- q.floor)
  else if q < 0 then exp_ub_aux n q
  else 1

def exp_lb (n : ℕ) (q : ℚ) : ℚ :=
  if q < 0 then exp_lb_non_pos n q
  else 1 / exp_ub_non_pos n (- q)

def exp_ub (n : ℕ) (q : ℚ) : ℚ :=
  if q < 0 then exp_ub_non_pos n q
  else 1 / exp_lb_non_pos n (- q)

def Interval.rat_exp (n : ℕ) (x : Interval ℚ) : Interval ℚ where
  lb := match x.lb with
    | ⊥ => some ⟨false, 0⟩
    | some ⟨c, a⟩ => some ⟨c, exp_lb n a⟩
  ub := match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ => some ⟨c, exp_ub n a⟩

@[interval_op RatReal]
theorem rat_exp_inclusion (approx_param : ℕ) {r : ℝ} {x : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) :
    (Real.exp r) ∈ (x.rat_exp approx_param).toSet rat_to_real := by
  sorry

end exp

section pi

def atan_aux_aux (q_sq : ℚ) (n : ℕ) (d term : ℚ) : ℚ :=
  match n with
  | 0 => term
  | n + 1 =>
      let next := -term * q_sq * (d / (d + 2))
      term + atan_aux_aux q_sq n (d + 2) next

def atan_aux (q : ℚ) (n : ℕ) : ℚ :=
  atan_aux_aux (q ^ 2) n 1 q

def atan_lb (q : ℚ) (n : ℕ) : ℚ :=
  atan_aux q (2 * n + 1)

def atan_ub (q : ℚ) (n : ℕ) : ℚ :=
  atan_aux q (2 * n)

def Interval.ratPi (approx_param : ℕ) : Interval ℚ :=
  let lb := 16 * atan_lb (1 / 5) approx_param - 4 * atan_ub (1 / 239) approx_param
  let ub := 16 * atan_ub (1 / 5) approx_param - 4 * atan_lb (1 / 239) approx_param
  { lb := some ⟨false, lb⟩
    ub := some ⟨false, ub⟩ }

@[interval_op RatReal]
theorem Interval.rat_pi_inclusion (approx_param : ℕ) :
    Real.pi ∈ (Interval.ratPi approx_param).toSet rat_to_real := by
  sorry

end pi

end IntervalArithmetic
