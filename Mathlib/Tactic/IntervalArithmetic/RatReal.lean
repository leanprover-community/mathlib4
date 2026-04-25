module

public import Mathlib.Tactic.IntervalArithmetic.Core
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Complex.Exponential

set_option linter.style.header false

@[expose] public section

open Nat

namespace IntervalArithmetic

def rat_to_real : ℚ → ℝ := fun x ↦ x

@[interval_arithmetic_decl RatReal]
theorem strictMono_rat_to_real : StrictMono rat_to_real := by
  intro x y hxy
  simp [rat_to_real, hxy]

/- "Unfolders / Converters" -/

def rat_const (q : ℚ) : Interval ℚ := ⟨some ⟨true, q⟩, some ⟨true,q⟩⟩

@[exact_interval_op RatReal]
def rat_const_inclusion (q : ℚ) : ↑q ∈ (rat_const q).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, rat_const, rat_to_real]

def rat_of_scientific_const (m : ℕ) (s : Bool) (e : ℕ) : Interval ℚ :=
  rat_const (Rat.ofScientific m s e)

@[exact_interval_op RatReal]
def rat_of_scientific_inclusion (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e)
    ∈ (rat_of_scientific_const m s e).toSet rat_to_real := by
  exact rat_const_inclusion _

def nat_const (n : ℕ) : Interval ℚ := ⟨some ⟨true, n⟩, some ⟨true, n⟩⟩

@[exact_interval_op RatReal]
def of_nat_inclusion (n : ℕ) : (OfNat.ofNat n) ∈ (nat_const n).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, rat_to_real, nat_const,
    Semiring.toGrindSemiring_ofNat ℝ n]

@[exact_interval_op RatReal]
def nat_const_inclusion (n : ℕ) : ↑n ∈ (nat_const n).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, nat_const, rat_to_real]

/- Exact Uniary Operation -/

def Interval.rat_neg (x : Interval ℚ) : Interval ℚ where
  lb := match x.ub with
    | ⊤ => ⊥
    | some ⟨c, a⟩ => some ⟨c, -a⟩
  ub := match x.lb with
    | ⊥ => ⊤
    | some ⟨c, a⟩ => some ⟨c, -a⟩

@[exact_interval_op RatReal]
def rat_neg_inclusion {r : ℝ} (x : Interval ℚ) (hrx : r ∈ x.toSet rat_to_real) :
    -r ∈ (x.rat_neg.toSet rat_to_real) := by
  simp only [Interval.rat_neg, Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds,
    rat_to_real] at hrx ⊢
  constructor
  · cases hx : x.ub <;> simp [hx] at hrx ⊢; grind
  · cases hx : x.lb <;> simp [hx] at hrx ⊢; grind

/- Exact Binary Ops -/

def Interval.rat_add (x y : Interval ℚ) : Interval ℚ where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩

@[exact_interval_op RatReal]
theorem rat_add_inclusion {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) (hsy : s ∈ y.toSet rat_to_real) :
    (r + s) ∈ (x.rat_add y).toSet rat_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.rat_add,
    rat_to_real] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.lb
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp only [hx, h₁, Bool.false_eq_true, ↓reduceIte, hy, h₂, Bool.and_self,
         Rat.cast_add] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.ub
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp only [hx, h₁, Bool.false_eq_true, ↓reduceIte, hy, h₂, Bool.and_self,
         Rat.cast_add] at hrx hsy ⊢ <;> grind
    all_goals simp

def Interval.rat_sub (x y : Interval ℚ) : Interval ℚ where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩

@[exact_interval_op RatReal]
theorem rat_sub_inclusion {r s : ℝ} {x y : Interval ℚ}
    (hrx : r ∈ x.toSet rat_to_real) (hsy : s ∈ y.toSet rat_to_real) :
    (r - s) ∈ (x.rat_sub y).toSet rat_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.rat_sub,
    rat_to_real] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.ub
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp only [hx, h₁, Bool.false_eq_true, ↓reduceIte, hy, h₂, Bool.and_self,
         Rat.cast_sub] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.lb
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp only [hx, h₁, Bool.false_eq_true, ↓reduceIte, hy, h₂, Bool.and_self,
         Rat.cast_sub] at hrx hsy ⊢ <;> grind
    all_goals simp

-- mul

def Interval.rat_mul (x y : Interval ℚ) : Interval ℚ :=
  sorry

def Interval.rat_pow (x : Interval ℚ) (n : ℕ) : Interval ℚ :=
  let zero_lb : LowerBound ℚ := some ⟨true, 0⟩
  let zero_ub : UpperBound ℚ := some ⟨true, 0⟩
  if n = 0 then rat_const 1
  else if zero_lb ≤ x.lb || Odd n then
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

@[exact_interval_op RatReal]
theorem rat_pow_inclusion {r : ℝ} {x : Interval ℚ} (n : ℕ) (hrx : r ∈ x.toSet rat_to_real) :
    (r ^ n) ∈ (x.rat_pow n).toSet rat_to_real := by
  sorry

/- Approx Uniary Operation -/

def rat_sqrt_lb (n : ℕ) (q : ℚ) : ℚ :=
  let n := n.succ
  Nat.sqrt (q.num.natAbs * n ^ 2 / q.den) / n

def rat_sqrt_ub (n : ℕ) (q : ℚ) : ℚ :=
  let n := n.succ
  (Nat.sqrt (q.num.natAbs * n ^ 2 / q.den) + 1) / n

def Interval.rat_sqrt (n : ℕ) (x : Interval ℚ) : Interval ℚ  where
  lb := match x.lb with
    | ⊥ => some ⟨true, 0⟩
    | some ⟨c, a⟩ => if a < 0 then some ⟨true, 0⟩ else some ⟨c, rat_sqrt_lb n a⟩
  ub := match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ => if a ≤ 0 then some ⟨true, 0⟩ else some ⟨c, rat_sqrt_ub n a⟩

@[approx_interval_op RatReal]
theorem rat_sqrt_inclusion (n : ℕ) {r : ℝ} {x : Interval ℚ} (hrx : r ∈ x.toSet rat_to_real) :
    √ r ∈ (x.rat_sqrt n).toSet rat_to_real := by
  sorry

-- exp

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

@[approx_interval_op RatReal]
theorem rat_exp_inclusion (n : ℕ) {r : ℝ} {x : Interval ℚ} (hrx : r ∈ x.toSet rat_to_real) :
    (Real.exp r) ∈ (x.rat_exp n).toSet rat_to_real := by
  sorry

end IntervalArithmetic
