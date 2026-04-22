module

public import Mathlib.Tactic.IntervalArithmetic.Core
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Sqrt

set_option linter.style.header false

@[expose] public section

namespace IntervalArithmetic

def rat_to_real : ℚ → ℝ := fun x ↦ x

@[interval_arithmetic_decl RatReal]
theorem strictMono_rat_to_real : StrictMono rat_to_real := by
  intro x y hxy
  simp [rat_to_real, hxy]

/- Constants -/

def rat_const (q : ℚ) : Interval ℚ := ⟨some ⟨true, q⟩, some ⟨true,q⟩⟩

@[exact_interval_op RatReal]
def rat_const_inclusion (q : ℚ) : ↑q ∈ (rat_const q).toSet rat_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, rat_const, rat_to_real]

def rat_of_scientific_const (m : ℕ) (s : Bool) (e : ℕ) : Interval ℚ :=
  rat_const (Rat.ofScientific m s e)

@[exact_interval_op RatReal]
def rat_of_scientific_inclusion (m : ℕ) (s : Bool) (e : ℕ) :
  (OfScientific.ofScientific (α := ℝ) m s e)
  ∈ (rat_of_scientific_const m s e).toSet rat_to_real := by sorry

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

/- ## Tactic Tests -/

example : (0 : ℝ) ≤ 1 := by
  interval RatReal 0

example : (0 : ℝ) < 1 := by
  interval RatReal 10

example : (1 : ℝ) ≤ 1 := by
  interval RatReal 10

example : (1 : ℝ) < 2 := by
  interval RatReal 10

example : (2 : ℝ) + √ 3 ≤ √ 24 := by
  interval RatReal 10

example : (2 : ℝ) + 3 < 6 := by
  interval RatReal 10

-- Two variables
example {r s : ℝ}
    (hr : r ∈ (rat_const (1 : ℚ)).toSet rat_to_real)
    (hs : s ∈ (rat_const (2 : ℚ)).toSet rat_to_real) :
    r + s ≤ 3 := by
  interval RatReal 10

-- Repeated variable
example {r : ℝ}
    (hr : r ∈ (nat_const 1).toSet rat_to_real) :
    r + r ≤ 2 := by
  interval RatReal 10

-- same variable on both sides
example {r : ℝ} (hr : r ∈ (nat_const 2).toSet rat_to_real) : r ≤ r := by
  interval RatReal 10

example {r s : ℝ}
    (hr : r ∈ (nat_const 0).toSet rat_to_real)
    (hs : s ∈ (nat_const 1).toSet rat_to_real) :
    r < s := by
  interval RatReal 10

-- variables embedded in larger expressions on both sides
example {r s : ℝ}
    (hr : r ∈ (nat_const 1).toSet rat_to_real)
    (hs : s ∈ (nat_const 2).toSet rat_to_real) :
    r + 1 ≤ s + 0 := by
  interval RatReal 10

def Iccq (a b : ℚ) : Interval ℚ := ⟨some ⟨true, a⟩,  some ⟨true, b⟩⟩
def Icoq (a b : ℚ) : Interval ℚ := ⟨some ⟨true, a⟩,  some ⟨false, b⟩⟩
def Iocq (a b : ℚ) : Interval ℚ := ⟨some ⟨false, a⟩, some ⟨true, b⟩⟩
def Iooq (a b : ℚ) : Interval ℚ := ⟨some ⟨false, a⟩, some ⟨false, b⟩⟩
def Iciq (a : ℚ) : Interval ℚ := ⟨some ⟨true, a⟩, ⊤⟩
def Iicq (b : ℚ) : Interval ℚ := ⟨⊥, some ⟨true, b⟩⟩

/- ## Non-singleton interval tests -/

-- plain variable-vs-variable
example {r s : ℝ}
    (hr : r ∈ (Iccq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iccq 2 3).toSet rat_to_real) :
    r ≤ s := by
  interval RatReal 10

example {r s : ℝ}
    (hr : r ∈ (Iccq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iccq 2 3).toSet rat_to_real) :
    r < s := by
  interval RatReal 10

-- touching closed intervals: only ≤ should work
example {r s : ℝ}
    (hr : r ∈ (Iccq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iccq 1 2).toSet rat_to_real) :
    r ≤ s := by
  interval RatReal 10

-- open/closed endpoint interaction for strict inequality
example {r s : ℝ}
    (hr : r ∈ (Icoq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iccq 1 2).toSet rat_to_real) :
    r < s := by
  interval RatReal 10

example {r s : ℝ}
    (hr : r ∈ (Iccq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iocq 1 2).toSet rat_to_real) :
    r < s := by
  interval RatReal 10

example {r s : ℝ}
    (hr : r ∈ (Iooq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iccq 1 2).toSet rat_to_real) :
    r < s := by
  interval RatReal 10

-- variables on both sides inside larger expressions

example {r s : ℝ}
    (hr : r ∈ (Iccq 0 1).toSet rat_to_real)
    (hs : s ∈ (Iccq 2 3).toSet rat_to_real) :
    r + 1 ≤ s := by
  interval RatReal 10

example {r s : ℝ}
    (hr1 : r ∈ (Iccq 0 2).toSet rat_to_real)
    (hr2 : r ∈ (Iccq 1 3).toSet rat_to_real)
    (hs1 : s ∈ (Iccq 0 1).toSet rat_to_real)
    (hs2 : s ∈ (Iccq (-1) 2).toSet rat_to_real) :
    r + s ≤ 3 := by
  interval RatReal 10

-- clean!

example {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : r ≤ 1 := by
  interval RatReal 10

example {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ r := by
  interval RatReal 10

example {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : r + 1 ≤ 2 := by
  interval RatReal 10

example {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) : 0 < r + s := by
  interval RatReal 10

example {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 0 < r := by
  interval RatReal 10

example {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : r < 1 := by
  interval RatReal 10

example {r : ℝ} (h0 : -1 ≤ r) (h1 : r ≤ 2) : r + 1 ≤ 3 := by
  interval RatReal 10

/- # MORE EXAMPLES -/

example : 0 ≤ ((0.34 : ℚ) : ℝ) := by
  interval RatReal 10

example (x : ℝ) (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) :
    0 ≤ x - 1 := by
  interval RatReal 10

example : Real.sqrt 2 ≤ 2 := by
  interval RatReal 10

example (x : ℝ) (hx : 1 ≤ x) (hx : x ≤ 2) : 0 ≤ x - x + 1 := by
  interval RatReal 10

end IntervalArithmetic
