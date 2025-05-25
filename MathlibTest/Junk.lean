import Mathlib

/-!
# Junk values in Lean and Mathlib

This file aims to document and test the various junk values used to keep functions total. Each
example is both an example application of the junk value, and a place to document and justify the
choice (hopefully, in addition to the actual definition).

This file can act as a reference guide for people who want to e.g. verify some theorem statement is
what they want, but perhaps are not so intimately familiar with all of Mathlib's API otherwise.

Most theorems should be provable by a simple calls to `simp`, `norm_num`, or `rfl`.
-/

/-! ## Truncating subtraction -/

/-- Nat subtraction: When subtracting a natural number `x` from a smaller one `y`, the value is
always zero. This is because we want to be able to also return a natural number, and so we can't
return a negative number. -/
example : (3 : ℕ) - (5 : ℕ) = 0 := by
  simp

/-- Because Nat subtraction truncates, it does not always agree with Int subtraction. -/
example : ↑(3 - 5 : ℕ) ≠ (3 - 5 : ℤ) := by
  simp

/-- Other types with a lower bound also truncate. `PNat`, the strictly positive natural numbers
(starting at 1), truncate at 1. Accordingly, they truncate even when subtracting a number from
itself. -/
example : (3 : ℕ+) - (5 : ℕ+) = 1 ∧ (10 : ℕ+) - (10 : ℕ+) = 1 := by
  and_intros <;> rfl

/-- `NNRat` truncates at 0. Here, `3 / 2 - 4 = 0`. -/
example : (3 : NNRat) / 2 - (4 : NNRat) = 0 := by
  decide +kernel

/-- `NNReal` truncates at 0. Here, `2 - π = 0`. -/
example : (2 : NNReal) - ⟨Real.pi, Real.pi_nonneg⟩ = 0 := by
  rw [tsub_eq_zero_iff_le]
  exact_mod_cast Real.two_le_pi

/-- `ENNReal` truncates subtraction at 0. Here, `π - ∞ = 0`. -/
example : ENNReal.ofNNReal ⟨Real.pi, Real.pi_nonneg⟩ - ⊤ = 0 := by
  simp

/-! ## Rounding division -/

/-- Doing division on types that aren't a `Group` or `GroupWithZero`, like `Nat`, typically
rounds down when it's defined. This is justified mostly by the typical behavior across many
programming languages, e.g. C, which do this with integer division. -/
example : 5 / 8 = 0 ∧ 100 / 6 = 16 := by
  norm_num

/-- For `Int`, rounding happens down if the denominator is positive, or up if the denominator is
negative. This is chosen so that `x / (-y) = -(x / y)` is always true. -/
example : (-10) / 3 = -4 ∧ (-10) / (-3) = 4 ∧ 10 / (-3) = -3 := by
  norm_num

/-! ## Division by zero -/

/-- Dividing a `Nat` by zero gives zero. Similarly for `Int`. -/
example : (1 : ℕ) / 0 = 0 ∧ (2 : ℤ) / 0 = 0 := by
  norm_num

/-! There's no division defined for `PNat`, so no worry about it giving 0 or 1. -/
/--
error: failed to synthesize
  HDiv ℕ+ ℕ+ ℕ+

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HDiv ℕ+ ℕ+ ℕ+

/-- In any `GroupWithZero`, division by zero gives the junk value zero. This includes, by extension,
any `Field` (like `Rat` or `Real`), as well as types like `NNRat` and `NNReal`. -/
example {G : Type*} [GroupWithZero G] :
    (10 : NNRat) / 0 = 0 ∧
    (20 : NNReal) / 0 = 0 ∧
    ∀ (x : G), x / 0 = 0 := by
  simp

/-- Division by zero also gives 0 in some more exotic non-groups like `EReal` and `Ordinal`. -/
example : (1 : EReal) / 0 = 0 ∧ Ordinal.omega0 / 0 = 0 := by
  simp

/-- Note that division by zero does _not_ give zero in `ENNReal`, where it gives `+∞` instead. -/
example : (1 : ENNReal) / 0 = ⊤ := by
  simp

/-! ## Arithmetic with Fin -/

/-- `Fin n` represents "natural numbers below n", and generally behaves like mod-n arithmetic. -/
example :
    (3 : Fin 5) + (4 : Fin 5) = 2 ∧
    (3 : Fin 5) * (2 : Fin 5) = 1 ∧
    (2 : Fin 9) ^ 4 = -2
    := by
  and_intros <;> rfl

/-- The design of `Fin` is heavily motivated by using it define the types like `UInt32`, which
describe twos-complement machine arithmetic. This means that division actually behaves like `Nat`
division, and not modular division. In this example, `3` and `11` are inverses modulo 16 and so
`(3 : Fin 16) * (11 : Fin 16) = 1`, but on the other hand `(1 : Fin 16) / (3 : Fin 16)` is
defined to have the same value as the natural number division `1 / 3`, which rounds down to 0.
-/
example :
    (3 : Fin 16) * (11 : Fin 16) = 1 ∧
    (1 : Fin 16) / (3 : Fin 16) = 0 := by
  and_intros <;> rfl

/-- `Fin` also allows arbitrary numeric literals, and simply casts them mod n. This can lead to
surprising looking true goals, like `x + 6 = x + 37`. Numeric literals can have a very
context-dependent meaning. -/
example (x : Fin 31) : x + 6 = x + 37 := by
  simp

/-! Here even the bare goal `6 = 37` turns out to be true. -/
/--
info: theorem extracted_1 : 6 = 37 := sorry
-/
#guard_msgs in
example {x : Fin 31} : x + 6 = x + 37 := by
  rw [add_right_inj]; clear x
  extract_goal
  simp

/-! ## Sqrt and Log-/

/-- `Nat.sqrt` rounds down to the nearest integer, again, in order to provide a `Nat` output. -/
example : Nat.sqrt 5 = 2 := by
  norm_num

/-- `Int.sqrt` and `Real.sqrt` obviously can take negative arguments, but we don't want to return
imaginary numbers, so they return 0 for any negative arguments. -/
example : (-3).sqrt = 0 ∧ (-Real.pi).sqrt = 0 := by
  constructor
  · rfl
  · simp [Real.sqrt_eq_zero', Real.pi_nonneg]

/-- `Nat.log2` rounds down. It uses the junk value `Nat.log2 0 = 0`. -/
example : Nat.log2 0 = 0 ∧ Nat.log2 100 = 6 := by
  and_intros <;> simp [Nat.log2]

/-- `Nat.log` generalizes this rounding down to arbitrary bases. If you wanted to instead round
up, there's `Nat.clog`, but it uses the same junk value when the argument is 0. When the base is
zero, the junk value is 0. -/
example : Nat.log 3 10 = 2 ∧ Nat.clog 3 10 = 3 ∧ Nat.log 0 100 = 0 := by
  simp [Nat.clog, Nat.log]

/-- `Int.log` could easily be mistaken to be a version of `Nat.log` for `Int` arguments instead.
In fact, `Int.log b x` is designed to try to extend `Nat.log` to give the appropriate negative value
when `x` is the interval `[0,1]`. The base `b` must be a natural number bases, so there's no worries
about what to do when the base is negative.

When the base `b` is 0, the same junk value of 0 is used as `Nat.log`. When the argument `x` is
zero or negative, the result is also zoer.
-/
example :
    Int.log 2 (100 / 3 : ℚ) = 5 ∧
    Int.log 0 Real.pi = 0 ∧
    Int.log 4 (0 : NNReal) = 0
    := by
  and_intros
  · rw [Int.log]
    rw [show ⌊_⌋₊ = 33 by decide +kernel, if_pos (by norm_num)]
    simp [Nat.log]
  · norm_num
  · norm_num

/-- `Real.log` needs to accept negative arguments. It agrees with the junk `Real.log 0 = 0`. For
negative arguments, `Real.log (-x) = Real.log x`. -/
example : Real.log 0 = 0 ∧ Real.log (-Real.exp 5) = 5 := by
  simp

/-- The function `ENNReal.log` maybe agrees most with the conventional notion of logarithm, that
the logarithm at 0 is negative infinity, and not supporting negative arguments. It returns an
`EReal` accordingly. By its behavior at 0, it breaks the pattern with `Nat.log`, `Int.log`, and
`Real.log`. -/
example : ENNReal.log 0 = ⊥ ∧ ENNReal.log ⊤ = ⊤ := by
  simp

/-! ## Arcsin and arccos -/

/-- Several functions on reals are defined using `OrderIso.symm`, for instead, `Real.arcsin`. This
means that the definition proceeds by starting with `Real.sin`, observing (in `Real.sinOrderIso`)
that it's a strictly monotonic and continuous map from `[-π/2, π/2]` to `[-1, 1]`, thus, a
bijection. Then inverting this function gives map from `[-1, 1]` to `[-π/2, π/2]`. Finally, this is
_extended_ to the whole reals, taking the extreme points `-π/2` and `π/2` as the minimal extension.

This means that `Real.arcsin x = -π/2` for all `x ≤ -1`, and it's `π/2` for all `x ≥ 1`.
-/
example : Real.arcsin (-4) = -(Real.pi/2) ∧ Real.arcsin 100 = Real.pi/2 := by
  norm_num

/-- Similarly, `Real.arccos` has the junk values of `π` on arguments less below `-1`, and `0` on
arguments above `1`. -/
example : Real.arccos (-37) = Real.pi ∧ Real.arccos 1037 = 0 := by
  norm_num

--TODO: rpow

/-! ## Indexing and lists -/

/-- Accessing a list `l : List α` with an "out of bounds" index is possible using the syntax `l[i]?` or
`l[i]!`. These are notations for `GetElem?.getElem?` and `GetElem?.getElem!`, respectively. The
former is "safe": it returns an `Option α`, which is `Option.none` if the index was out of bounds.

But `getElem!` takes an `Inhabited` instance on the type `α` and uses that as the junk value for
any extra indexing. In this example, we make a list of two natural numbers `[3, 5]` and access index
100. This gives the `Inhabited.default` value for `Nat`, which happens to be 0.
-/
example : [3, 5][100]! = 0 := by
  rfl

--TODO: explaining `get` and `getD`. Note that `get` takes a `Fin` and so naturally "wraps around".
