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

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
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
info: theorem _example.extracted_1 : 6 = 37 := sorry
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
  and_intros <;> rfl

/-- `Nat.log` generalizes this rounding down to arbitrary bases. If you wanted to instead round
up, there's `Nat.clog`, but it uses the same junk value when the argument is 0. When the base is
zero, the junk value is 0. -/
example : Nat.log 3 10 = 2 ∧ Nat.clog 3 10 = 3 ∧ Nat.log 0 100 = 0 := by
  simp [Nat.clog, Nat.log]

/-- `Int.log` could easily be mistaken to be a version of `Nat.log` for `Int` arguments instead.
In fact, `Int.log b x` is designed to try to extend `Nat.log` to give the appropriate negative value
when `x` is the interval `[0,1]`. The base `b` must be a natural number base, so there's no worries
about what to do when the base is negative.

When the base `b` is 0, the same junk value of 0 is used as `Nat.log`. When the argument `x` is
zero or negative, the result is also zero.
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
the logarithm of 0 is negative infinity, and not supporting negative arguments. It returns an
`EReal` accordingly. By its behavior at 0, it breaks the pattern with `Nat.log`, `Int.log`, and
`Real.log`. -/
example : ENNReal.log 0 = ⊥ ∧ ENNReal.log ⊤ = ⊤ := by
  simp

/-- Real powers `(_ : ℝ) ^ (_ : ℝ)` agree with the conventional definition when the base is
nonnegative, and we define them in order to agree with natural numbers where applicable. This means
adopting the convention that `0 ^ 0 = 1` (which is otherwise sometimes debated). -/
example : (0 : ℝ) ^ (0 : ℝ) = 1 := by
  simp

/-- The behavior on negative bases is strange enough that it's often considered "junk", though.
It's defined as the real part of the complex power `(_ : ℂ) ^ (_ : ℂ)`, which is turn defined as
`fun x y ↦ exp (y * log x)`. The resulting definition for reals can be expressed in terms of
`Real.exp`, `Real.log`, and `Real.cos`. In particular, this does _not_ agree with the schoolbook
definition of odd roots of negative numbers, i.e. `(-1) ^ (1/3) ≠ -1`.

In this example, `(-8) ^ (5/3) = 16`. Contrast with how it might "conventionally" have the value of
`((-8) ^ (1/3)) ^ 5 = (-2) ^ 5 = -32`.
-/
example : (-8 : ℝ) ^ (5/3 : ℝ) = 16 := by
  rw [Real.rpow_def_of_neg (by norm_num), Real.log_neg_eq_log]
  rw [← Real.cos_two_pi_sub, ← sub_mul, mul_comm (_ - _)]
  norm_num
  rw [mul_div Real.pi, mul_one, Real.cos_pi_div_three]
  suffices Real.exp (Real.log 8 * (5 / 3)) = Real.exp (Real.log 32) by
    rw [this, Real.exp_log (by positivity)]
    norm_num
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (32 : ℝ) = 2 ^ 5 by norm_num]
  simp only [Real.log_pow, Nat.cast_ofNat]
  ring_nf

/-- The binary entropy function `Real.binEntropy` is simply defined in terms of `Real.log` as
`p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹`, so it happily provides junk values outside of its
traditional domain `[0, 1]`. In this example, the entropy of the "probability" `-1` turns out to be
`-2 * log 2`. -/
example : Real.binEntropy (-1) = -2 * Real.log 2 := by
  simp only [Real.binEntropy, Real.log_inv]
  norm_num

/-! ## Arcsin and arccos -/

/-- Several functions on reals are defined using `OrderIso.symm`, for instead, `Real.arcsin`. This
means that the definition proceeds by starting with `Real.sin`, observing (in `Real.sinOrderIso`)
that it's a strictly monotonic and continuous map from `[-π/2, π/2]` to `[-1, 1]`, thus, a
bijection. Then inverting this function gives a map from `[-1, 1]` to `[-π/2, π/2]`. Finally, this is
_extended_ to the whole reals, taking the extreme points `-π/2` and `π/2` as the minimal extension.

This means that `Real.arcsin x = -π/2` for all `x ≤ -1`, and it's `π/2` for all `x ≥ 1`.
-/
example : Real.arcsin (-4) = -(Real.pi/2) ∧ Real.arcsin 100 = Real.pi/2 := by
  norm_num

/-- Similarly, `Real.arccos` has the junk values of `π` on arguments less below `-1`, and `0` on
arguments above `1`. -/
example : Real.arccos (-37) = Real.pi ∧ Real.arccos 1037 = 0 := by
  norm_num

/-! ## Indexing and lists -/

/-- Accessing a list `l : List α` with an "out of bounds" index is possible using the syntax `l[i]?` or
`l[i]!`. These are notations for `GetElem?.getElem?` and `GetElem?.getElem!`, respectively. The
former is "safe": it returns an `Option α`, which is `Option.none` if the index was out of bounds.

But `getElem!` takes an `Inhabited` instance on the type `α` and uses that as the junk value for
any extra indexing. In this example, we make a list of two natural numbers `[3, 5]` and access index
100. This gives the `Inhabited.default` value for `Nat`, which happens to be 0.
-/
example : [3, 5][100]! = default ∧ default = 0 := by
  and_intros <;> rfl

/-- A list can also be accessed through `List.get` and `List.getD`. `List.get` takes a
`Fin l.length`, which is guaranteed to be within bounds; in this sense, it must be "safe". But
recall that `Fin` accepts _numerals_ outside the range, casting them mod n. In this example,
accessing a length-5 list at index (numeric literal) 12 gives element 2. -/
example :
    let l : List ℕ := [100,200,300,400,500];
    have h : l.length = 5 := rfl;
    let index : Fin l.length := h ▸ 12;
    l.get index = 300 := by
  rfl

/-- The `getD` operation gets an element with a Nat index, but returns an (explicitly provided)
default value if out of range. Here, we provide a default value of 37, which is what we then get out
since we access out-of-bounds at index 12. -/
example : [100,200,300,400,500].getD 12 37 = 37 := by
  rfl

/- Finally there's `List.get!`, which gives the default value from `Inhabited` like `getElem!`,
and so is equivalent as far as theorem proving goes; but (if run in a program) causes a panic.

This is currently deprecated in favor of `[i]!`, the `getElem!` syntax.

Note that similar APIs are duplicated across several types: e.g. `Vector.get`, `Array.getD`,
`String.get!`, `Option.getD`, etc.
-/
#guard_msgs(drop warning) in
example : [100,200,300,400,500].get! 12 = default := by
  rfl

/- Trying to evaluate the expression leads to a panic. -/
#guard_msgs(drop all) in
#eval [100,200,300,400,500].get! 12

/-! # Strings -/

/-- `String.get`, `String.get!`, and `String.get?` generally mimic arrays and lists by accessing
individual characters within the String, as if it were a `List Char`. The junk value is the
character `'A'`.

But there's the additional complication that UTF-8 characters (the encoding of Strings in Lean) are
a variable number of bytes, so even though the index is a byte offset, this can point to an invalid
location if it lands in the middle of a character.

`String.get'` splits the difference by requiring a proof (or as the documentation calls it, merely
"evidence") that the index is within bounds, but it will still give the junk `'A'` if it lands in
the middle of a character. -/
example :
    "Hello!".get 0 = 'H' ∧
    "Hello!".get (.mk 100) = default ∧
    "Hello!".get! (.mk 100) = default ∧
    "Hello!".get? (.mk 100) = none ∧
    "Hello!".get' (.mk 3) (by decide) = 'l' ∧
    "⋃ℕℐℂ₀𝔻ℰ".get' (.mk 2) (by decide) = default ∧
    "⋃ℕℐℂ₀𝔻ℰ".get' (.mk 3) (by decide) = 'ℕ' ∧
    default = 'A'
    := by
  and_intros <;> rfl

/-! # Derivatives -/

/-- The derivative of a function at a point where it's not differentiable is given the junk
value of 0. In this example, the derivative of `7x + |x|` at `x = 0` is equal to 0 (even though
the "sensible" values would be 6, 8, or maybe 7).

This holds for the many variants of derivatives, like `fderiv`, `fderivWithin`, etc.

Note this junk value can mean expressions like "twice differentiable" can be harder to express
than you think: the function `if (x = 0) then 1 else x ^ 2` isn't differentiable at 0, but its
derivative simplifies to `if (x = 0) then 0 else 2 * x`, which is just `2 * x`, and so its
derivative is differentiable everywhere.

In that example, instead of writing `Differentiable (deriv f)`, use `ContDiff ℝ 2 f`.
-/
example : deriv (fun (x : ℝ) ↦ 7 * x + |x|) 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  by_contra h
  have h₂ : DifferentiableAt ℝ (fun (x : ℝ) ↦ (-7) * x) 0 := by
    fun_prop
  apply not_differentiableAt_abs_zero
  simpa [Pi.add_def] using h₂.add h

/-- Another version is that `analyticOrderAt` and `analyticOrderNatAt` give the junk value
0 when the function isn't analytic at the point. -/
example : analyticOrderAt Real.log 0 = 0 := by
  apply analyticOrderAt_of_not_analyticAt
  by_contra h
  replace h := AnalyticAt.continuousAt h
  simp at h

/- # Find and Nth -/

/-- The function `Nat.nth p n` gives the `n+1`th natural number satisfying a predicate, but if there
are not this many, it is defined to give the junk index 0. Here, we ask for the 5th prime that's
less than 10, and find the answer is 0.

`Nat.find` is similar in its purpose (it only returns the first one, see `Nat.nth_zero_of_exists`),
but "safe"  in the sense that it requires a proof that there is a natural number satisfying the
condition. `Nat.Subtype.ofNat` functions similar to `Nat.nth` but takes a proof that the set is
infinite.
-/
example : Nat.nth (fun n ↦ n < 10 ∧ n.Prime) 4 = 0 := by
  apply Nat.nth_of_card_le (Set.Finite.sep (Set.finite_lt_nat 10) _) ?_
  conv in Set.Finite.toFinset _ =>
    equals {2, 3, 5, 7} =>
      ext
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rw [and_imp]
        decide +revert
      · rintro (_|_|_|_) <;> subst ‹ℕ› <;> decide
  rfl
