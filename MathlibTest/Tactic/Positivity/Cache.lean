module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Positivity

/-! # Tests for the `positivity` cache

`trace.Tactic.positivity.cache` prints one line for every lookup that is answered from the cache.
-/

namespace Cache

/-! ### Repeated subterms are analysed only once -/

/--
trace: [Tactic.positivity.cache] new: x => nonnegative
[Tactic.positivity.cache] hit: x => nonnegative
[Tactic.positivity.cache] new: x + x => nonnegative
[Tactic.positivity.cache] hit: x + x => nonnegative
[Tactic.positivity.cache] new: x + x + (x + x) => nonnegative
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {x : ℤ} (hx : 0 ≤ x) : 0 ≤ (x + x) + (x + x) := by positivity

example {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ ((((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x))))
        + (((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x)))))
  := by positivity

example {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
        + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
  := by positivity

/-! ### Failures are cached too, and a cached failure is still a failure -/

/--
trace: [Tactic.positivity.cache] new: y => none
[Tactic.positivity.cache] new: |y| => nonnegative
[Tactic.positivity.cache] hit: y => none
[Tactic.positivity.cache] new: y * 2 => none
[Tactic.positivity.cache] new: |y * 2| => nonnegative
[Tactic.positivity.cache] new: |y| + |y * 2| => nonnegative
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {y : ℤ} : 0 ≤ |y| + |y * 2| := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x y : ℤ} (hx : 0 ≤ x) : 0 ≤ (y + x) * (y + x) := by positivity

/-! ### The cache survives a failing extension

The extension for `x * y` fails, since nothing is known about `y`, but the result for `x` that
was found on the way is still available afterwards. -/

/--
trace: [Tactic.positivity.cache] new: x => positive
[Tactic.positivity.cache] new: y => none
[Tactic.positivity.cache] new: x * y => none
[Tactic.positivity.cache] new: |x * y| => nonnegative
[Tactic.positivity.cache] hit: x => positive
[Tactic.positivity.cache] new: |x * y| + x => positive
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {x y : ℤ} (hx : 0 < x) : 0 < |x * y| + x := by positivity

/-! ### Results found without a `PartialOrder` are kept apart from those found with one

`ℂ` has no `PartialOrder` instance here, so for `(t : ℂ)` the `Nat.cast` extension asks whether
`t ≠ 0` *without* an order, and the answer is `nonzero`. For `(t : ℤ)` it asks about the same `t`
*with* the order on `ℕ`, and needs the answer `positive`. So the first answer must not be reused
for the second question: there are two `new: t` lines below, and no `hit: t` line. -/

/--
trace: [Tactic.positivity.cache] new: t => nonzero
[Tactic.positivity.cache] new: ↑t => nonzero
[Tactic.positivity.cache] new: t => positive
[Tactic.positivity.cache] new: ↑t => positive
[Tactic.positivity.cache] new: c => nonzero
[Tactic.positivity.cache] new: ↑t * c => nonzero
[Tactic.positivity.cache] new: ↑(↑t * c) => nonzero
[Tactic.positivity.cache] new: ↑t * ↑(↑t * c) => nonzero
[Tactic.positivity.cache] hit: ↑t => positive
[Tactic.positivity.cache] hit: c => nonzero
[Tactic.positivity.cache] hit: c => nonzero
[Tactic.positivity.cache] new: c * c => nonzero
[Tactic.positivity.cache] new: ↑t * (c * c) => nonzero
[Tactic.positivity.cache] new: ↑(↑t * (c * c)) => nonzero
[Tactic.positivity.cache] new: ↑t * ↑(↑t * c) * ↑(↑t * (c * c)) => nonzero
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example (t : ℕ) (c : ℤ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (t : ℂ) * (((t : ℤ) * c : ℤ) : ℂ) * (((t : ℤ) * (c * c) : ℤ) : ℂ) ≠ 0 := by positivity

example (t : ℕ) (c : ℤ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (t : ℂ) * (((t : ℤ) * c : ℤ) : ℂ) ≠ 0 := by positivity

example (t : ℕ) (c : ℤ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (((t : ℤ) * c : ℤ) : ℂ) * (t : ℂ) ≠ 0 := by positivity

/-! ### The cache is shared with subterms under a binder -/

/--
trace: [Tactic.positivity.cache] new: x => nonnegative
[Tactic.positivity.cache] hit: x => nonnegative
[Tactic.positivity.cache] new: x + x => nonnegative
[Tactic.positivity.cache] new: ?_ => nonnegative
[Tactic.positivity.cache] new: ↑?_ => nonnegative
[Tactic.positivity.cache] new: (x + x) * ↑?_ => nonnegative
[Tactic.positivity.cache] new: ∑ i ∈ s, (x + x) * ↑i => nonnegative
[Tactic.positivity.cache] hit: x + x => nonnegative
[Tactic.positivity.cache] new: ∑ i ∈ s, (x + x) * ↑i + (x + x) => nonnegative
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {x : ℤ} (hx : 0 ≤ x) (s : Finset ℕ) : 0 ≤ ∑ i ∈ s, (x + x) * (i : ℤ) + (x + x) := by
  positivity

end Cache
