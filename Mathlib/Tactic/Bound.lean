/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Aesop
public meta import Mathlib.Tactic.Bound.Attribute
public meta import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Linarith.Frontend

/-!
## The `bound` tactic

`bound` is an `aesop` wrapper that proves inequalities by straightforward recursion on structure,
assuming that intermediate terms are nonnegative or positive as needed.  It also has some support
for guessing where it is unclear where to recurse, such as which side of a `min` or `max` to use
as the bound or whether to assume a power is less than or greater than one.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
by turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
uses specialized lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.

Additional hypotheses can be passed as `bound [h0, h1 n, ...]`.  This is equivalent to declaring
them via `have` before calling `bound`.

See `MathlibTest/Bound/bound.lean` for tests.

### Calc usage

Since `bound` requires the inequality proof to exactly match the structure of the expression, it is
often useful to iterate between `bound` and `rw / simp` using `calc`.  Here is an example:

```
-- Calc example: A weak lower bound for `z ↦ z^2 + c`
lemma le_sqr_add {c z : ℂ} (cz : abs c ≤ abs z) (z3 : 3 ≤ abs z) :
    2 * abs z ≤ abs (z^2 + c) := by
  calc abs (z^2 + c)
    _ ≥ abs (z^2) - abs c := by bound
    _ ≥ abs (z^2) - abs z := by bound
    _ ≥ (abs z - 1) * abs z := by rw [mul_comm, mul_sub_one, ← pow_two, ← abs.map_pow]
    _ ≥ 2 * abs z := by bound
```

### Aesop rules

`bound` uses threes types of aesop rules: `apply`, `forward`, and closing `tactic`s.  To register a
lemma as an `apply` rule, tag it with `@[bound]`.  It will be automatically converted into either a
`norm apply` or `safe apply` rule depending on the number and type of its hypotheses:

1. Nonnegativity/positivity/nonpositivity/negativity hypotheses get score 1 (those involving `0`).
2. Other inequalities get score 10.
3. Disjunctions `a ∨ b` get score 100, plus the score of `a` and `b`.

Score `0` lemmas turn into `norm apply` rules, and score `0 < s` lemmas turn into `safe apply s`
rules.  The score is roughly lexicographic ordering on the counts of the three type (guessing,
general, involving-zero), and tries to minimize the complexity of hypotheses we have to prove.
See `Mathlib/Tactic/Bound/Attribute.lean` for the full algorithm.

To register a lemma as a `forward` rule, tag it with `@[bound_forward]`.  The most important
builtin forward rule is `le_of_lt`, so that strict inequalities can be used to prove weak
inequalities.  Another example is `HasFPowerSeriesOnBall.r_pos`, so that `bound` knows that any
power series present in the context have positive radius of convergence.  Custom `@[bound_forward]`
rules that similarly expose inequalities inside structures are often useful.

### Guessing apply rules

There are several cases where there are two standard ways to recurse down an inequality, and it is
not obvious which is correct without more information.  For example, `a ≤ min b c` is registered as
a `safe apply 4` rule, since we always need to prove `a ≤ b ∧ a ≤ c`.  But if we see `min a b ≤ c`,
either `a ≤ c` or `b ≤ c` suffices, and we don't know which.

In these cases we declare a new lemma with an `∨` hypotheses that covers the two cases.  Tagging
it as `@[bound]` will add a +100 penalty to the score, so that it will be used only if necessary.
Aesop will then try both ways by splitting on the resulting `∨` hypothesis.

Currently the two types of guessing rules are
1. `min` and `max` rules, for both `≤` and `<`
2. `pow` and `rpow` monotonicity rules which branch on `1 ≤ a` or `a ≤ 1`.

### Closing tactics

We close numerical goals with `norm_num` and `linarith`.
-/

public meta section

open Lean Elab Meta Term Mathlib.Tactic Syntax
open Lean.Elab.Tactic (liftMetaTactic liftMetaTactic' TacticM getMainGoal)

namespace Mathlib.Tactic.Bound

/-!
### `.mpr` lemmas of iff statements for use as Aesop apply rules

Once Aesop can do general terms directly, we can remove these:

  https://github.com/leanprover-community/aesop/issues/107
-/

lemma Nat.cast_pos_of_pos {R : Type} [Semiring R] [PartialOrder R] [IsOrderedRing R] [Nontrivial R]
    {n : ℕ} : 0 < n → 0 < (n : R) :=
  Nat.cast_pos.mpr

lemma Nat.one_le_cast_of_le {α : Type} [AddCommMonoidWithOne α] [PartialOrder α]
    [AddLeftMono α] [ZeroLEOneClass α]
    [CharZero α] {n : ℕ} : 1 ≤ n → 1 ≤ (n : α) :=
  Nat.one_le_cast.mpr

/-!
### Apply rules for `bound`

Most `bound` lemmas are registered in-place where the lemma is declared. These are only the lemmas
that do not require additional imports within this file.
-/

-- Reflexivity
attribute [bound] le_refl

-- 0 ≤, 0 <
attribute [bound] sq_nonneg Nat.cast_nonneg abs_nonneg Nat.zero_lt_succ pow_pos pow_nonneg
  sub_nonneg_of_le sub_pos_of_lt inv_nonneg_of_nonneg inv_pos_of_pos tsub_pos_of_lt mul_pos
  mul_nonneg div_pos div_nonneg add_nonneg

-- 1 ≤, ≤ 1
attribute [bound] Nat.one_le_cast_of_le one_le_mul_of_one_le_of_one_le

-- ≤
attribute [bound] le_abs_self neg_abs_le neg_le_neg tsub_le_tsub_right mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right le_add_of_nonneg_right le_add_of_nonneg_left le_mul_of_one_le_right
  mul_le_of_le_one_right sub_le_sub add_le_add mul_le_mul

-- <
attribute [bound] Nat.cast_pos_of_pos neg_lt_neg sub_lt_sub_left sub_lt_sub_right add_lt_add_left
  add_lt_add_right mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right

-- min and max
attribute [bound] min_le_right min_le_left le_max_left le_max_right le_min max_le lt_min max_lt

-- Memorize a few constants to avoid going to `norm_num`
attribute [bound] zero_le_one zero_lt_one zero_le_two zero_lt_two

/-!
### Forward rules for `bound`
-/

-- Bound applies `le_of_lt` to all hypotheses
attribute [bound_forward] le_of_lt

/-!
### Guessing rules: when we don't know how to recurse
-/

section Guessing

variable {α : Type} [LinearOrder α] {a b c : α}

-- `min` and `max` guessing lemmas
lemma le_max_of_le_left_or_le_right : a ≤ b ∨ a ≤ c → a ≤ max b c := le_max_iff.mpr
lemma lt_max_of_lt_left_or_lt_right : a < b ∨ a < c → a < max b c := lt_max_iff.mpr
lemma min_le_of_left_le_or_right_le : a ≤ c ∨ b ≤ c → min a b ≤ c := min_le_iff.mpr
lemma min_lt_of_left_lt_or_right_lt : a < c ∨ b < c → min a b < c := min_lt_iff.mpr

-- Register guessing rules
attribute [bound]
  -- Which side of the `max` should we use as the lower bound?
  le_max_of_le_left_or_le_right
  lt_max_of_lt_left_or_lt_right
  -- Which side of the `min` should we use as the upper bound?
  min_le_of_left_le_or_right_le
  min_lt_of_left_lt_or_right_lt

end Guessing

/-!
### Closing tactics

TODO: Kim Morrison noted that we could check for `ℕ` or `ℤ` and try `lia` as well.
-/

/-- Close numerical goals with `norm_num` -/
meta def boundNormNum : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    let tac := do Mathlib.Meta.NormNum.elabNormNum .missing .missing .missing
    let goals ← Lean.Elab.Tactic.run i.goal tac |>.run'
    if !goals.isEmpty then failure
    return (#[], none, some .hundred)
attribute [aesop unsafe 10% tactic (rule_sets := [Bound])] boundNormNum

/-- Close numerical and other goals with `linarith` -/
meta def boundLinarith : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    Linarith.linarith false [] {} i.goal
    return (#[], none, some .hundred)
attribute [aesop unsafe 5% tactic (rule_sets := [Bound])] boundLinarith

/-!
### `bound` tactic implementation
-/

/-- Aesop configuration for `bound` -/
def boundConfig : Aesop.Options := {
  enableSimp := false,
  terminal := true
}

end Mathlib.Tactic.Bound

/-- `bound` tactic for proving inequalities via straightforward recursion on expression structure.

An example use case is

```
-- Calc example: A weak lower bound for `z ↦ z^2 + c`
lemma le_sqr_add (c z : ℝ) (cz : ‖c‖ ≤ ‖z‖) (z3 : 3 ≤ ‖z‖) :
    2 * ‖z‖ ≤ ‖z^2 + c‖ := by
  calc ‖z^2 + c‖
    _ ≥ ‖z^2‖ - ‖c‖ := by bound
    _ ≥ ‖z^2‖ - ‖z‖ := by  bound
    _ ≥ (‖z‖ - 1) * ‖z‖ := by
      rw [mul_comm, mul_sub_one, ← pow_two, ← norm_pow]
    _ ≥ 2 * ‖z‖ := by bound
```

`bound` is built on top of `aesop`, and uses
1. Apply lemmas registered via the `@[bound]` attribute
2. Forward lemmas registered via the `@[bound_forward]` attribute
3. Local hypotheses from the context
4. Optionally: additional hypotheses provided as `bound [h₀, h₁]` or similar. These are added to the
   context as if by `have := hᵢ`.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
by turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
contains lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.  Conversely, `gcongr` can prove
inequalities for more types of relations, supports all `positivity` functionality, and is likely
faster since it is more specialized (not built atop `aesop`). -/
syntax "bound" (" [" term,* "]")? : tactic

-- Plain `bound` elaboration, with no hypotheses
elab_rules : tactic
  | `(tactic| bound) => do
    let tac ← `(tactic| aesop (rule_sets := [Bound, -default]) (config := Bound.boundConfig))
    liftMetaTactic fun g ↦ do return (← Lean.Elab.runTactic g tac.raw).1

-- Rewrite `bound [h₀, h₁]` into `have := h₀, have := h₁, bound`, and similar
macro_rules
  | `(tactic| bound%$tk [$[$ts],*]) => do
    let haves ← ts.mapM fun (t : Term) => withRef t `(tactic| have := $t)
    `(tactic| ($haves;*; bound%$tk))

/-!
We register `bound` with the `hint` tactic.
-/

register_hint 70 bound
register_try?_tactic (priority := 70) bound
