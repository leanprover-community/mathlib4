module
import Mathlib.Tactic.Basify
import Mathlib.Tactic

open scoped NNReal ENNReal

set_option linter.unnecessarySeqFocus false

/-! ### `ℝ≥0∞` -/

example : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ = 4⁻¹ := by
  basify
  norm_num

example (a b : ℝ≥0∞) : a + b = b + a := by
  basify
  ring

example (a b : ℝ≥0∞) : a * b = b * a := by
  basify <;> ring

example (a b c : ℝ≥0∞) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  basify
  linarith

example (a b : ℝ≥0∞) (h : a + b = 0) : a = 0 := by
  basify <;> linarith

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a + b ≠ ⊤ := by
  basify

example (a : ℝ≥0∞) : a ≤ a + 1 := by
  basify <;> linarith

/-- Truncated subtraction becomes `max (· - ·) 0`. -/
example (a b : ℝ≥0∞) (hb : b ≠ ⊤) (h : a ≤ b) : a - b = 0 := by
  basify
  exact max_eq_right (sub_nonpos.2 h)

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) : (a + b).toReal = a.toReal + b.toReal := by
  basify

/-- An atom that is not a local hypothesis is generalized first. -/
example (f : ℕ → ℝ≥0∞) : f 0 + f 1 = f 1 + f 0 := by
  basify
  ring

/-- A reducible alias, used to exercise deduplication of atoms up to definitional unfolding. -/
@[reducible] def twoAlias : ℕ := 2

/-- Atoms are interned with `AtomM`, so `f twoAlias` and `f 2` are one atom rather than two.
Deduplicating them syntactically instead generalizes the second occurrence to a variable that never
gets case split, and leaves the goal sitting in `ℝ≥0∞`. -/
example (f : ℕ → ℝ≥0∞) : f twoAlias ≤ f 2 + f twoAlias := by
  basify
  linarith

/-- An opaque function and a reducible alias of it, to exhibit the limitation below. -/
opaque opaqueF : ℕ → ℝ≥0∞

@[reducible] noncomputable def aliasF (n : ℕ) : ℝ≥0∞ := opaqueF n

/-- `aliasF 0` and `opaqueF 0` are definitionally equal but have different head symbols, so no
single `kabstract` pattern abstracts both occurrences: `generalizeHyp` filters candidate subterms
by head symbol before trying `isDefEq`. `AtomM` still identifies them, so only one of the two is
generalized, and the other is left for the final `simp_all` to rewrite through the recorded
equation. The result is a single variable, as it should be -- though with the case-split binders
left anonymous this example can no longer assert that; the deduplication itself is pinned by the
`twoAlias` test above, which fails outright without it. -/
example : opaqueF 0 ≤ aliasF 0 := by
  basify
  exact le_rfl

/-- `g a` is an atom, since `g` is not a registered operation: it is split as a whole rather than
being descended into. -/
example (g : ℝ≥0∞ → ℝ≥0∞) (a : ℝ≥0∞) : g a ≤ g a + 1 := by
  basify <;> linarith

example (g : ℝ≥0∞ → ℝ≥0∞) (a b : ℝ≥0∞) (h : g a ≤ g b) : g a + g b = g b + g a := by
  basify <;> linarith

example (a : ℝ≥0∞) (h : a ≠ 0) (h' : a ≠ ⊤) : a * a⁻¹ = 1 := by
  basify
  field_simp

example (a b : ℝ≥0∞) (hb : b ≠ ⊤) (h : a ≤ b) : a ≠ ⊤ := by
  basify

example (a : ℝ≥0∞) (n : ℕ) (h : a ≠ ⊤) : a ^ n ≠ ⊤ := by
  basify

/-- The `ℝ≥0∞` arithmetic at the heart of `Wiedijk100Theorems.first_vote_neg`: `A` stands for the
measure of a set, which is an atom, so it is generalized and split, and everything else moves to
`ℝ`. The original proof spelled out `ENNReal.eq_sub_of_add_eq`, `ENNReal.eq_div_iff`,
`ENNReal.mul_sub`, `ENNReal.mul_div_cancel` and `ENNReal.add_sub_cancel_left` by hand. -/
example (A : ℝ≥0∞) (p q : ℕ) (h : 0 < p + q) (hA : A + p / (p + q) = 1) : A = q / (p + q) := by
  have h' : (p + q : ℝ≥0∞) ≠ 0 := mod_cast h.ne'
  basify
  field_simp at hA ⊢
  linarith

/-! ### `ℝ≥0`

`ℝ≥0` is a subtype, so its eliminator has a single case: it replaces an atom by `x.toNNReal` with
`x : ℝ` and `0 ≤ x`, and the propositions then move to `ℝ`.

Little of that is new. `ℝ≥0` is a semifield, so `ring` and `field_simp` work on it natively, and
`linarith` ships a preprocessor (`Mathlib/Tactic/Linarith/NNRealPreprocessor.lean`) that performs
much the same move: shift the (in)equalities to `ℝ` and add `NNReal.coe_nonneg` for each atom.
`rify` shifts the propositions without the nonnegativity facts, and `push_cast`/`norm_cast` have
nothing to do on a goal stated purely in `ℝ≥0` -- there is no cast in it to move.

These tests therefore check two things: that `basify` agrees with the existing tactics where
they already work, and what it does with truncated subtraction, which is the one place the two
disagree.
-/

example (a : ℝ≥0) : 0 ≤ a := by
  basify

/-! #### Goals the existing tactics already handle -/

example (a b c : ℝ≥0) : (a + b) * c = a * c + b * c := by ring

example (a b c : ℝ≥0) : (a + b) * c = a * c + b * c := by
  basify
  ring

example (a b : ℝ≥0) : ((a + b : ℝ≥0) : ℝ) = a + b := by push_cast; ring

example (a b : ℝ≥0) : ((a + b : ℝ≥0) : ℝ) = a + b := by
  basify

example (a b : ℝ≥0) : a ≤ a + b := by linarith

example (a b : ℝ≥0) : a ≤ a + b := by
  basify
  linarith

example (a b : ℝ≥0) (h : a + b = 0) : a = 0 := by linarith

example (a b : ℝ≥0) (h : a + b = 0) : a = 0 := by
  basify
  linarith

example (a b : ℝ≥0) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by nlinarith

example (a b : ℝ≥0) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  basify
  nlinarith

/-- Atoms that are not local hypotheses get their facts too. -/
example (f : ℕ → ℝ≥0) : f 0 ≤ f 0 + f 1 := by
  basify
  linarith

example (a : ℝ≥0) (h : a ≠ 0) : a * a⁻¹ = 1 := by field_simp

example (a : ℝ≥0) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  basify
  field_simp

example (a b : ℝ≥0) (h : b ≠ 0) : a / b * b = a := by
  basify
  field_simp

example (a b : ℝ≥0) : min a b ≤ max a b := by
  basify
  exact min_le_max

/-! #### Truncated subtraction

This is where the tactics differ. `NNReal.coe_sub` is conditional, so `push_cast` gets through it
only when the inequality is handed over, and `linarith`'s preprocessor leaves `↑(a - b)` as an
opaque nonnegative atom. `basify` uses the unconditional `NNReal.coe_sub_def` instead, so it
always makes progress, at the cost of landing on a `max` that the linear arithmetic tactics cannot
themselves see through.
-/

example (a b : ℝ≥0) (h : a ≤ b) : a - b = 0 := by
  fail_if_success linarith
  basify
  exact max_eq_right (sub_nonpos.2 h)

example (a b : ℝ≥0) (h : b ≤ a) : a - b + b = a := by
  fail_if_success linarith
  basify
  rw [max_eq_left (by linarith)]
  ring

/-- Handing `push_cast` the inequality is the sharper tool when you have it. -/
example (a b : ℝ≥0) (h : b ≤ a) : a - b + b = a := by
  rify [h]
  ring

/-! ### `ℕ∞`

These are the `enat_to_nat` tests. Two of them no longer need the trailing `lia`.
-/

example (a b : ℕ∞) (h : a = b) : a - b = b - a := by
  basify

example (a b : ℕ∞) (h : a ≤ b) : a - b < b + 1 := by
  basify
  lia

example (a b : ℕ∞) (h : a ≤ b) : a - 2 * b ≤ b + 1 := by
  basify
  lia

example (a b c : ℕ∞) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  basify
  lia

/-- The tactic works with inaccessible names. -/
example (a b : ℕ∞) (h : a = b) : a - b = b - a := by
  let a : ℤ := 42
  let b : ℤ := 32
  basify

/-! ### `ℕ+`

`ℕ+` is a subtype like `ℝ≥0`, so its eliminator has a single case: it exposes the underlying
natural together with `0 < n`. These are the `pnat_to_nat` tests.
-/

example (a b : ℕ+) (h : a < b) : 1 < b := by
  basify
  lia

/-- The tactic works with inaccessible names. -/
example (a b : ℕ+) (h : a = b) : b = a := by
  let a : ℤ := 42
  basify

/-- A fact that is already in the context is not recorded twice. -/
example (a b : ℕ+) (h : a < b) : 1 < b := by
  have := a.pos
  basify
  lia

/-! ### Several registered types at once -/

example (m : ℕ∞) (a : ℝ≥0∞) (hm : m ≠ ⊤) (ha : a ≠ ⊤) : m + m ≠ ⊤ ∧ a + a ≠ ⊤ := by
  basify
