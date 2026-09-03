module
import Mathlib.Tactic.Basify
import Mathlib.Tactic

open scoped NNReal ENNReal

set_option linter.unnecessarySeqFocus false

/-! ## Operations of `ℝ≥0∞` and `ℝ≥0` -/

example (a : ℝ≥0∞) (h : a ≠ ⊤) : (0 : ℝ≥0∞) ≤ a := by
  basify

example (a : ℝ≥0∞) : a ≤ a + 1 := by
  basify
  linarith

example (a : ℝ≥0∞) (h : a ≠ ⊤) : a ≤ a + 2 := by
  basify
  linarith

example (a b : ℝ≥0∞) (h : a + 1.5 = b + 1.5) : a = b := by
  basify
  linarith

example (n : ℕ) : (n : ℝ≥0∞) ≠ ⊤ := by
  basify

example (a b c : ℝ≥0∞) (hc : c ≠ ⊤) (h : a + c = b + c) : a = b := by
  basify
  linarith

example (a b c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) (h : a * c = b * c) : a = b := by
  basify
  grind

example (a b : ℝ≥0∞) (hb : b ≠ ⊤) (h : a ≤ b) : a - b = 0 := by
  basify
  grind

example (a : ℝ≥0∞) (n : ℕ) (h : a ≠ ⊤) : a ^ n ≠ ⊤ := by
  basify

example (a : ℝ≥0∞) (h : a ≠ 0) (h' : a ≠ ⊤) : a * a⁻¹ = 1 := by
  basify
  field_simp

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hb0 : b ≠ 0) : a / b * b = a := by
  basify
  field_simp

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) : 2 * min a b ≤ a + b := by
  basify
  grind

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a + b ≤ 2 * max a b := by
  basify
  grind

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) : (a + b).toReal = a.toReal + b.toReal := by
  basify

/-! ## Operations of `ℕ∞` -/

example (a : ℕ∞) : a + 0 = a := by
  basify
  lia

example (a : ℕ∞) : a ≤ a + 1 := by
  basify
  lia

example (a b : ℕ∞) (h : a ≤ b) : a ≤ b + 2 := by
  basify
  lia

example (a b : ℕ∞) (h : a = b) : a - b = b - a := by
  basify

example (a : ℕ∞) (h : a ≠ ⊤) : 2 * a = a + a := by
  basify
  lia

/-! ## Operations of `ℕ+` -/

example (a : ℕ+) : 1 ≤ a := by
  basify
  lia

example (a : ℕ+) (h : a = 2) : 2 ≤ a := by
  basify
  lia

example (a b : ℕ+) : a < a + b := by
  basify
  lia

example (a b : ℕ+) : a ≤ a * b := by
  basify
  nlinarith

example (a b : ℕ+) (h : b < a) : a - b < a := by
  basify
  lia

/-! ## Atoms -/

/-- An atom that is not a variable is generalized before it can be split. -/
example (f : ℕ → ℝ≥0∞) (h1 : f 1 ≠ ⊤) (h : f 0 + f 1 = f 2 + f 1) : f 0 = f 2 := by
  basify
  linarith

/-- A reducible alias, used below to exercise deduplication of atoms up to unfolding. -/
abbrev two' : ℕ := 2

/-- Atoms are interned with `AtomM` at `instances` transparency -/
example (f : ℕ → ℝ≥0∞) : f two' ≤ f 2 + f two' := by
  basify
  linarith

def foo : ℝ≥0∞ := 1
def bar : ℝ≥0∞ := foo

/-- `foo` and `bar` are definitionally equal, but we collect atoms up to `instanses` transparency -/
example : foo ≤ bar := by
  fail_if_success (basify; linarith)
  unfold bar
  basify
  linarith

/-- Atom under a binder -/
example (a b c : ℝ≥0∞) (hc : c ≠ ⊤) (h : a + c = b + c) : ∀ _ : ℕ, a = b := by
  basify
  linarith

/-- An atom under a `let` -/
example (a b : ℝ≥0∞) (h : (let c : ℝ≥0∞ := a + b; c) = 0) : a = 0 := by
  basify <;> linarith

/-- A subterm with bvar is not an atom -/
example (f : ℕ → ℝ≥0∞) (h : ∀ i, f i ≤ 1) : f 0 ≤ 1 := by
  have := h 0
  basify

/-! ### Complex examples -/

/-- The `ℝ≥0∞` arithmetic at the heart of `Wiedijk100Theorems.first_vote_neg`. The original proof
spelled out `ENNReal.eq_sub_of_add_eq`, `ENNReal.eq_div_iff`, `ENNReal.mul_sub`,
`ENNReal.mul_div_cancel` and `ENNReal.add_sub_cancel_left` by hand. -/
example (A : ℝ≥0∞) (p q : ℕ) (h : 0 < p + q) (hA : A + p / (p + q) = 1) : A = q / (p + q) := by
  have h' : (p + q : ℝ≥0∞) ≠ 0 := by
    basify
    rify at h
    grind
  basify
  grind
