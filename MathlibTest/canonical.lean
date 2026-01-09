import Mathlib.Data.Real.Basic

-- From https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Canonical/near/538098556

/--
info: Try this:
  [apply] exact
    Exists.intro 2
      (by simp only [Nat.zero_add, Nat.zero_mul, Nat.succ_mul, Nat.succ.injEq, Nat.succ_add] <;> exact Eq.refl Nat.zero)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∃ n : Nat, n * n = 4 := by
  canonical

-- From https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Canonical/near/538228811

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/--
info: Try this:
  [apply] exact fun ε a ↦
    Exists.intro (hu (hf ε a).choose (Exists.choose_spec (hf ε a)).1).choose fun n a_1 ↦
      (Exists.choose_spec (hf ε a)).2 (u n)
        (Exists.choose_spec (hu (hf ε a).choose (Exists.choose_spec (hf ε a)).1) n a_1)
---
warning: declaration uses 'sorry'
---
warning: unused variable `hf`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  canonical
