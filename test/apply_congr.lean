import Mathlib.Tactic.ApplyCongr
import Mathlib.Algebra.BigOperators.Group.Finset

example (f g : ℤ → ℤ) (S : Finset ℤ) (h : ∀ m ∈ S, f m = g m) :
    Finset.sum S f = Finset.sum S g := by
  conv_lhs =>
    -- If we just call `congr` here, in the second goal we're helpless,
    -- because we are only given the opportunity to rewrite `f`.
    -- However `apply_congr` uses the appropriate `@[congr]` lemma,
    -- so we get to rewrite `f x`, in the presence of the crucial `H : x ∈ S` hypothesis.
    apply_congr
    · skip
    · simp [*]
