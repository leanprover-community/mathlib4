/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Absolutely Monotone Functions

A function `f : ℝ → ℝ` is absolutely monotone on a set `s` if it is smooth on `s` and all its
iterated derivatives within `s` are nonnegative on `s`.

## Main definitions

* `AbsolutelyMonotoneOn` — smooth on `s` with nonnegative iterated derivatives within `s`

## Main results

* Closure under `add`, `smul`, `mul`

## References

* [D. V. Widder, *The Laplace Transform*][widder1941]
-/

public section

open Set Filter
open scoped ENNReal NNReal Topology ContDiff

/-- A function `f : ℝ → ℝ` is absolutely monotone on a set `s` if it is smooth on `s` and all
iterated derivatives within `s` are nonnegative. -/
structure AbsolutelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ f s
  nonneg : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x

namespace AbsolutelyMonotoneOn

/-- A globally smooth function all of whose iterated derivatives are nonnegative on a set `s`
satisfying `UniqueDiffOn` is absolutely monotone on `s`. Such sets `s` include open sets,
`Set.Ici`, and convex sets with nonempty interior. -/
theorem of_contDiff {f : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDeriv n f x) : AbsolutelyMonotoneOn f s where
  contDiffOn := hf.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt.of_le (by exact_mod_cast le_top))
      hx]
    exact h n x hx

/-! ### Basic closure properties -/

theorem add {f g : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hf : AbsolutelyMonotoneOn f s)
    (hg : AbsolutelyMonotoneOn g s) : AbsolutelyMonotoneOn (f + g) s where
  contDiffOn := hf.contDiffOn.add hg.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_add hx hs ((hf.contDiffOn x hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffOn x hx).of_le (by exact_mod_cast le_top))]
    exact add_nonneg (hf.nonneg n x hx) (hg.nonneg n x hx)

theorem smul {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ} (hf : AbsolutelyMonotoneOn f s) (hc : 0 ≤ c) :
    AbsolutelyMonotoneOn (c • f) s where
  contDiffOn := hf.contDiffOn.const_smul c
  nonneg n x hx := by
    rw [iteratedDerivWithin_const_smul_field c f]
    exact smul_nonneg hc (hf.nonneg n x hx)

theorem mul {f g : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hf : AbsolutelyMonotoneOn f s)
    (hg : AbsolutelyMonotoneOn g s) : AbsolutelyMonotoneOn (f * g) s where
  contDiffOn := hf.contDiffOn.mul hg.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_mul hx hs ((hf.contDiffOn x hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffOn x hx).of_le (by exact_mod_cast le_top))]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf.nonneg i x hx)) (hg.nonneg (n - i) x hx)

end AbsolutelyMonotoneOn
