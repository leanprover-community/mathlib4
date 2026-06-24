/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Absolutely monotone functions

A function `f : ℝ → ℝ` is *absolutely monotone* on a set `s` if its iterated derivatives are all
nonnegative on `s`.

## Main definitions

* `AbsolutelyMonotoneOn` — there exists a Taylor series for `f` on `s` with nonnegative terms at
  each point of `s`.

## Main results

* `AbsolutelyMonotoneOn.contDiffOn` — the function is `C^∞` on `s`.
* `AbsolutelyMonotoneOn.of_contDiff` — a globally `C^∞` function with nonnegative iterated
  derivatives on `s` is absolutely monotone on `s`.
* `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` — under `UniqueDiffOn`, the definition
  is equivalent to `f` being `C^∞` on `s` with every iterated derivative within `s` nonnegative.
* `AbsolutelyMonotoneOn.add` — closure under addition.
* `AbsolutelyMonotoneOn.smul` — closure under nonnegative scalar multiplication.

## Implementation

The precise definition is phrased via the existence of a Taylor series with nonnegative terms
(`HasFTaylorSeriesUpToOn`) rather than via `iteratedDerivWithin`. This avoids forcing a
`UniqueDiffOn s` hypothesis on every result: without `UniqueDiffOn`, "the" iterated derivative
within `s` is not canonical, but the existence of a Taylor series is intrinsic to `f` and `s`.
When `s` does satisfy `UniqueDiffOn`, the condition reduces to `f` being `C^∞` on `s` with every
iterated derivative within `s` nonnegative.

## References

* [D. V. Widder, *The Laplace Transform*][widder1941]
-/

public section

open Set Filter
open scoped ContDiff

/-- A function `f : ℝ → ℝ` is **absolutely monotone on a set `s`** if, heuristically, all
iterated derivatives of `f` on `s` are nonnegative. For technical reasons related to unique
differentiability, the precise definition is phrased as the existence of a Taylor series for
`f` on `s` whose `n`th term, evaluated at the all-ones tuple, is nonnegative for every `n` and
every `x ∈ s`. See `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` for the equivalence
under `UniqueDiffOn`. -/
def AbsolutelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ p : ℝ → FormalMultilinearSeries ℝ ℝ ℝ,
    HasFTaylorSeriesUpToOn ∞ f p s ∧
    ∀ (n : ℕ) ⦃x : ℝ⦄, x ∈ s → 0 ≤ p x n fun _ ↦ (1 : ℝ)

namespace AbsolutelyMonotoneOn

variable {f g : ℝ → ℝ} {s : Set ℝ}

/-- An absolutely monotone function on `s` is `C^∞` on `s`. -/
theorem contDiffOn (hf : AbsolutelyMonotoneOn f s) : ContDiffOn ℝ ∞ f s := by
  obtain ⟨_, hp, _⟩ := hf
  exact hp.contDiffOn

/-- A globally `C^∞` function whose iterated derivatives are nonnegative on `s` is absolutely
monotone on `s`. The set `s` need *not* satisfy `UniqueDiffOn`. -/
theorem of_contDiff (hf : ContDiff ℝ ∞ f) (h : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDeriv n f x) :
    AbsolutelyMonotoneOn f s := by
  refine ⟨ftaylorSeries ℝ f, (hf.ftaylorSeries).hasFTaylorSeriesUpToOn s, fun n x hx => ?_⟩
  exact iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ) (f := f) ▸ h n x hx

/-- Under `UniqueDiffOn`, a Taylor witness for an absolutely monotone function agrees with
`iteratedDerivWithin`, so the latter is nonnegative on `s`. -/
theorem iteratedDerivWithin_nonneg (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn ℝ s)
    (n : ℕ) {x : ℝ} (hx : x ∈ s) : 0 ≤ iteratedDerivWithin n f s x := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  have heq : p x n = iteratedFDerivWithin ℝ n f s x :=
    hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) hs hx
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, ← heq]
  exact hp_nn n hx

/-- Under `UniqueDiffOn`, a function is absolutely monotone on `s` iff it is `C^∞` on `s` with
every iterated derivative within `s` nonnegative. -/
theorem iff_iteratedDerivWithin_nonneg (hs : UniqueDiffOn ℝ s) :
    AbsolutelyMonotoneOn f s ↔
      ContDiffOn ℝ ∞ f s ∧ ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x := by
  refine ⟨fun hf => ⟨hf.contDiffOn, fun n x hx => hf.iteratedDerivWithin_nonneg hs n hx⟩, ?_⟩
  rintro ⟨hcont, hnn⟩
  refine ⟨ftaylorSeriesWithin ℝ f s, hcont.ftaylorSeriesWithin hs, fun n x hx => ?_⟩
  exact iteratedDerivWithin_eq_iteratedFDerivWithin (𝕜 := ℝ) (f := f) (s := s) ▸ hnn n x hx

/-! ### Closure properties -/

/-- The sum of two absolutely monotone functions is absolutely monotone. -/
theorem add (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f + g) s := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  obtain ⟨q, hq, hq_nn⟩ := hg
  refine ⟨p + q, hp.add hq, fun n x hx => ?_⟩
  simp only [Pi.add_apply, FormalMultilinearSeries.add_apply, add_apply]
  exact add_nonneg (hp_nn n hx) (hq_nn n hx)

/-- A nonnegative scalar multiple of an absolutely monotone function is absolutely monotone. -/
theorem smul {c : ℝ} (hf : AbsolutelyMonotoneOn f s) (hc : 0 ≤ c) :
    AbsolutelyMonotoneOn (c • f) s := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  -- Witness: post-composition by the CLM `y ↦ c * y`.
  set T : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ with hT
  have hcomp : (T ∘ f) = c • f := by ext x; simp [hT, smul_eq_mul]
  refine ⟨_, hcomp ▸ hp.continuousLinearMap_comp T, fun n x hx => ?_⟩
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, hT,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  exact mul_nonneg hc (hp_nn n hx)

end AbsolutelyMonotoneOn
