/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Absolutely Monotone Functions

A function `f : ℝ → ℝ` is absolutely monotone on a set `s` if it is smooth
on `s` and all its iterated derivatives within `s` are nonneg on `s`.

## Main definitions

* `AbsolutelyMonotoneOn` — smooth on `s` with nonneg iterated derivatives within `s`

## Main results

* Closure under `add`, `smul`, `mul`
* `absolutelyMonotoneOn_exp`, `absolutelyMonotoneOn_cosh`, `absolutelyMonotoneOn_pow`

## References

* Widder, D.V. (1941). *The Laplace Transform*.
-/

public section

open Set Filter
open scoped ENNReal NNReal Topology ContDiff

/-- A function `f : ℝ → ℝ` is absolutely monotone on a set `s` if it is
smooth on `s` and all iterated derivatives within `s` are nonneg. -/
structure AbsolutelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ f s
  nonneg : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x

namespace AbsolutelyMonotoneOn

/-- Constructor from global `ContDiff` and global `iteratedDeriv`.
Works for any `UniqueDiffOn` set (includes open sets, `Ici a`,
convex sets with nonempty interior, etc.). -/
theorem of_contDiff {f : ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s)
    (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDeriv n f x) :
    AbsolutelyMonotoneOn f s where
  contDiffOn := hf.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      (hf.contDiffAt.of_le (by exact_mod_cast le_top)) hx]
    exact h n x hx

/-- Nonneg Taylor coefficients at any point in `s`. -/
theorem nonneg_taylor_coeffs {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AbsolutelyMonotoneOn f s) {x : ℝ} (hx : x ∈ s)
    (n : ℕ) :
    0 ≤ iteratedDerivWithin n f s x / (n.factorial : ℝ) :=
  div_nonneg (hf.nonneg n x hx) (Nat.cast_nonneg _)

/-! ### Basic closure properties -/

theorem add {f g : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f + g) s where
  contDiffOn := hf.contDiffOn.add hg.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_add hx hs
      ((hf.contDiffOn x hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffOn x hx).of_le (by exact_mod_cast le_top))]
    exact add_nonneg (hf.nonneg n x hx) (hg.nonneg n x hx)

theorem smul {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hf : AbsolutelyMonotoneOn f s) (hc : 0 ≤ c) :
    AbsolutelyMonotoneOn (c • f) s where
  contDiffOn := hf.contDiffOn.const_smul c
  nonneg n x hx := by
    rw [iteratedDerivWithin_const_smul_field c f]
    exact smul_nonneg hc (hf.nonneg n x hx)

theorem mul {f g : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f * g) s where
  contDiffOn := hf.contDiffOn.mul hg.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_mul hx hs
      ((hf.contDiffOn x hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffOn x hx).of_le (by exact_mod_cast le_top))]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (hf.nonneg i x hx)
    · exact hg.nonneg (n - i) x hx

end AbsolutelyMonotoneOn

/-! ### Examples -/

theorem absolutelyMonotoneOn_exp (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    AbsolutelyMonotoneOn Real.exp s :=
  .of_contDiff hs Real.contDiff_exp fun n x _hx => by
    have : iteratedDeriv n Real.exp x = Real.exp x := by
      have h := iteratedDeriv_exp_const_mul n (1 : ℝ)
      simp only [one_pow, one_mul] at h
      exact congr_fun h x
    rw [this]; exact (Real.exp_pos x).le

theorem absolutelyMonotoneOn_cosh :
    AbsolutelyMonotoneOn Real.cosh (Ici 0) :=
  .of_contDiff (uniqueDiffOn_Ici 0) Real.contDiff_cosh
    fun n x hx => by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk, show k + k = 2 * k from by ring,
          Real.iteratedDeriv_even_cosh]
        exact (Real.cosh_pos x).le
      · rw [hk, Real.iteratedDeriv_odd_cosh]
        exact Real.sinh_nonneg_iff.mpr (mem_Ici.mp hx)

theorem absolutelyMonotoneOn_const {c : ℝ} (hc : 0 ≤ c)
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    AbsolutelyMonotoneOn (fun _ => c) s :=
  .of_contDiff hs contDiff_const fun n x _hx => by
    simp only [iteratedDeriv_const]
    split
    · exact hc
    · exact le_refl 0

theorem absolutelyMonotoneOn_pow (n : ℕ) :
    AbsolutelyMonotoneOn (fun x => x ^ n) (Ici 0) :=
  .of_contDiff (uniqueDiffOn_Ici 0) (contDiff_id.pow n)
    fun k x hx => by
      simp only [iteratedDeriv_pow]
      exact mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mem_Ici.mp hx) _)
