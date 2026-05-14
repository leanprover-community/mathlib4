/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Higher differentiability in one dimension

The general theory of higher derivatives in Mathlib is developed using the Fréchet derivative
`fderiv`; but for maps defined on the field, the one-dimensional derivative `deriv` is often easier
to use. In this file, we reformulate some higher smoothness results in terms of `deriv`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open scoped ContDiff

open Set

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {m n : ℕ∞ω} {f : 𝕜 → F} {s : Set 𝕜}

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `derivWithin`) is `C^n`. -/
theorem contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (derivWithin f s) s := by
  have : derivWithin f s =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f s := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]

theorem contDiffOn_one_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 1 f s ↔ DifferentiableOn 𝕜 f s ∧ ContinuousOn (derivWithin f s) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

theorem contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (derivWithin f s) s := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem contDiffOn_succ_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (deriv f) s := by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))

theorem contDiffOn_infty_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (deriv f) s := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp

protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (derivWithin f s) s :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2

theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f) s :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f s) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (deriv f) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

@[fun_prop]
protected lemma ContDiffWithinAt.derivWithin {x : 𝕜}
    (H : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (derivWithin f s) s x := by
  exact ContDiffWithinAt.comp _ (by fun_prop) (g := fun f ↦ f 1) (t := .univ)
    (H.fderivWithin_right hs hmn hx) (fun _ _ ↦ trivial)

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
theorem contDiff_succ_iff_deriv :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω → AnalyticOn 𝕜 f univ) ∧
      ContDiff 𝕜 n (deriv f) := by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]

theorem contDiff_one_iff_deriv :
    ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (deriv f) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
  simp

theorem contDiff_infty_iff_deriv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (deriv f) := by
  rw [show (∞ : ℕ∞ω) = ∞ + 1 from rfl, contDiff_succ_iff_deriv]
  simp

theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Continuous (deriv f) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

@[fun_prop]
theorem ContDiff.continuous_deriv_one (h : ContDiff 𝕜 1 f) : Continuous (deriv f) :=
  ContDiff.continuous_deriv h (le_refl 1)

@[fun_prop]
theorem ContDiff.differentiable_deriv_two (h : ContDiff 𝕜 2 f) : Differentiable 𝕜 (deriv f) := by
  unfold deriv; fun_prop

@[fun_prop]
protected lemma ContDiffAt.derivWithin {x : 𝕜} (H : ContDiffAt 𝕜 n f x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (deriv f) x := by
  simpa using ContDiffWithinAt.derivWithin (s := .univ) H.contDiffWithinAt (by simp) hmn

@[fun_prop]
theorem ContDiff.deriv' (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n (deriv f) := by
  unfold deriv; fun_prop

@[fun_prop]
theorem ContDiff.iterate_deriv :
    ∀ (n : ℕ) {f : 𝕜 → F}, ContDiff 𝕜 ∞ f → ContDiff 𝕜 ∞ (deriv^[n] f)
  | 0, _, hf => hf
  | n + 1, _, hf => ContDiff.iterate_deriv n (contDiff_infty_iff_deriv.mp hf).2

@[fun_prop]
theorem ContDiff.iterate_deriv' (n : ℕ) :
    ∀ (k : ℕ) {f : 𝕜 → F}, ContDiff 𝕜 (n + k : ℕ) f → ContDiff 𝕜 n (deriv^[k] f)
  | 0, _, hf => hf
  | k + 1, _, hf => ContDiff.iterate_deriv' _ k (contDiff_succ_iff_deriv.mp hf).2.2

end
