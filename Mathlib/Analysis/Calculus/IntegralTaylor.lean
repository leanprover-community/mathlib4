/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib

/-!
# Taylor's formula with an integral remainder

-/

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable {f : E → F} {x y : E} (t : 𝕜) {n : ℕ}

theorem bar {m : Fin (n + 1) → E} (hf : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) x) :
    iteratedFDeriv 𝕜 (n + 1) f x m =
    fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n f y (Fin.tail m)) x (m 0) := by
  convert iteratedFDeriv_succ_apply_left m
  simp [fderiv_continuousMultilinear_apply_const hf]

theorem foo (hf : ContDiffAt 𝕜 (n + 1) f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ iteratedFDeriv 𝕜 n f (x + s • y) (fun _ ↦ y)) t =
    iteratedFDeriv 𝕜 (n + 1) f (x + t • y) (fun _ ↦ y) := by
  have hg : Differentiable 𝕜 (fun (s : 𝕜) ↦ (x + s • y)) := by fun_prop
  have hf' : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) (x + t • y) := by
    apply hf.differentiableAt_iteratedFDeriv
    norm_cast
    grind
  convert fderiv_comp_deriv t (hf'.continuousMultilinear_apply_const _) hg.differentiableAt
  have hdiff : deriv (fun s ↦ x + s • y) t = y := by
    simpa using (deriv_smul_const (x := t) differentiableAt_id y)
  rw [hdiff]
  apply bar hf'

end NontriviallyNormedField

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

variable {f : E → F} {x y : E} {n : ℕ}

theorem baz (hf : ∀ (t : ℝ) (_ht₁ : 0 ≤ t) (_ht₂ : t ≤ 1), ContDiffAt ℝ (n + 1) f (x + t • y)) :
    f (x + y) = ∫ t in 0..1, iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
  sorry
