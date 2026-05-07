/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib

/-!
# Dirichlet Eigenvalues

In this file we define Dirichlet eigenvalues.

## Main Definitions

* `MeasureTheory.mlconvolution f g μ x = (f ⋆ₘₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`
  is the multiplicative convolution of `f` and `g` w.r.t. the measure `μ`.
* `MeasureTheory.lconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`
  is the additive convolution of `f` and `g` w.r.t. the measure `μ`.
-/

@[expose] public section

open scoped Laplacian

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Laplacian (X → ℝ) (X → ℝ)]
  (S : Set X) (u : X → ℝ) (t : ℝ)

/-- A real-valued function `u` is a Dirichlet eigenfunction on a set `S` if `u` is nonzero on `S`,
satisfies `Δ u + t u = 0` on `S`, and vanishes on the boundary of `S`.

[Automatically have smoothness on nonzero connected component, so get union?] -/
structure DirichletEigenfunction : Prop where
  nonzero : ∃ x ∈ S, u x ≠ 0
  smooth : ContDiffOn ℝ 2 u S
  eigenfunction : ∀ x ∈ interior S, Δ u x + t * u x = 0
  vanishing : ∀ x ∈ frontier S, u x = 0

namespace DirichletEigenfunction

theorem smooth (h : DirichletEigenfunction S u t) : False := by
  sorry

end DirichletEigenfunction


/-- A Dirichlet eigenvalue of a set `S` is a value of `λ` for which there exists a nonzero
real-valued function `u` satisfying `Δ u + λ u = 0` on `S` and `u = 0` on `∂S`. -/
def dirichletEigenvalues : Set ℝ :=
  { t | ∃ u : X → ℝ, (∃ x ∈ S, u x ≠ 0) ∧ (∀ x ∈ S, Δ u + t • u = 0) ∧ ∀ x ∈ frontier S, u x = 0}

theorem dirichletEigenvalues_empty : dirichletEigenvalues (∅ : Set X) = ∅ := by
  by_contra! h
  obtain ⟨t, u, ⟨x, ⟨⟩, hux⟩, huS, hu0⟩ := h

theorem nonneg_of_mem_dirichletEigenvalues {t : ℝ} (ht : t ∈ dirichletEigenvalues S) : 0 ≤ t := by
  sorry
