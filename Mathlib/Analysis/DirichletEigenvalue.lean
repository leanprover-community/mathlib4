/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Dirichlet Eigenvalues

In this file we define Dirichlet eigenvalues.

## Main Definitions

* `DirichletEigenfunction`: A predicate stating that a function `u` is a Dirichlet eigenfunction.
* `dirichletEigenvalues`: The set of Dirichlet eigenvalues of a set `S`.

## TODO
* Prove that Dirichlet eigenvalues are positive (requires a more general divergence theorem).
-/

@[expose] public section

open scoped Laplacian

variable {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  (S : Set X) (u : X → ℝ) (t : ℝ)

/-- A real-valued function `u` is a Dirichlet eigenfunction on a set `S` if:
1) `u` is not identically zero on `S`,
2) `u` is continuous on the closure of `S`,
3) `u` is twice continuously differentiable on the interior of `S`,
4) `u` satisfies `Δ u + t u = 0` on the interior of `S`,
5) `u` vanishes on the boundary of `S`. -/
structure DirichletEigenfunction : Prop where
  nonzero : ∃ x ∈ S, u x ≠ 0
  continuous : ContinuousOn u (closure S)
  smooth : ContDiffOn ℝ 2 u (interior S)
  eigenfunction : ∀ x ∈ interior S, Δ u x + t * u x = 0
  vanishing : ∀ x ∈ frontier S, u x = 0

/-- A Dirichlet eigenvalue of a set `S` is a value of `t` for which there exists a nonzero
real-valued function `u` satisfying `Δ u + λ u = 0` on `S` and `u = 0` on `∂S`. -/
def dirichletEigenvalues : Set ℝ :=
  { t | ∃ u : X → ℝ, DirichletEigenfunction S u t}

theorem dirichletEigenvalues_empty : dirichletEigenvalues (∅ : Set X) = ∅ := by
  by_contra! h
  obtain ⟨t, u, hu⟩ := h
  obtain ⟨x, ⟨⟩, hux⟩ := hu.nonzero
