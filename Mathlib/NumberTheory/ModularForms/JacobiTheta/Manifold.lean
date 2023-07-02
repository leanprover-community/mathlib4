/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module number_theory.modular_forms.jacobi_theta.manifold
! leanprover-community/mathlib commit 57f9349f2fe19d2de7207e99b0341808d977cdcf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Manifold differentiability of the Jacobi theta function

In this file we reformulate differentiability of the Jacobi theta function in terms of manifold
differentiability.

## TODO

Prove smoothness (in terms of `Smooth`).
-/


open scoped UpperHalfPlane Manifold

theorem mdifferentiable_jacobiTheta : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (jacobiTheta ∘ (↑) : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
#align mdifferentiable_jacobi_theta mdifferentiable_jacobiTheta
