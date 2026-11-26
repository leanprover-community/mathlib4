/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Manifold differentiability of the Jacobi theta functions

In this file we reformulate differentiability of the Jacobi theta functions `jacobiTheta`,
`jacobiTheta₀₁` and `jacobiTheta₁₀` in terms of manifold differentiability.

## TODO

Prove smoothness (in terms of `Smooth`).
-/

public section


open scoped UpperHalfPlane Manifold

theorem mdifferentiable_jacobiTheta : MDiff (jacobiTheta ∘ (↑) : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta τ.coe_im_pos).mdifferentiableAt.comp τ
    τ.mdifferentiable_coe

theorem mdifferentiable_jacobiTheta₀₁ : MDiff (jacobiTheta₀₁ ∘ (↑) : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta₀₁ τ.coe_im_pos).mdifferentiableAt.comp τ
    τ.mdifferentiable_coe

theorem mdifferentiable_jacobiTheta₁₀ : MDiff (jacobiTheta₁₀ ∘ (↑) : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta₁₀ τ.coe_im_pos).mdifferentiableAt.comp τ
    τ.mdifferentiable_coe
