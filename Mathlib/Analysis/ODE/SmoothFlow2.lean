/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth dependence on initial condition

We prove that the solution of a $C^n$ vector field has $C^n$ dependence on the initial condition.

## Main definitions and results



## Implementation notes



## Tags

differential equation, dynamical system, initial value problem

-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-
`f : E → E`
  Differential equation
`tmin tmax : ℝ`
  End points of interval `Icc tmin tmax` in which solution exists
`t₀ : Icc tmin tmax`
  Initial time of solution
`x : E`
  Initial value of solution
`f' : E → E →L[ℝ] E`
  Derivative of `f`
`F := C(Icc tmin tmax, E)`
  Shorthand for the function space in which solutions live

Construct `T : E × F → F` as an implicit equation such that `T (x, α) = 0` gives a solution `α` with
initial condition `α t₀ = x`. Let `(x₀, α₀)` be such a pair, which exists due to the Picard-Lindelöf
theorem. Our goal is to apply the implicit function theorem to extract an implicit function
`α : E → F` such that `T (x, α x) = 0` for `x` in a neighbourhood of `x₀`. Furthermore, if `f` is
`C^n` with `n > 0`, then `α : E → F` is also `C^n`.

The formula for `T` is
`T (x, α) := fun t ↦ x - α t + ∫ τ in t₀..t, f (α τ)`.
Some casting of real numbers to `Icc tmin tmax` is necessary to make this type check.

We need to show that `T` is `C^n` if `f` is `C^n`. It is easier to do this for the integral term
first. In fact, we will do this more generally by defining
`I g α := fun t ↦ ∫ τ in t₀..t, g (α τ)`,
where `g : E → X` for some type `X`. This equals the integral term of `T` when `g = f`. `I g` has
the derivative
`I' g := fun t ↦ ∫ τ in t₀..t, g' (α τ)`,
where `g' : E → E →L[ℝ] X` is the derivative of `g`. By induction,
`I^(n) g = I g^(n)`.
We can also show that `I g` is continuous if `g` is continuous, so `I g` is `C^n` if `g` is `C^n`.
Then, `T^(n) (x, α)` can be shown to be `C^n` if `f` is `C^n` by relating it to `I^(n) f α`.

In particular, we have the form of the first derivative `T' (x₀, α₀) : E × F →L[ℝ] F`. We need to
show that `T' (x₀, α₀) (x, ·) : F →L[ℝ] F` is invertible for all `x : E`. (...)

Then, `T` satisfies `IsContDiffImplicitAt` (probably will be superceded and removed by #26985).

We have now shown that `α : E → F` is locally `C^n` around `x₀` if `f` is `C^n`. We then need to
show that the uncurried `α_unc : E × ℝ → E` is locally `C^n` around `(x₀, t₀)`. (...)

Finally, we will show that `α_unc` is `C^n` over its domain of definition.

-/
