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
`I g := fun α t ↦ ∫ τ in t₀..t, g (α τ) : F → C(Icc tmin tmax, X)`,
where `g : E → X` for some type `X`. This equals the integral term of `T` when `g = f`. `I g` has
the derivative at `α`
`I' g α := fun dα t ↦ ∫ τ in t₀..t, g' (α τ) (dα τ) : F →L[ℝ] C(Icc tmin tmax, X)`,
where `g' : E → E →L[ℝ] X` is the derivative of `g`. By induction,
`I^(n) g = I g^(n)`.

Let's get the types right.
`g^(0) = f  : E → E`
`g^(1) = g' : E → E →L[ℝ] E`
`g^(2)      : E → E →L[ℝ] E →L[ℝ] E`

`I^(0) g = I g  : F → C(Icc tmin tmax, X)`
`I^(1) g = I' g : F → F →L[ℝ] C(Icc tmin tmax, X)`
`I^(2) g        : F → F →L[ℝ] F →L[ℝ] C(Icc tmin tmax, X)`

`I^(0) f = I f  : F → F`
`I^(1) f = I' f : F → F →L[ℝ] F`
`I^(2) f        : F → F →L[ℝ] F →L[ℝ] F`

`t ↦ I^(0) g^(1) α t (dα t) : C(Icc tmin tmax, E)` and
`I^(1) g^(0) α dα : C(Icc tmin tmax, E)` are equal. This requires handling multilinear application.

We can also show that `I g` is continuous if `g` is continuous, so `I g` is `C^n` if `g` is `C^n`.
Then, `T^(n) (x, α)` can be shown to be `C^n` if `f` is `C^n` by relating it to `I^(n) f α`.

In particular, we have the form of the first derivative `T' (x₀, α₀) : E × F →L[ℝ] F`. We need to
show that `T' (x₀, α₀) (x, ·) : F →L[ℝ] F` is invertible for all `x : E`. (...)

Then, `T` satisfies `IsContDiffImplicitAt` (probably will be superceded and removed by #26985).

We have now shown that `α : E → F` is locally `C^n` around `x₀` if `f` is `C^n`. We then need to
show that the uncurried `α_unc : E × ℝ → E` is locally `C^n` around `(x₀, t₀)`. (...)

Finally, we will show that `α_unc` is `C^n` over its domain of definition.

Translate this whole time-independent treatment to the time-dependent case.
-/

namespace SmoothFlow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-
`IsContDiffImplicitAt` requires complete normed spaces, so we can't use `α : ℝ → E` with junk
values. We'll use `C(Icc tmin tmax, E)` instead, but we need to cast such functions as elements of
`ℝ → E` in order to use `integral`.

It's not ideal to carry around `t₀` for `compProj`. Unfortunately, `NonemptyInterval` doesn't have a
topology defined on it yet.
-/

noncomputable def compProj {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) : ℝ → E :=
  fun t ↦ α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t)

/-
This is `I^(0) g^(n)`, where `g^(n)` could be a general multilinear map in `E`. Since we later want
`I^(0) g^(n)` to be `I^(n) g^(0)`, which is a multilinear map in `F`, and `F` is a function space
`Icc tmin tmax → E`, we need to apply `g^(n)` to a vector of `dα τ : E`.

`f` is `C^n` in `E`
`g^(0)` is `C^n` in `E`
`g^(n)` is continuous in `E`
`I^(0) g^(n)` is continuous in `F`
--- Induction
Use
`I^(k) g^(l+1) = I^(k+1) g^(l)` for all `k`, `l`
Show
`I(k) g^(l+m) = I^(k+m) g^(l)` for all `k`, `l`, `m`

Base case trivial
Inductive case:
For `m`, assume
`I(k) g^(l+m) = I^(k+m) g^(l)` for all `k` `l`
Then
`I(k) g^(l+m+1) = I^(k+1) g^(l+m) = I^(k+m+1) g^(l)` by taking `k = k + 1`

Specialise `k = 0`, `l = 0`, `m = n`:
`I^(0) g^(n) = I^(n) g^(0)`
---
`I^(n) g^(0)` is continuous in `F`
`I^(n) f` is continuous in `F`
`I^(0) f` is `C^n`

Differentiation under the integral sign requries
`intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip` (or friends):
`I^(1) g = I^(0) g^(1)`
`I^(k+1) g^(l) = I^(k) g^(l+1)` follows
-/

noncomputable def integralN {n : ℕ} (g : E → E [×n]→L[ℝ] E)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : (i : Fin n) → C(Icc tmin tmax, E)) : Icc tmin tmax → E :=
  fun t ↦ ∫ τ in t₀..t, g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)

/-
We need the target space to be continuous curves (`F`) so that we can later take derivatives with
respect to `α : F`, which requires a finite metric on the target space.
-/

-- need `g` continuous on `u` and `α` maps to `u`
def integralNCM {n : ℕ} (g : E → E [×n]→L[ℝ] E)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : (i : Fin n) → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) :=
  sorry

noncomputable def integral (f : E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) : Icc tmin tmax → E :=
  fun t ↦ ∫ τ in t₀..t, f (compProj t₀ α τ)

-- need `g` continuous on `u` and `α` maps to `u`
def integralCM (f : E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) :=
  sorry

lemma integralN_zero (f : E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) :
    integralN (iteratedFDeriv ℝ 0 f) t₀ α Fin.elim0 = integral f t₀ α := by
  rfl

-- need `g` continuous on `u` and `α` maps to `u`
lemma integralNCM_zero (f : E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) :
    integralNCM (iteratedFDeriv ℝ 0 f) t₀ α Fin.elim0 = integralCM f t₀ α := by
  sorry

/-
This is `I^(0) g^(n)` as a multilinear map in `F`, in order to later match up with the iterated
derivative `I^(n) g^(0)`.

Think about domain of validity

`g^(0) := f` is `C^n` on `u` (open)
`g^(k)` is `C^(n-k)` on `u` for all `k ≤ n`
This means that `g^(k)` has junk value outside `u`
Since `g^(k) (α τ)` is multilinear in `E`, its composition with a vector of `dα` is also continuous
multilinear
But `I^(0) g^(k)` is only continuous on `{α : F | MapsTo α univ u}`
-/

-- need `g` continuous on `u` and `α` maps to `u`
noncomputable def integralNCMLM {n : ℕ} (g : E → E [×n]→L[ℝ] E)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) [×n]→L[ℝ] C(Icc tmin tmax, E) where
  toFun := integralNCM g t₀ α
  map_update_add' := sorry
  map_update_smul' := sorry
  cont := sorry

lemma continuousOn_integralN {n : ℕ} {g : E → E [×n]→L[ℝ] E}
    {u : Set E} (hg : ContinuousOn g u) (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    ContinuousOn (integralNCMLM g t₀) {α : C(Icc tmin tmax, E) | MapsTo α univ u} := by
  sorry


/-
`I^(1) g = I^(0) g^(1)`
-/

-- variable
-- {n : ℕ} (g : E → E [×n]→L[ℝ] E)
--     {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))

-- #check fun x ↦ fderiv ℝ g x
-- #check ContinuousLinearMap.uncurryLeft (𝕜 := ℝ)
--   (n := n) (Ei := fun _ : Fin (Nat.succ n) => E) (G := E)
-- #check fun x ↦ ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (n + 1) => E) (fderiv ℝ g x)
-- #check integralNCMLM
--   (fun x ↦ ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (n + 1) => E) (fderiv ℝ g x)) t₀ α
-- #check ContinuousMultilinearMap.curryLeft (integralNCMLM
--   (fun x ↦ ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (n + 1) => E) (fderiv ℝ g x)) t₀ α)
-- #check fderiv ℝ (integralNCMLM g t₀) α

lemma hasFDerivAt_integralNCM {n : ℕ} (g : E → E [×n]→L[ℝ] E)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    HasFDerivAt (integralNCMLM g t₀)
      (ContinuousMultilinearMap.curryLeft
        (integralNCMLM (fun x ↦ ContinuousLinearMap.uncurryLeft
          (Ei := fun _ : Fin (n + 1) => E) (fderiv ℝ g x)) t₀ α)) α := by sorry

/-
`I^(k) g^(l+1) = I^(k+1) g^(l)` for all `k`, `l`, where `g : E → E [×n]→L[ℝ] E`

By induction, we will show `I^(0) g^(n) = I^(n) g^(0)`
Then `I^(0) f^(n) = I^(n) f^(0)`

There's a type check problem, which can be solved by `ContinuousMultilinearMap.curryFinFinset`.
I don't know why this lemma doesn't just use `Fin (k + l)`, so maybe we can write our own lemma
using `finSumFinEquiv` instead of `finSumEquivOfFinset`, which is only used once in Mathlib.

`iteratedFDeriv` and `iteratedDeriv` don't yet have `k + l` composition lemmas, only `succ` lemmas.
-/

section

universe u v v' wE wE₁ wE' wEi wG wG'

variable
  {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ} {E : ι → Type wE}
  {Ei : Fin n.succ → Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

def curryFinSum {k l n : ℕ} (h : k + l = n) :
    (G [×n]→L[𝕜] G') ≃ₗᵢ[𝕜] G [×k]→L[𝕜] G [×l]→L[𝕜] G' := sorry

end

/-
Should follow from `hasFDerivAt_integralNCM` by substituting `g := g^(l)` and taking `k` derivatives
on the whole expression.
-/

-- variable {n k l : ℕ} {g : E → E [×n]→L[ℝ] E}
--     {u : Set E} (hg : ContinuousOn g u) (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
--     (α : C(Icc tmin tmax, E)) (h : k + l = n)
--     (ggg : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) E)
-- #check (curryFinSum (n := l + n) (k := l) (l := n) rfl).symm
-- #check fun x ↦ (curryFinSum (𝕜 := ℝ) (G := E) (G' := E) rfl).symm (iteratedFDeriv ℝ l g x)

-- need `g` continuous on `u` and `α` maps to `u`
lemma integralNCMLM_succ {n k l : ℕ} {g : E → E [×n]→L[ℝ] E}
    {u : Set E} (hg : ContinuousOn g u) (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) :
  have h : k + (l + 1 + n) = (k + 1) + (l + n) := by group
  (curryFinSum (𝕜 := ℝ) (G := C(Icc tmin tmax, E)) (G' := C(Icc tmin tmax, E)) h).symm
  (iteratedFDeriv ℝ k (integralNCMLM
    (fun x ↦ (curryFinSum (𝕜 := ℝ) (G := E) (G' := E) rfl).symm (iteratedFDeriv ℝ (l + 1) g x))
    t₀) α) =
  (curryFinSum (𝕜 := ℝ) (G := C(Icc tmin tmax, E)) (G' := C(Icc tmin tmax, E)) rfl).symm
  (iteratedFDeriv ℝ (k + 1) (integralNCMLM
    (fun x ↦ (curryFinSum (𝕜 := ℝ) (G := E) (G' := E) rfl).symm (iteratedFDeriv ℝ l g x))
    t₀) α) := by
  sorry

/-
This is the step `I^(0) g^(n) = I^(n) g^(0)`

state it generally with `g`?
-/

lemma integralNCMLM_eq {n : ℕ} (f : E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    integralNCMLM (iteratedFDeriv ℝ n f) t₀ = iteratedFDeriv ℝ n (integralCM f t₀) := by sorry















end SmoothFlow
